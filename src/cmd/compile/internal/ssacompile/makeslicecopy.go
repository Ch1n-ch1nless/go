// Copyright 2026 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssacompile

import (
	"cmd/compile/internal/ir"
	"cmd/compile/internal/ssa"
	"cmd/compile/internal/ssa/ssaop"
	"cmd/compile/internal/types"
	"fmt"
	"strings"
)

// makeslicecopyElim looks for:
//
//	m := make([]T, len(s))
//	copy(m, s)
//
// after lowering, where the copy is represented by
// runtime.typedslicecopy, and turns the allocation into:
//
//	m := makeslicecopy(et, len(s), len(s), s)
//
// The important part is that this is only valid when evaluating the source
// expression cannot observe the stores which initialize the destination slice
// header.

var debugMakesliceCopyElim = false

func makeslicecopyElim(f *ssa.Func) {
	changed := false
	defer func() {
		debugMakesliceCopyElim = false
	}()

	if strings.Contains(f.Name, "SliceMakeCopyBothComplex") {
		fmt.Println("I'm turned on!")
		debugMakesliceCopyElim = true
	}

	for _, b := range f.Blocks {
		if debugMakesliceCopyElim {
			fmt.Println("===============\n")
			fmt.Println("Current block: ", b.LongString())
		}
		for _, v := range b.Values {
			if debugMakesliceCopyElim {
				fmt.Println("------------------\n")
				fmt.Println("Current value: ", v.LongString())
			}

			if v.Op != ssaop.OpStaticCall {
				continue
			}

			if debugMakesliceCopyElim {
				fmt.Println("Found a static call:", v.Aux)
			}

			ac, ok := v.Aux.(*ssa.AuxCall)
			if !ok || ac == nil || ac.Fn == nil || ac.Fn.Name != "runtime.typedslicecopy" {
				continue
			}

			// typedslicecopy has:
			//
			//   0: type
			//   1: dst pointer
			//   2: dst length
			//   3: src pointer
			//   4: src length
			//   last: memory
			//
			// At this point the high-level slice operations have already
			// been lowered. In particular, do not try to reconstruct
			// SliceMake/SlicePtr here. For the form produced by make([]T,len),
			// dstPtr is the result of runtime.makeslice itself.
			if len(v.Args) < 6 {
				continue
			}

			typeArg := v.Args[0]
			dstPtr := v.Args[1]
			dstLen := v.Args[2]
			srcPtr := v.Args[3]
			srcLen := v.Args[4]
			copyMem := v.Args[len(v.Args)-1]

			if typeArg == nil || dstPtr == nil || dstLen == nil ||
				srcPtr == nil || srcLen == nil || copyMem == nil {
				continue
			}

			if debugMakesliceCopyElim {
				fmt.Println("Typedslicecopy was found")
			}

			// Find the runtime.makeslice call which directly produced dstPtr.
			//
			// Lowered form:
			//
			//   makeCall = runtime.makeslice(type, len, cap, mem)
			//   dstPtr   = SelectN(makeCall, 0)
			//
			// Requiring len == cap == dstLen preserves the original
			// make([]T, len) shape.
			makeCall := findMakesliceCallFromPtr(dstPtr)
			if makeCall == nil || len(makeCall.Args) < 4 {
				continue
			}
			if makeCall.Args[1] != dstLen || makeCall.Args[2] != dstLen {
				continue
			}

			if debugMakesliceCopyElim {
				fmt.Println("Makeslice was found")
			}

			makeMem := makeCall.Args[len(makeCall.Args)-1]
			if makeMem == nil || !makeMem.Type.IsMemory() {
				continue
			}

			if debugMakesliceCopyElim {
				fmt.Println("Makeslice memory was found")
			}

			// The memory result of makeslice is the first memory from which
			// the destination-header stores are chained.
			makeResultMem := findCallMemoryResult(makeCall)
			if makeResultMem == nil {
				continue
			}

			if debugMakesliceCopyElim {
				fmt.Println("Makeslice memory result was found")
			}

			// Find the stores between makeslice and typedslicecopy.
			headerStores := collectHeaderStores(copyMem, makeResultMem)
			if len(headerStores) == 0 {
				continue
			}

			if debugMakesliceCopyElim {
				fmt.Println("Header stores were found")
			}

			// dstPtr must be used only to initialize the destination header
			// and as the destination of this typedslicecopy. Otherwise
			// replacing it with the new allocation could change unrelated
			// uses.
			var ptrStore *ssa.Value
			ptrStoreCount := 0
			safePtrUses := true
			for _, ub := range f.Blocks {
				for _, u := range ub.Values {
					for i, arg := range u.Args {
						if arg != dstPtr {
							continue
						}
						if u == v {
							if i != 1 {
								safePtrUses = false
							}
							continue
						}
						if i == 1 && containsValue(headerStores, u) {
							if u.Args[1] != dstPtr {
								safePtrUses = false
								continue
							}
							ptrStore = u
							ptrStoreCount++
							continue
						}
						safePtrUses = false
					}
				}
			}
			if !safePtrUses || ptrStoreCount != 1 || ptrStore == nil {
				continue
			}

			if debugMakesliceCopyElim {
				fmt.Println("Destination pointer uses are safe")
			}

			// Collect loads needed to evaluate srcPtr and srcLen.
			var sourceLoads []*ssa.Value
			collectSourceLoads(srcPtr, &sourceLoads)
			collectSourceLoads(srcLen, &sourceLoads)
			sourceLoads = uniqueValues(sourceLoads)

			// First validate the entire transformation. Do not mutate SSA
			// until every source load has passed both checks.
			safe := true
			for _, load := range sourceLoads {
				if load == nil || len(load.Args) == 0 || load.MemoryArg() == nil {
					safe = false
					break
				}

				loadAddr := load.Args[0]
				loadSize := load.Type.Size()

				for _, store := range headerStores {
					if len(store.Args) == 0 || store.Args[0] == nil {
						safe = false
						break
					}

					storeAddr := store.Args[0]
					storeSize := storeTypeSize(store)

					if debugMakesliceCopyElim {
						fmt.Printf(
							"CHECK DISJOINT:\n"+
								"  load  = %s\n"+
								"  addr  = %s\n"+
								"  size  = %d\n"+
								"  store = %s\n"+
								"  addr  = %s\n"+
								"  size  = %d\n",
							load.LongString(),
							loadAddr.LongString(),
							loadSize,
							store.LongString(),
							storeAddr.LongString(),
							storeSize,
						)
					}

					disjoint := ssa.Disjoint1(
						loadAddr,
						loadSize,
						storeAddr,
						storeSize,
					)

					if debugMakesliceCopyElim {
						fmt.Println("  => disjoint:", disjoint)
					}

					if !disjoint {
						if debugMakesliceCopyElim {
							fmt.Println("  !!! DISJOINT FAILED !!!")
						}
						safe = false
						break
					}
				}
				if !safe {
					break
				}

				dependsOnlyOnStores := memoryDependsOnlyOnStores(
					load.MemoryArg(),
					makeResultMem,
					headerStores,
				)

				if debugMakesliceCopyElim {
					fmt.Println("MEMORY CHECK:")
					fmt.Println("  load:", load.LongString())
					fmt.Println("  memory:", load.MemoryArg().LongString())
					fmt.Println("  makeResultMem:", makeResultMem.LongString())
					fmt.Println("  dependsOnlyOnStores:", dependsOnlyOnStores)
				}

				if !dependsOnlyOnStores {
					if debugMakesliceCopyElim {
						fmt.Println("  !!! MEMORY DEPENDENCY FAILED !!!")
					}
					safe = false
					break
				}
			}
			if !safe {
				continue
			}

			if debugMakesliceCopyElim {
				fmt.Println("Source loads are safe")
			}

			// typeArg is already the runtime type pointer expected by
			// makeslicecopy, so no high-level destination type recovery is
			// necessary here.

			abiInfo := f.ABIDefault.ABIAnalyzeTypes(
				[]*types.Type{
					types.Types[types.TUNSAFEPTR],
					types.Types[types.TINT],
					types.Types[types.TINT],
					types.Types[types.TUNSAFEPTR],
				},
				[]*types.Type{
					types.Types[types.TUNSAFEPTR],
				},
			)

			call := b.NewValue0A(
				v.Pos,
				ssaop.OpStaticLECall,
				types.NewResults([]*types.Type{
					types.Types[types.TUNSAFEPTR],
					types.TypeMem,
				}),
				ssa.StaticAuxCall(ir.Syms.Makeslicecopy, abiInfo),
			)

			call.AddArg(typeArg)
			call.AddArg(dstLen)
			call.AddArg(srcLen)
			call.AddArg(srcPtr)
			call.AddArg(makeMem)

			newPtr := b.NewValue1I(
				v.Pos,
				ssaop.OpSelectN,
				types.Types[types.TUNSAFEPTR],
				0,
				call,
			)

			newMem := b.NewValue1I(
				v.Pos,
				ssaop.OpSelectN,
				types.TypeMem,
				1,
				call,
			)

			// The pointer produced by makeslice was stored into the
			// destination slice header. Replace that stored pointer with
			// the pointer returned by makeslicecopy.
			ptrStore.SetArg(1, newPtr)

			// The first header store must now depend on makeslicecopy's
			// memory result. collectHeaderStores walks backwards, so the
			// last entry is the earliest store.
			earliestStore := headerStores[len(headerStores)-1]
			replaceMemoryArg(earliestStore, newMem)

			// Source loads no longer need to wait for destination-header
			// initialization. Their memory dependency can start at the
			// original makeslice input memory.
			for _, load := range sourceLoads {
				replaceMemoryArg(load, makeMem)
			}

			// typedslicecopy is now redundant. Its memory result was the
			// final memory in the old header-store chain, so preserve that
			// chain rather than replacing it with newMem directly.
			replaceMemoryResultUses(v, copyMem)

			changed = true
		}
	}

	if changed {
		f.InvalidateCFG()
	}
}

// findMakesliceCallFromPtr finds the runtime.makeslice call which directly
// produced dstPtr in lowered SSA.
//
// The expected lowered form is:
//
//	SelectN(0, runtime.makeslice(...))
//
// High-level SlicePtr/SliceMake operations have already been lowered before
// this pass, so they must not be searched for here.
func findMakesliceCallFromPtr(ptr *ssa.Value) *ssa.Value {
	if ptr == nil || ptr.Op != ssaop.OpSelectN || len(ptr.Args) != 1 || ptr.AuxInt != 0 {
		return nil
	}

	call := ptr.Args[0]
	if call == nil || call.Op != ssaop.OpStaticCall {
		return nil
	}

	ac, ok := call.Aux.(*ssa.AuxCall)
	if !ok || ac == nil || ac.Fn == nil || ac.Fn.Name != "runtime.makeslice" {
		return nil
	}

	return call
}

// findCallMemoryResult finds SelectN(1, call) for a call returning
// (pointer, memory).
func findCallMemoryResult(call *ssa.Value) *ssa.Value {
	if call == nil {
		return nil
	}

	for _, b := range call.Block.Func.Blocks {
		for _, v := range b.Values {
			if v.Op != ssaop.OpSelectN ||
				len(v.Args) != 1 ||
				v.Args[0] != call ||
				v.AuxInt != 1 {
				continue
			}

			if v.Type.IsMemory() {
				return v
			}
		}
	}

	return nil
}

// containsValue reports whether values contains v.
func containsValue(values []*ssa.Value, v *ssa.Value) bool {
	for _, x := range values {
		if x == v {
			return true
		}
	}
	return false
}

// collectHeaderStores walks backwards through the memory chain from endMem
// until startMem.
//
// Only stores are accepted. Any other memory operation makes the pattern
// too complicated for this conservative pass.
func collectHeaderStores(endMem, startMem *ssa.Value) []*ssa.Value {
	var stores []*ssa.Value

	cur := endMem

	for cur != nil && cur != startMem {
		switch cur.Op {
		case ssaop.OpStore, ssaop.OpStoreWB:
			stores = append(stores, cur)

		default:
			return nil
		}

		cur = cur.MemoryArg()
	}

	if cur != startMem {
		return nil
	}

	return stores
}

// collectSourceLoads recursively finds ordinary loads required to compute v.
//
// Memory dependencies are deliberately not traversed as data dependencies.
// The memory chain is handled separately by memoryDependsOnlyOnStores.
func collectSourceLoads(v *ssa.Value, loads *[]*ssa.Value) {
	if v == nil {
		return
	}

	if v.Op == ssaop.OpLoad {
		*loads = append(*loads, v)
		return
	}

	if v.Op == ssaop.OpPhi {
		for _, arg := range v.Args {
			collectSourceLoads(arg, loads)
		}
		return
	}

	for _, arg := range v.Args {
		if arg == nil {
			continue
		}

		if arg.Type != nil && arg.Type.IsMemory() {
			continue
		}

		collectSourceLoads(arg, loads)
	}
}

// memoryDependsOnlyOnStores reports whether mem reaches startMem through
// exactly the destination header stores we already identified.
func memoryDependsOnlyOnStores(
	mem *ssa.Value,
	startMem *ssa.Value,
	headerStores []*ssa.Value,
) bool {
	allowed := make(map[*ssa.Value]bool, len(headerStores))
	for _, store := range headerStores {
		allowed[store] = true
	}

	cur := mem

	for cur != nil && cur != startMem {
		if !allowed[cur] {
			return false
		}
		cur = cur.MemoryArg()
	}

	return cur == startMem
}

// replaceMemoryArg changes the memory argument of v.
func replaceMemoryArg(v, mem *ssa.Value) {
	if v == nil || mem == nil {
		return
	}

	for i, arg := range v.Args {
		if arg != nil && arg.Type != nil && arg.Type.IsMemory() {
			v.SetArg(i, mem)
			return
		}
	}
}

// replaceMemoryResultUses replaces uses of the memory result of a call.
//
// For StaticLECall the actual memory result is normally represented by
// SelectN(call, 1), so replace that SelectN's users rather than trying to
// replace arbitrary arguments of the call itself.
func replaceMemoryResultUses(call, newMem *ssa.Value) {
	if call == nil || newMem == nil {
		return
	}

	var oldMem []*ssa.Value

	for _, b := range call.Block.Func.Blocks {
		for _, v := range b.Values {
			if v.Op == ssaop.OpSelectN &&
				len(v.Args) == 1 &&
				v.Args[0] == call &&
				v.AuxInt == 1 &&
				v.Type.IsMemory() {
				oldMem = append(oldMem, v)
			}
		}
	}

	for _, mem := range oldMem {
		for _, b := range call.Block.Func.Blocks {
			for _, v := range b.Values {
				for i, arg := range v.Args {
					if arg == mem {
						v.SetArg(i, newMem)
					}
				}
			}
		}
	}
}

// uniqueValues removes duplicate SSA values while preserving order.
func uniqueValues(values []*ssa.Value) []*ssa.Value {
	if len(values) < 2 {
		return values
	}

	seen := make(map[*ssa.Value]bool, len(values))
	result := make([]*ssa.Value, 0, len(values))

	for _, v := range values {
		if v == nil || seen[v] {
			continue
		}

		seen[v] = true
		result = append(result, v)
	}

	return result
}

// storeTypeSize returns the size written by a Store/StoreWB.
func storeTypeSize(store *ssa.Value) int64 {
	if store == nil || len(store.Args) < 2 || store.Args[1] == nil {
		return 0
	}

	return store.Args[1].Type.Size()
}
