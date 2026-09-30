// Copyright 2026 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssacompile

import (
	"cmd/compile/internal/abi"
	"cmd/compile/internal/ir"
	"cmd/compile/internal/ssa"
	"cmd/compile/internal/ssa/ssaop"
	"cmd/compile/internal/types"
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

func makeslicecopyElim(f *ssa.Func) {
	changed := false

	for _, b := range f.Blocks {
		for _, v := range b.Values {
			if v.Op != ssaop.OpStaticCall {
				continue
			}

			ac, ok := v.Aux.(*ssa.AuxCall)
			if !ok || ac == nil || ac.Fn == nil {
				continue
			}
			if ac.Fn.Name == "runtime.memmove" {
				if elimMemmoveCopy(f, b, v) {
					changed = true
					// elimMemmoveCopy changes the CFG. Dominance information
					// must be recomputed before the next candidate is checked.
					f.InvalidateCFG()
				}
				continue
			}
			if ac.Fn.Name != "runtime.typedslicecopy" {
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

			// typedslicecopy returns (n int, mem), and the copy count is
			// observed through SelectN(v, 0) whenever the result of copy()
			// is used. runtime.makeslicecopy returns only the new slice
			// pointer and cannot report the number of copied elements, so
			// such a use makes the call uneliminable: invalidating
			// typedslicecopy would leave a dangling SelectN that crashes
			// lower with "value still has N uses".
			intResultUsed := false
			for _, b2 := range f.Blocks {
				for _, u := range b2.Values {
					for _, arg := range u.Args {
						if arg == v && (u.Op != ssaop.OpSelectN || u.AuxInt != 1) {
							intResultUsed = true
							break
						}
					}
					if intResultUsed {
						break
					}
				}
				if intResultUsed {
					break
				}
			}
			if intResultUsed {
				continue
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

			makeMem := makeCall.Args[len(makeCall.Args)-1]
			if makeMem == nil || !makeMem.Type.IsMemory() {
				continue
			}

			// The memory result of makeslice is the first memory from which
			// the destination-header stores are chained.
			makeResultMem := findCallMemoryResult(makeCall)
			if makeResultMem == nil {
				continue
			}

			// Find the stores between makeslice and typedslicecopy.
			headerStores := collectHeaderStores(copyMem, makeResultMem)
			if len(headerStores) == 0 {
				continue
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

					disjoint := disjointAddrs(
						loadAddr,
						loadSize,
						storeAddr,
						storeSize,
					)

					if !disjoint {
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

				if !dependsOnlyOnStores {
					safe = false
					break
				}
			}
			if !safe {
				continue
			}

			// The new call and the relocated header stores are created in b.
			// Every operand that they capture must therefore dominate b.
			if !valuesDominateBlock(f, b, typeArg, dstLen, srcLen, srcPtr, makeMem) {
				continue
			}
			operandsDominate := true
			for _, load := range sourceLoads {
				if load == nil || load.MemoryArg() == nil ||
					!valueDominatesBlock(f, load.MemoryArg(), load.Block) {
					operandsDominate = false
					break
				}
			}
			for _, store := range headerStores {
				if len(store.Args) < 2 ||
					!valuesDominateBlock(f, b, store.Args[0], store.Args[1]) {
					operandsDominate = false
					break
				}
			}
			if !operandsDominate {
				continue
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

			// The header stores may live in a different block than
			// typedslicecopy: a bounds check can sit between them. The new
			// makeslicecopy call must be created in the block of
			// typedslicecopy, because it consumes the source loads placed
			// there, so the header stores have to be relocated into that
			// block to consume the makeslicecopy memory result and store
			// the makeslicecopy pointer into the destination header.
			//
			// Relocation is only valid if nothing outside the destination
			// block reads the destination header: such a read would observe
			// the stores earlier than the original code does.
			dstHeaderBase := valueAddressBase(ptrStore.Args[0])
			relocatable := true
			for _, b2 := range f.Blocks {
				for _, u := range b2.Values {
					if u.Block == b || containsValue(headerStores, u) || containsValue(sourceLoads, u) {
						continue
					}
					if readsAddress(u, dstHeaderBase) {
						relocatable = false
					}
				}
			}
			if !relocatable {
				continue
			}

			// expandCalls has already run by the time this pass executes,
			// so a freshly created StaticLECall would never be expanded and
			// would fail the post-lowering consistency check. Emit the call
			// directly in its post-expansion form instead: OpStaticCall with
			// register-only results followed by memory.
			call := b.NewValue0A(
				v.Pos,
				ssaop.OpStaticCall,
				types.NewResults(append(abi.RegisterTypes(abiInfo.OutParams()), types.TypeMem)),
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

			// Create relocated copies of the header stores in block b,
			// chained after the makeslicecopy memory result.
			// collectHeaderStores walks from the newest store to the
			// oldest, so walk in reverse to rebuild the chain in the
			// original order.
			storeMem := newMem
			lastStore := (*ssa.Value)(nil)
			for i := len(headerStores) - 1; i >= 0; i-- {
				old := headerStores[i]
				val := old.Args[1]
				if old == ptrStore {
					// The makeslice pointer is superseded by the pointer
					// returned by makeslicecopy.
					val = newPtr
				}
				ns := b.NewValue3A(old.Pos, old.Op, types.TypeMem, old.Aux, old.Args[0], val, storeMem)
				storeMem = ns
				if i == 0 {
					lastStore = ns
				}
			}

			// Repoint every consumer of the old header-store memory. A value
			// that reads the destination header after the stores (and sits in
			// the destination block) must observe the relocated store chain,
			// i.e. lastStore. Everything else sees the memory state before the
			// destination header was written, which is makeslice's argument
			// memory: source loads have been repointed to it, and source
			// address computations must match so that no dependency cycle is
			// introduced between the source loads feeding the new call and the
			// relocated stores producing lastStore.
			for _, b2 := range f.Blocks {
				for _, u := range b2.Values {
					if containsValue(headerStores, u) || containsValue(sourceLoads, u) {
						continue
					}
					for i, arg := range u.Args {
						if arg == nil || !arg.Type.IsMemory() {
							continue
						}
						if containsValue(headerStores, arg) {
							if u.Block == b && readsAddress(u, dstHeaderBase) {
								u.SetArg(i, lastStore)
							} else {
								u.SetArg(i, makeMem)
							}
						}
					}
				}
			}

			// Source loads no longer need to wait for destination-header
			// initialization, and the intermediate allocation performed by
			// makeslice is gone entirely: the source expression is evaluated
			// against makeslice's argument memory, before any part of the
			// destination is written.
			for _, load := range sourceLoads {
				replaceMemoryArg(load, makeMem)
			}

			// Repoint remaining users of the makeslice memory result to
			// makeslice's argument memory. The intermediate allocation is
			// gone, so SelectN(makeCall, 1) no longer has a meaning: values
			// that were ordered after the makeslice call (for example the
			// LocalAddr used to address the destination header) must instead
			// observe the memory state that existed before makeslice ran.
			for _, b2 := range f.Blocks {
				for _, u := range b2.Values {
					if containsValue(headerStores, u) || containsValue(sourceLoads, u) {
						continue
					}
					for i, arg := range u.Args {
						if arg == makeResultMem {
							u.SetArg(i, makeMem)
						}
					}
				}
			}

			// typedslicecopy is now redundant. Its memory result is
			// superseded by the relocated header-store chain.
			replaceMemoryResultUses(v, lastStore)

			// The original runtime.typedslicecopy and runtime.makeslice
			// calls are both superseded by the single makeslicecopy call.
			// Invalidating them also removes, transitively, the old header
			// stores and the makeslice result selectors. deadcode at the
			// end of this pass drops the invalidated values from the
			// blocks, so that lower never sees them.
			v.InvalidateRecursively()
			makeCall.InvalidateRecursively()
			for _, hs := range headerStores {
				hs.InvalidateRecursively()
			}

			changed = true
		}
	}

	if changed {
		deadcode(f)
		f.InvalidateCFG()
	}
}

// elimMemmoveCopy eliminates the make+copy pattern when the copy is lowered
// to runtime.memmove rather than runtime.typedslicecopy:
//
//	m := make([]T, len(s))
//	copy(m, s)
//
// The frontend lowers such a copy to:
//
//	n = min(len(to), len(from))
//	if to.ptr != from.ptr {
//	    memmove(to.ptr, from.ptr, n*sizeof(T))
//	}
//
// Because to.ptr is a fresh allocation produced directly by runtime.makeslice,
// it can never equal from.ptr, so the guard is always true and can be dropped.
// The whole pattern is then replaced by a single runtime.makeslicecopy call,
// mirroring the typedslicecopy case.
func elimMemmoveCopy(f *ssa.Func, b *ssa.Block, v *ssa.Value) bool {
	// Deliberately disabled for now. This transformation rewrites the CFG,
	// removes a pointer-equality guard, relocates stores, and rewrites a memory
	// Phi. Keep it disabled until all-path memory and destination-observation
	// proofs cover the complete CFG pattern. Missing an optimization is safer
	// than miscompiling a program.
	return false
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
		// The address of a load can itself depend on pointer loads. Those
		// loads must be checked too: moving destination-header stores must
		// not change a pointer used to form a source address.
		if len(v.Args) > 0 {
			collectSourceLoads(v.Args[0], loads)
		}
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

// memoryDependsOn reports whether mem reaches target by following memory
// arguments. Phi values are traversed through all their memory-typed args.
func memoryDependsOn(mem, target *ssa.Value) bool {
	if mem == nil || target == nil {
		return false
	}

	// This is a proof used before moving destination-header stores. Every
	// incoming memory path must reach target. A Phi with one matching input
	// and one unrelated input is not sufficient.
	active := make(map[*ssa.Value]bool)
	checked := make(map[*ssa.Value]bool)
	var visit func(*ssa.Value) bool
	visit = func(v *ssa.Value) bool {
		if v == nil {
			return false
		}
		if v == target {
			return true
		}
		if checked[v] {
			return true
		}
		// A cycle that does not reach target on the current path is not a
		// proof. In particular, don't let a loop Phi prove itself.
		if active[v] {
			return false
		}
		active[v] = true
		defer delete(active, v)

		if v.Op == ssaop.OpPhi {
			foundMemoryArg := false
			for _, a := range v.Args {
				if a == nil || a.Type == nil || !a.Type.IsMemory() {
					continue
				}
				foundMemoryArg = true
				if !visit(a) {
					return false
				}
			}
			if !foundMemoryArg {
				return false
			}
			checked[v] = true
			return true
		}

		m := v.MemoryArg()
		if m == nil || !visit(m) {
			return false
		}
		checked[v] = true
		return true
	}
	return visit(mem)
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
// The memory result of a call is represented by SelectN(call, 1), so replace
// that SelectN's users rather than trying to replace arbitrary arguments of
// the call itself.
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

// valueDominatesBlock reports whether v is available on every path to b.
// A value defined in b itself is considered dominating because this pass only
// inserts new values at the end of b.
func valueDominatesBlock(f *ssa.Func, v *ssa.Value, b *ssa.Block) bool {
	if f == nil || v == nil || v.Block == nil || b == nil {
		return false
	}
	if v.Block == b {
		return true
	}

	idom := f.Idom()
	for cur := b; cur != nil; {
		cur = idom[cur.ID]
		if cur == v.Block {
			return true
		}
	}
	return false
}

// valuesDominateBlock reports whether every value is available at b.
func valuesDominateBlock(f *ssa.Func, b *ssa.Block, values ...*ssa.Value) bool {
	for _, v := range values {
		if !valueDominatesBlock(f, v, b) {
			return false
		}
	}
	return true
}

// disjointAddrs reports whether the memory regions [addr1, addr1+n1) and
// [addr2, addr2+n2) provably do not overlap.
//
// Disjoint1 understands only a limited set of address forms. In particular,
// it cannot prove disjointness when one address is derived from a pointer
// loaded through an argument. We may extend that proof when the other address
// is rooted in a fresh runtime.makeslice allocation: an object allocated by
// this call cannot alias an object reachable from an incoming argument.
//
// The fallback is deliberately narrow. A load from a local stack slot is not
// treated as input-derived, because that slot could contain a pointer to the
// fresh allocation. Every load in an address expression must instead be
// rooted in an incoming argument or a global address, and those load slots
// must be disjoint from the fresh allocation being initialized.
func disjointAddrs(addr1 *ssa.Value, n1 int64, addr2 *ssa.Value, n2 int64) bool {
	if addr1 == nil || addr2 == nil || n1 < 0 || n2 < 0 {
		return false
	}
	if ssa.Disjoint1(addr1, n1, addr2, n2) {
		return true
	}

	// Disjoint1 intentionally understands only a small set of address forms.
	// A pointer loaded from memory reachable through an incoming argument can
	// still be proven disjoint from a LocalAddr in the current stack frame.
	//
	// This fallback is deliberately asymmetric in its proof: one side must be
	// a local stack address, and the other side must be derived from an
	// incoming argument. Every load in the pointer derivation must itself read
	// from argument-derived memory. Thus a store to the local stack object
	// cannot change the loaded pointer chain.
	if isLocalStackAddress(addr1) && addressLoadsStableAgainstLocalStack(addr2) {
		return true
	}
	if isLocalStackAddress(addr2) && addressLoadsStableAgainstLocalStack(addr1) {
		return true
	}
	return false
}

// isLocalStackAddress reports whether ptr is a LocalAddr rooted at SP.
// Address arithmetic and nil checks are peeled first.
func isLocalStackAddress(ptr *ssa.Value) bool {
	base := addressBaseForDisjoint(ptr)
	if base == nil || base.Op != ssaop.OpLocalAddr || len(base.Args) == 0 {
		return false
	}
	return base.Args[0].Op == ssaop.OpSP
}

// addressLoadsStableAgainstLocalStack reports whether ptr is derived from an
// incoming argument and every load used to form that pointer reads from
// argument-derived memory. Such load slots cannot overlap a LocalAddr in the
// current frame in ordinary safe Go code, so stores to that local object do
// not invalidate the pointer derivation.
//
// Unknown operations and cycles fail closed. This proof is intentionally
// narrower than general alias analysis; it does not treat arbitrary loaded
// pointers or global memory as disjoint from stack locals.
func addressLoadsStableAgainstLocalStack(ptr *ssa.Value) bool {
	if !addressDerivedFromInput(ptr) {
		return false
	}

	seen := make(map[*ssa.Value]bool)
	var visit func(*ssa.Value) bool
	visit = func(v *ssa.Value) bool {
		if v == nil || seen[v] {
			return v != nil
		}
		seen[v] = true

		switch v.Op {
		case ssaop.OpLoad:
			if len(v.Args) < 2 || v.Args[0] == nil {
				return false
			}
			// The loaded pointer's storage must be input-derived as well.
			if !addressDerivedFromInput(v.Args[0]) {
				return false
			}
			return visit(v.Args[0])
		case ssaop.OpOffPtr, ssaop.OpPtrIndex:
			if len(v.Args) == 0 {
				return false
			}
			return visit(v.Args[0])
		case ssaop.OpPhi:
			if len(v.Args) == 0 {
				return false
			}
			for _, arg := range v.Args {
				if !visit(arg) {
					return false
				}
			}
			return true
		default:
			if ssaop.OpcodeTable[v.Op].NilCheck && len(v.Args) > 0 {
				return visit(v.Args[0])
			}
			// The provenance checker already validates the terminal value.
			return addressDerivedFromInput(v)
		}
	}
	return visit(ptr)
}

// addressBaseForDisjoint peels address arithmetic and nil checks. It is kept
// separate from valueAddressBase because it also handles pointer indexing.
func addressBaseForDisjoint(ptr *ssa.Value) *ssa.Value {
	for ptr != nil {
		switch ptr.Op {
		case ssaop.OpOffPtr, ssaop.OpPtrIndex:
			if len(ptr.Args) == 0 {
				return ptr
			}
			ptr = ptr.Args[0]
		default:
			if ssaop.OpcodeTable[ptr.Op].NilCheck && len(ptr.Args) > 0 {
				ptr = ptr.Args[0]
				continue
			}
			return ptr
		}
	}
	return nil
}

// addressDerivedFromInput proves that a pointer expression ultimately comes
// from an incoming argument or a global address. Loads are accepted only when
// the address of the loaded pointer itself has that provenance. Local stack
// slots and unknown operations fail closed.
func addressDerivedFromInput(ptr *ssa.Value) bool {
	active := make(map[*ssa.Value]bool)
	var visit func(*ssa.Value) bool
	visit = func(v *ssa.Value) bool {
		if v == nil || active[v] {
			return false
		}
		active[v] = true
		defer delete(active, v)

		switch v.Op {
		case ssaop.OpArg, ssaop.OpArgIntReg, ssaop.OpAddr:
			return true
		case ssaop.OpOffPtr, ssaop.OpPtrIndex, ssaop.OpLoad:
			if len(v.Args) == 0 {
				return false
			}
			return visit(v.Args[0])
		case ssaop.OpPhi:
			if len(v.Args) == 0 {
				return false
			}
			for _, arg := range v.Args {
				if !visit(arg) {
					return false
				}
			}
			return true
		default:
			if ssaop.OpcodeTable[v.Op].NilCheck && len(v.Args) > 0 {
				return visit(v.Args[0])
			}
			return false
		}
	}
	return visit(ptr)
}

// valueAddressBase returns the base pointer of an address value after
// peeling offsets and nil checks.
func valueAddressBase(ptr *ssa.Value) *ssa.Value {
	if ptr == nil {
		return nil
	}
	for ptr.Op == ssaop.OpOffPtr {
		ptr = ptr.Args[0]
	}
	if ssaop.OpcodeTable[ptr.Op].NilCheck {
		ptr = ptr.Args[0]
	}
	return ptr
}

// readsAddress reports whether v reads memory at an address based on base.
func readsAddress(v *ssa.Value, base *ssa.Value) bool {
	if v == nil || base == nil || v.Op != ssaop.OpLoad || len(v.Args) == 0 || v.Args[0] == nil {
		return false
	}
	return valueAddressBase(v.Args[0]) == base
}
