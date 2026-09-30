// Copyright 2026 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssacompile

import (
	"cmd/compile/internal/abi"
	"cmd/compile/internal/ir"
	"cmd/compile/internal/ssa"
	"cmd/compile/internal/ssa/block"
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
	// runtime.memmove has:
	//
	//   0: dst pointer
	//   1: src pointer
	//   2: size
	//   last: memory
	if len(v.Args) < 4 {
		return false
	}
	dstPtr := v.Args[0]
	srcPtr := v.Args[1]
	sizeArg := v.Args[2]
	copyMem := v.Args[len(v.Args)-1]

	if dstPtr == nil || srcPtr == nil || sizeArg == nil || copyMem == nil {
		return false
	}

	// The destination must be a fresh allocation produced directly by
	// runtime.makeslice with len == cap.
	makeCall := findMakesliceCallFromPtr(dstPtr)
	if makeCall == nil || len(makeCall.Args) < 4 {
		return false
	}
	if makeCall.Args[1] != makeCall.Args[2] {
		return false
	}
	typeArg := makeCall.Args[0]
	dstLen := makeCall.Args[1]

	makeMem := makeCall.Args[len(makeCall.Args)-1]
	if makeMem == nil || !makeMem.Type.IsMemory() {
		return false
	}
	makeResultMem := findCallMemoryResult(makeCall)
	if makeResultMem == nil {
		return false
	}

	// The size copied by memmove is n*sizeof(T) where n = min(len(to),
	// len(from)) is produced by a Phi feeding a shift by log2(sizeof(T)).
	// Recover len(from) from that Phi: runtime.makeslicecopy clamps the
	// copied length internally, so passing len(from) directly lets the min
	// computation die with the memmove call.
	if sizeArg.Op != ssaop.OpLsh64x64 || len(sizeArg.Args) != 2 {
		return false
	}
	shift := sizeArg.Args[1]
	if shift.Op != ssaop.OpConst64 {
		return false
	}
	elemSize := int64(0)
	if srcPtr.Type != nil && srcPtr.Type.IsPtr() {
		elemSize = srcPtr.Type.Elem().Size()
	}
	if elemSize <= 0 || int64(1)<<shift.AuxInt != elemSize {
		return false
	}
	count := sizeArg.Args[0]
	srcLen := (*ssa.Value)(nil)
	switch count.Op {
	case ssaop.OpPhi:
		if len(count.Args) != 2 {
			return false
		}
		seenDstLen := false
		for _, arg := range count.Args {
			if arg == dstLen {
				seenDstLen = true
				continue
			}
			srcLen = arg
		}
		if !seenDstLen || srcLen == nil {
			return false
		}
	case ssaop.OpCondSelect:
		// The frontend can lower min(len(to), len(from)) either as a Phi
		// or as a CondSelect. Handle both forms. CondSelect has:
		//
		//   cond = Less64(srcLen, dstLen)
		//   count = CondSelect(srcLen, dstLen, cond)
		//
		// i.e. count = cond ? srcLen : dstLen.
		if len(count.Args) != 3 {
			return false
		}
		trueVal := count.Args[0]
		falseVal := count.Args[1]
		cond := count.Args[2]
		if cond.Op != ssaop.OpLess64 || len(cond.Args) != 2 {
			return false
		}
		if trueVal == dstLen && falseVal == dstLen {
			return false
		}
		if trueVal != dstLen && falseVal == dstLen {
			if (cond.Args[0] == trueVal && cond.Args[1] == dstLen) ||
				(cond.Args[0] == dstLen && cond.Args[1] == trueVal) {
				srcLen = trueVal
			}
		} else if trueVal == dstLen && falseVal != dstLen {
			// cond ? dstLen : srcLen -- inverted, reject.
			return false
		}
		if srcLen == nil {
			return false
		}
	default:
		return false
	}

	// The memmove call must live in its own block that is entered from a
	// guard block via If to.ptr != from.ptr, and must merge back into a
	// block containing a memory Phi.
	copyBlock := v.Block
	if copyBlock.Kind != block.BlockPlain || len(copyBlock.Succs) != 1 || len(copyBlock.Preds) != 1 {
		return false
	}
	mergeBlock := copyBlock.Succs[0].B
	guardBlock := copyBlock.Preds[0].B
	if guardBlock.Kind != block.BlockIf || len(guardBlock.Succs) != 2 {
		return false
	}
	guard := guardBlock.Controls[0]
	if guard == nil || guard.Op != ssaop.OpNeqPtr || len(guard.Args) != 2 {
		return false
	}
	if !((guard.Args[0] == dstPtr && guard.Args[1] == srcPtr) ||
		(guard.Args[0] == srcPtr && guard.Args[1] == dstPtr)) {
		return false
	}
	hasCopy, hasMerge := false, false
	for _, e := range guardBlock.Succs {
		if e.B == copyBlock {
			hasCopy = true
		}
		if e.B == mergeBlock {
			hasMerge = true
		}
	}
	if !hasCopy || !hasMerge {
		return false
	}

	// Find the memory result of memmove; it must feed only the memory Phi
	// in the merge block.
	var memResult *ssa.Value
	for _, b2 := range f.Blocks {
		for _, u := range b2.Values {
			if u.Op != ssaop.OpSelectN || len(u.Args) != 1 || u.Args[0] != v || !u.Type.IsMemory() {
				continue
			}
			if memResult != nil {
				return false
			}
			memResult = u
		}
	}
	if memResult == nil {
		return false
	}

	var memPhi *ssa.Value
	for _, u := range mergeBlock.Values {
		if u.Op != ssaop.OpPhi {
			continue
		}
		for _, arg := range u.Args {
			if arg == memResult {
				if memPhi != nil {
					return false
				}
				memPhi = u
			}
		}
	}
	if memPhi == nil || len(memPhi.Args) != len(mergeBlock.Preds) {
		return false
	}
	foundCopyMem := false
	for _, arg := range memPhi.Args {
		if arg == copyMem {
			foundCopyMem = true
		}
	}
	if !foundCopyMem {
		return false
	}
	// memmove's memory result must have no uses other than the merge Phi.
	for _, b2 := range f.Blocks {
		for _, u := range b2.Values {
			if u == memPhi {
				continue
			}
			for _, arg := range u.Args {
				if arg == memResult {
					return false
				}
			}
		}
	}

	// Find the destination-header stores between makeslice and memmove.
	headerStores := collectHeaderStores(copyMem, makeResultMem)
	if len(headerStores) == 0 {
		return false
	}

	// dstPtr must be used only by memmove, by the (now dead) guard, and by
	// exactly one of the destination-header stores.
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
					if i != 0 {
						safePtrUses = false
					}
					continue
				}
				if u == guard {
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
		return false
	}

	// Validate the source loads exactly like the typedslicecopy case.
	var sourceLoads []*ssa.Value
	collectSourceLoads(srcPtr, &sourceLoads)
	collectSourceLoads(srcLen, &sourceLoads)
	sourceLoads = uniqueValues(sourceLoads)

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
			if !disjointAddrs(loadAddr, loadSize, store.Args[0], storeTypeSize(store)) {
				safe = false
				break
			}
		}
		if !safe {
			break
		}
		if !memoryDependsOnlyOnStores(load.MemoryArg(), makeResultMem, headerStores) {
			safe = false
			break
		}
	}
	if !safe {
		return false
	}

	// The destination header must not be read outside the guard block, so
	// that relocating the stores into the guard block is unobservable.
	//
	// A read of the destination header is only unsafe when it observes the
	// header through a memory state that predates the header stores: after
	// relocation such a read would be repointed to makeslice's argument
	// memory and observe a stale header. A read whose memory depends on the
	// merge Phi observes the final header and is repointed to the relocated
	// store chain, which writes exactly the same values (the makeslicecopy
	// pointer and the original len/cap), so it is safe.
	dstHeaderBase := valueAddressBase(ptrStore.Args[0])
	relocatable := true
	for _, b2 := range f.Blocks {
		for _, u := range b2.Values {
			if u.Block == guardBlock || containsValue(headerStores, u) || containsValue(sourceLoads, u) {
				continue
			}
			if !readsAddress(u, dstHeaderBase) {
				continue
			}
			if !memoryDependsOn(u.MemoryArg(), memPhi) {
				relocatable = false
			}
		}
	}
	if !relocatable {
		return false
	}

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

	// Emit the makeslicecopy call in the guard block, where both the source
	// loads (defined in the entry block) and the memory merge dominate.
	call := guardBlock.NewValue0A(
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

	newPtr := guardBlock.NewValue1I(
		v.Pos,
		ssaop.OpSelectN,
		types.Types[types.TUNSAFEPTR],
		0,
		call,
	)

	newMem := guardBlock.NewValue1I(
		v.Pos,
		ssaop.OpSelectN,
		types.TypeMem,
		1,
		call,
	)

	// Relocate the destination-header stores into the guard block, chained
	// after the makeslicecopy memory result.
	storeMem := newMem
	lastStore := (*ssa.Value)(nil)
	for i := len(headerStores) - 1; i >= 0; i-- {
		old := headerStores[i]
		val := old.Args[1]
		if old == ptrStore {
			val = newPtr
		}
		ns := guardBlock.NewValue3A(old.Pos, old.Op, types.TypeMem, old.Aux, old.Args[0], val, storeMem)
		storeMem = ns
		if i == 0 {
			lastStore = ns
		}
	}

	// Repoint every consumer of the old header-store memory.
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
					if u.Block == guardBlock && readsAddress(u, dstHeaderBase) {
						u.SetArg(i, lastStore)
					} else {
						u.SetArg(i, makeMem)
					}
				}
			}
		}
	}

	// Source loads no longer need to wait for destination-header
	// initialization; evaluate them against makeslice's argument memory.
	for _, load := range sourceLoads {
		replaceMemoryArg(load, makeMem)
	}

	// Repoint remaining users of makeslice's memory result to makeslice's
	// argument memory.
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

	// The merge Phi is superseded by the relocated store chain.
	for _, b2 := range f.Blocks {
		for _, u := range b2.Values {
			if u == memPhi {
				continue
			}
			for i, arg := range u.Args {
				if arg == memPhi {
					u.SetArg(i, lastStore)
				}
			}
		}
	}

	// Drop the guard: dstPtr is a fresh makeslice allocation, so it can
	// never equal srcPtr and the copy always runs. The min branch is left
	// to deadcode: its Phi dies with the memmove chain and the redundant
	// comparison is harmless.
	succIdx := -1
	for i, e := range guardBlock.Succs {
		if e.B == copyBlock {
			succIdx = i
			break
		}
	}
	if succIdx < 0 {
		return false
	}
	guardBlock.RemoveSucc(succIdx)
	guardBlock.Kind = block.BlockPlain
	guardBlock.ResetControls()
	guardBlock.Likely = ssa.BranchUnknown

	// memmove, makeslice and the original header stores are all superseded
	// by the single makeslicecopy call. Invalidating them also removes,
	// transitively, the min Phi and the memmove size computation. The merge
	// Phi is left valid so that deadcode can update it when it removes the
	// memmove block.
	v.InvalidateRecursively()
	makeCall.InvalidateRecursively()
	for _, hs := range headerStores {
		hs.InvalidateRecursively()
	}

	return true
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

// memoryDependsOn reports whether mem reaches target by following memory
// arguments. Phi values are traversed through all their memory-typed args.
func memoryDependsOn(mem, target *ssa.Value) bool {
	if mem == nil || target == nil {
		return false
	}

	seen := make(map[*ssa.Value]bool)
	var visit func(*ssa.Value) bool
	visit = func(v *ssa.Value) bool {
		if v == nil || seen[v] {
			return false
		}
		seen[v] = true
		if v == target {
			return true
		}
		if v.Op == ssaop.OpPhi {
			for _, a := range v.Args {
				if a != nil && a.Type != nil && a.Type.IsMemory() && visit(a) {
					return true
				}
			}
			return false
		}
		m := v.MemoryArg()
		if m == nil {
			return false
		}
		return visit(m)
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

// disjointAddrs reports whether the memory regions [addr1, addr1+n1) and
// [addr2, addr2+n2) provably do not overlap.
//
// It first tries the shared ssa.Disjoint1 analysis. ssa.Disjoint1 cannot
// reason about addresses whose value is loaded from memory (OpLoad), so when
// it fails disjointAddrs falls back to a structural check: a region on the
// current frame's stack can never be addressed through a pointer loaded from
// memory or received as a function argument. Any pointer stored in memory or
// passed in from the caller refers to the heap or the caller's own frame, not
// to a local of the current frame.
func disjointAddrs(addr1 *ssa.Value, n1 int64, addr2 *ssa.Value, n2 int64) bool {
	if ssa.Disjoint1(addr1, n1, addr2, n2) {
		return true
	}

	base := func(ptr *ssa.Value) *ssa.Value {
		for ptr.Op == ssaop.OpOffPtr {
			ptr = ptr.Args[0]
		}
		if ssaop.OpcodeTable[ptr.Op].NilCheck {
			ptr = ptr.Args[0]
		}
		return ptr
	}

	onCurrentFrame := func(ptr *ssa.Value) bool {
		p := base(ptr)
		if p == nil || len(p.Args) == 0 {
			return false
		}
		return (p.Op == ssaop.OpLocalAddr || p.Op == ssaop.OpAddr) && p.Args[0].Op == ssaop.OpSP
	}

	notOnCurrentFrame := func(ptr *ssa.Value) bool {
		p := base(ptr)
		if p == nil {
			return false
		}
		return p.Op == ssaop.OpLoad || p.Op == ssaop.OpArg || p.Op == ssaop.OpArgIntReg
	}

	return (onCurrentFrame(addr1) && notOnCurrentFrame(addr2)) ||
		(onCurrentFrame(addr2) && notOnCurrentFrame(addr1))
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
