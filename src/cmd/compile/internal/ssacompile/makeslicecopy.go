package ssacompile

import (
	"cmd/compile/internal/ir"
	"cmd/compile/internal/reflectdata"
	"cmd/compile/internal/ssa"
	"cmd/compile/internal/ssa/ssaop"
	"cmd/compile/internal/types"
)

// makeslicecopyElim looks for the SSA form produced by:
//
//	m := make([]T, len(s))
//	copy(m, s)
//
// and replaces the allocation's backing pointer with a direct
// call to runtime.makeslicecopy.
//
// This pass deliberately stays conservative. If the expected SSA shape,
// types, or memory uses are not present, it leaves the original code alone.
func makeslicecopyElim(f *ssa.Func) {
	changed := false

	for _, b := range f.Blocks {
		for i := len(b.Values) - 1; i >= 0; i-- {
			v := b.Values[i]
			if v.Op != ssaop.OpMove || len(v.Args) != 3 {
				continue
			}

			dst := v.Args[0]
			src := v.Args[1]
			mem := v.Args[2]

			moveSize := v.AuxInt
			if moveSize <= 0 {
				continue
			}

			elemType, ok := v.Aux.(*types.Type)
			if !ok || elemType == nil {
				continue
			}

			// OpMove requires non-overlapping source and destination.
			if !ssa.Disjoint1(dst, moveSize, src, moveSize) {
				continue
			}
			if ssa.IsSamePtr(dst, src) {
				continue
			}

			if v.Uses > 1 {
				continue
			}

			sliceMake := findSliceMake(dst)
			if sliceMake == nil || len(sliceMake.Args) < 3 {
				continue
			}

			slicePtr := sliceMake.Args[0]
			if slicePtr == nil || slicePtr.Op != ssaop.OpSlicePtr {
				continue
			}
			if slicePtr.Uses > 1 {
				continue
			}

			typeLinksym := reflectdata.TypeLinksym(elemType)
			_, sb := f.SpSb()

			// Address of the runtime type descriptor.
			typePtr := b.NewValue1A(
				v.Pos,
				ssaop.OpAddr,
				f.Config.Types.BytePtr,
				typeLinksym,
				sb,
			)

			sliceLen := sliceMake.Args[1]
			if sliceLen == nil {
				continue
			}

			callArgs := []*ssa.Value{
				typePtr,
				sliceLen,
				sliceLen,
				src,
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

			call := b.NewValue0A(
				v.Pos,
				ssaop.OpStaticCall,
				types.Types[types.TUNSAFEPTR],
				ssa.StaticAuxCall(ir.Syms.Makeslicecopy, abiInfo),
			)
			for _, arg := range callArgs {
				call.AddArg(arg)
			}

			// makeslicecopy returns the newly allocated backing pointer.
			sliceMake.SetArg(0, call)

			// The old Move is no longer needed. Replace its memory users with
			// the memory value that preceded the Move.
			for _, useBlock := range f.Blocks {
				for _, use := range useBlock.Values {
					if use.MemoryArg() == v {
						n := len(use.Args)
						if n != 0 {
							use.Args[n-1] = mem
						}
					}
				}
			}

			changed = true
		}
	}

	if changed {
		f.InvalidateCFG()
	}
}

// findSliceMake follows the pointer expression used as the destination of
// OpMove and returns the corresponding OpSliceMake.
func findSliceMake(v *ssa.Value) *ssa.Value {
	for v != nil && v.Op == ssaop.OpOffPtr {
		v = v.Args[0]
	}

	if v == nil || v.Op != ssaop.OpSlicePtr || len(v.Args) != 1 {
		return nil
	}

	slice := v.Args[0]
	if slice == nil || slice.Op != ssaop.OpSliceMake {
		return nil
	}

	return slice
}
