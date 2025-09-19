// Copyright 2025 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import (
	"cmd/compile/internal/types"
	"os"
)

// mergeConditionalBranches optimizes nested conditional branches on ARM64.
// The algorithm detects patterns where two consecutive conditional branches
// form logical AND/OR operations and transforms them into conditional
// comparison instructions (CCMP/CCMN).
//
// OR pattern (index 1) and AND pattern (index 0):
//
// if1                                if1
// | \                                / |
// |  \                              /  |
// |   if2            OR          if2   |
// |  /   \                      /   \  |
// | /     \                    /     \ |
// |/       \                  /       \|
// either   both	          both     either
// true     false             true     false
//
// This transformation reduces branch mispredictions and improves performance
// by leveraging ARM64's conditional execution capabilities.
func mergeConditionalBranches(f *Func) {
	if f.Config.arch != "arm64" {
		return
	}

	if name := os.Getenv("CCMP_GEN"); name != "YES" {
		return
	}

	blocks := f.postorder()

	for _, block := range blocks {
		if detectNestedIfBlock(block, 0) {
			transformNestedIfBlock(block, 0)
		} else if detectNestedIfBlock(block, 1) {
			transformNestedIfBlock(block, 1)
		}
	}
}

// ...
func skipEmptyPlainBlocks(block *Block) *Block {
	for isEmptyPlainBlock(block) {
		block = block.Succs[0].Block()
	}
	return block
}

// ...
func isEmptyPlainBlock(block *Block) bool {
	if block.Kind == BlockPlain && len(block.Values) == 0 &&
		len(block.Preds) == 1 && len(block.Succs) == 1 {
		return true
	}
	return false
}

// ...
func deleteEmptyPlainBlocks(block *Block) *Block {
	for isEmptyPlainBlock(block) {
		nextBlock := block.Succs[0].Block()
		deleteEmptyPlainBlock(block)
		block = nextBlock
	}
	return block
}

// ...
func deleteEmptyPlainBlock(block *Block) {
	prevEdge := block.Preds[0]
	nextEdge := block.Succs[0]

	prevEdge.b.Succs[prevEdge.i] = nextEdge
	nextEdge.b.Preds[nextEdge.i] = prevEdge

	invalidateEmptyPlainBlock(block)
}

// ...
func invalidateEmptyPlainBlock(block *Block) {
	block.removePred(0)
	block.removeSucc(0)
	block.Reset(BlockInvalid)
}

func detectNestedIfBlock(b *Block, index int) bool {
	if !isIfBlock(b) {
		return false
	}

	nestedBlock := skipEmptyPlainBlocks(b.Succs[index].Block())
	resultBlock1 := skipEmptyPlainBlocks(b.Succs[index^1].Block())
	if nestedBlock == b || nestedBlock == resultBlock1 {
		return false
	}

	if len(nestedBlock.Preds) != 1 ||
		len(nestedBlock.Succs) != 2 ||
		!isIfBlock(nestedBlock) ||
		!canValuesBeMoved(nestedBlock) {
		return false
	}

	resultBlock2 := skipEmptyPlainBlocks(nestedBlock.Succs[index^1].Block())
	if resultBlock1 != resultBlock2 {
		// Both false branches must go to same target
		return false
	}

	// Здесь надо придумать проверку фи-нод в resultBlock.
	// Так как не факт, что ssa value из этих блоков

	// Так же стоит проверить, и nestedBlock.Succs[index].Block()
	// Там удалять пустые блоки может быть плохой идеей

	return true
}

func canValuesBeMoved(b *Block) bool {
	for _, v := range b.Values {
		if !canValueBeMoved(v) {
			return false
		}
	}
	return true
}

func canValueBeMoved(v *Value) bool {
	if v.Op == OpPhi {
		return false
	} else if v.Type.IsMemory() {
		return false
	} else if v.Op.HasSideEffects() {
		return false
	} else if opcodeTable[v.Op].nilCheck {
		return false
	} else if v.MemoryArg() != nil {
		return false
	}
	return true
}

func hasPhi(b *Block) bool {
	for _, v := range b.Values {
		if v.Op == OpPhi {
			return true
		}
	}
	return false
}

func isIfBlock(b *Block) bool {
	switch b.Kind {
	case BlockARM64EQ,
		BlockARM64NE,
		BlockARM64LT,
		BlockARM64LE,
		BlockARM64GT,
		BlockARM64GE,
		BlockARM64ULT,
		BlockARM64ULE,
		BlockARM64UGT,
		BlockARM64UGE:
		return isComparisonOperation(b.Controls[0])
	case BlockARM64Z,
		BlockARM64NZ,
		BlockARM64ZW,
		BlockARM64NZW:
		return true
	default:
		return false
	}
}

func isComparisonOperation(value *Value) bool {
	if value.Uses != 1 {
		return false
	}

	switch value.Op {
	case OpARM64CMP,
		OpARM64CMPconst,
		OpARM64CMN,
		OpARM64CMNconst,
		OpARM64CMPW,
		OpARM64CMPWconst,
		OpARM64CMNW,
		OpARM64CMNWconst:
		return true
	default:
		return false
	}
}

func transformNestedIfBlock(b *Block, index int) {
	clearPatternFromEmptyPlainBlocks(b, index)
	nestedBlock := b.Succs[index].Block()

	transformPrimaryComparisonValue(b)
	transformDependentComparisonValue(nestedBlock)
	transformToConditionalComparisonValue(b, index)
	fixComparisonWithConstant(nestedBlock, index)
	setNewControlValue(b, index)
	moveAllValues(b, nestedBlock)
	elimNestedBlock(nestedBlock, index)
}

func clearPatternFromEmptyPlainBlocks(b *Block, index int) {
	nestedBlock := deleteEmptyPlainBlocks(b.Succs[index].Block())
	deleteEmptyPlainBlocks(b.Succs[index^1].Block())
	deleteEmptyPlainBlocks(nestedBlock.Succs[index^1].Block())
}

func moveAllValues(dest, src *Block) {
	for _, value := range src.Values {
		value.Block = dest
		dest.Values = append(dest.Values, value)
	}
	src.truncateValues(0)
}

func elimNestedBlock(b *Block, index int) {
	prevEdge := b.Preds[0]
	nextEdge := b.Succs[index]
	removedEdge := b.Succs[index^1]

	prevEdge.b.Succs[prevEdge.i] = nextEdge
	nextEdge.b.Preds[nextEdge.i] = prevEdge

	falseResultBlock := removedEdge.Block()
	i := removedEdge.Index()

	falseResultBlock.removePred(i)
	for _, v := range falseResultBlock.Values {
		if v.Op != OpPhi {
			continue
		}
		falseResultBlock.removePhiArg(v, i)
	}

	b.removePred(0)
	b.removeSucc(1)
	b.removeSucc(0)
	b.Reset(BlockInvalid)
}

func setNewControlValue(block *Block, index int) {
	nestedBlock := block.Succs[index].Block()
	block.resetWithControl(nestedBlock.Kind, nestedBlock.Controls[0])
	if index == 0 && block.Likely == BranchLikely && nestedBlock.Likely == BranchLikely {
		block.Likely = BranchLikely
	} else if index == 1 && block.Likely == BranchUnlikely && nestedBlock.Likely == BranchUnlikely {
		block.Likely = BranchUnlikely
	} else {
		block.Likely = BranchUnknown
	}
	nestedBlock.Likely = BranchUnknown
}

func transformPrimaryComparisonValue(block *Block) {
	switch block.Kind {
	case BlockARM64Z:
		arg0 := block.Controls[0]
		controlValue := block.NewValue1I(arg0.Pos, OpARM64CMPconst, types.TypeFlags, 0, arg0)
		block.resetWithControl(BlockARM64EQ, controlValue)
	case BlockARM64NZ:
		arg0 := block.Controls[0]
		controlValue := block.NewValue1I(arg0.Pos, OpARM64CMPconst, types.TypeFlags, 0, arg0)
		block.resetWithControl(BlockARM64NE, controlValue)
	case BlockARM64ZW:
		arg0 := block.Controls[0]
		controlValue := block.NewValue1I(arg0.Pos, OpARM64CMPWconst, types.TypeFlags, 0, arg0)
		block.resetWithControl(BlockARM64EQ, controlValue)
	case BlockARM64NZW:
		arg0 := block.Controls[0]
		controlValue := block.NewValue1I(arg0.Pos, OpARM64CMPWconst, types.TypeFlags, 0, arg0)
		block.resetWithControl(BlockARM64NE, controlValue)
	}
}

func transformDependentComparisonValue(block *Block) {
	typ := &block.Func.Config.Types

	switch block.Kind {
	case BlockARM64EQ,
		BlockARM64NE,
		BlockARM64LT,
		BlockARM64LE,
		BlockARM64GT,
		BlockARM64GE,
		BlockARM64ULT,
		BlockARM64ULE,
		BlockARM64UGT,
		BlockARM64UGE:
		value := block.Controls[0]
		arg0 := value.Args[0]

		switch value.Op {
		case OpARM64CMPconst:
			auxConstant := auxIntToInt64(value.AuxInt)
			value.reset(OpARM64CMP)
			constantValue := block.Func.constVal(OpARM64MOVDconst, typ.UInt64, auxConstant, true)
			value.AddArg2(arg0, constantValue)
		case OpARM64CMNconst:
			auxConstant := auxIntToInt64(value.AuxInt)
			value.reset(OpARM64CMN)
			constantValue := block.Func.constVal(OpARM64MOVDconst, typ.UInt64, auxConstant, true)
			value.AddArg2(arg0, constantValue)
		case OpARM64CMPWconst:
			auxConstant := auxIntToInt32(value.AuxInt)
			value.reset(OpARM64CMPW)
			constantValue := block.Func.constVal(OpARM64MOVDconst, typ.UInt64, int64(auxConstant), true)
			value.AddArg2(arg0, constantValue)
		case OpARM64CMNWconst:
			auxConstant := auxIntToInt32(value.AuxInt)
			value.reset(OpARM64CMNW)
			constantValue := block.Func.constVal(OpARM64MOVDconst, typ.UInt64, int64(auxConstant), true)
			value.AddArg2(arg0, constantValue)
		}
	case BlockARM64Z:
		arg0 := block.Controls[0]
		arg1 := block.Func.constVal(OpARM64MOVDconst, typ.UInt64, 0, true)
		comparisonValue := block.NewValue2(arg0.Pos, OpARM64CMP, types.TypeFlags, arg0, arg1)
		block.resetWithControl(BlockARM64EQ, comparisonValue)
	case BlockARM64NZ:
		arg0 := block.Controls[0]
		arg1 := block.Func.constVal(OpARM64MOVDconst, typ.UInt64, 0, true)
		comparisonValue := block.NewValue2(arg0.Pos, OpARM64CMP, types.TypeFlags, arg0, arg1)
		block.resetWithControl(BlockARM64NE, comparisonValue)
	case BlockARM64ZW:
		arg0 := block.Controls[0]
		arg1 := block.Func.constVal(OpARM64MOVDconst, typ.UInt64, 0, true)
		comparisonValue := block.NewValue2(arg0.Pos, OpARM64CMPW, types.TypeFlags, arg0, arg1)
		block.resetWithControl(BlockARM64EQ, comparisonValue)
	case BlockARM64NZW:
		arg0 := block.Controls[0]
		arg1 := block.Func.constVal(OpARM64MOVDconst, typ.UInt64, 0, true)
		comparisonValue := block.NewValue2(arg0.Pos, OpARM64CMPW, types.TypeFlags, arg0, arg1)
		block.resetWithControl(BlockARM64NE, comparisonValue)
	default:
		panic("Wrong block kind")
	}
}

func fixComparisonWithConstant(block *Block, index int) {
	controlValue := block.Controls[0]
	switch controlValue.Op {
	case OpARM64CCMP:
		params := controlValue.AuxArm64ConditionalParams()
		arg0 := controlValue.Args[0]
		arg1 := controlValue.Args[1]
		arg2 := controlValue.Args[2]
		if arg1.Op == OpARM64MOVDconst {
			imm := auxIntToInt64(arg1.AuxInt)
			if imm&^0x1f == 0 {
				controlValue.reset(OpARM64CCMPconst)
				params.constValue = uint8(imm)
				params.ind = true
				controlValue.AuxInt = arm64ConditionalParamsToAuxInt(params)
				controlValue.AddArg2(arg0, arg2)
				return
			}
		}

		if arg0.Op == OpARM64MOVDconst {
			imm := auxIntToInt64(arg0.AuxInt)
			if imm&^0x1f == 0 {
				controlValue.reset(OpARM64CCMPconst)
				params = invertConditionsInBlock(block, index)
				params.constValue = uint8(imm)
				params.ind = true
				controlValue.AuxInt = arm64ConditionalParamsToAuxInt(params)
				controlValue.AddArg2(arg1, arg2)
				return
			}
		}
	case OpARM64CCMN:
		params := controlValue.AuxArm64ConditionalParams()
		arg0 := controlValue.Args[0]
		arg1 := controlValue.Args[1]
		arg2 := controlValue.Args[2]
		if arg1.Op == OpARM64MOVDconst {
			imm := auxIntToInt64(arg1.AuxInt)
			if imm&^0x1f == 0 {
				controlValue.reset(OpARM64CCMNconst)
				params.constValue = uint8(imm)
				params.ind = true
				controlValue.AuxInt = arm64ConditionalParamsToAuxInt(params)
				controlValue.AddArg2(arg0, arg2)
				return
			}
		}

		if arg0.Op == OpARM64MOVDconst {
			imm := auxIntToInt64(arg0.AuxInt)
			if imm&^0x1f == 0 {
				controlValue.reset(OpARM64CCMNconst)
				params = invertConditionsInBlock(block, index)
				params.constValue = uint8(imm)
				params.ind = true
				controlValue.AuxInt = arm64ConditionalParamsToAuxInt(params)
				controlValue.AddArg2(arg1, arg2)
				return
			}
		}
	case OpARM64CCMPW:
		params := controlValue.AuxArm64ConditionalParams()
		arg0 := controlValue.Args[0]
		arg1 := controlValue.Args[1]
		arg2 := controlValue.Args[2]
		if arg1.Op == OpARM64MOVDconst {
			imm := auxIntToInt32(arg1.AuxInt)
			if imm&^0x1f == 0 {
				controlValue.reset(OpARM64CCMPWconst)
				params.constValue = uint8(imm)
				params.ind = true
				controlValue.AuxInt = arm64ConditionalParamsToAuxInt(params)
				controlValue.AddArg2(arg0, arg2)
				return
			}
		}

		if arg0.Op == OpARM64MOVDconst {
			imm := auxIntToInt32(arg0.AuxInt)
			if imm&^0x1f == 0 {
				controlValue.reset(OpARM64CCMPWconst)
				params = invertConditionsInBlock(block, index)
				params.constValue = uint8(imm)
				params.ind = true
				controlValue.AuxInt = arm64ConditionalParamsToAuxInt(params)
				controlValue.AddArg2(arg1, arg2)
				return
			}
		}
	case OpARM64CCMNW:
		params := controlValue.AuxArm64ConditionalParams()
		arg0 := controlValue.Args[0]
		arg1 := controlValue.Args[1]
		arg2 := controlValue.Args[2]
		if arg1.Op == OpARM64MOVDconst {
			imm := auxIntToInt32(arg1.AuxInt)
			if imm&^0x1f == 0 {
				controlValue.reset(OpARM64CCMNWconst)
				params.constValue = uint8(imm)
				params.ind = true
				controlValue.AuxInt = arm64ConditionalParamsToAuxInt(params)
				controlValue.AddArg2(arg0, arg2)
				return
			}
		}

		if arg0.Op == OpARM64MOVDconst {
			imm := auxIntToInt32(arg0.AuxInt)
			if imm&^0x1f == 0 {
				controlValue.reset(OpARM64CCMNWconst)
				params = invertConditionsInBlock(block, index)
				params.constValue = uint8(imm)
				params.ind = true
				controlValue.AuxInt = arm64ConditionalParamsToAuxInt(params)
				controlValue.AddArg2(arg1, arg2)
				return
			}
		}
	}
}

func invertConditionsInBlock(block *Block, index int) arm64ConditionalParams {
	params := block.Controls[0].AuxArm64ConditionalParams()
	newKind := invertBlockKind(block.Kind)
	block.Kind = newKind
	if index == 1 {
		newKind = negateBlockKind(newKind)
	}
	params.nzcv = getNzcvByBlockKind(newKind)
	return params
}

func transformToConditionalComparisonValue(block *Block, index int) {
	nestedBlock := block.Succs[index].Block()

	oldValue := block.Controls[0]
	oldKind := block.Kind

	nestedValue := nestedBlock.Controls[0]
	nestedKind := nestedBlock.Kind

	if index == 1 {
		oldKind = negateBlockKind(oldKind)
		nestedKind = negateBlockKind(nestedKind)
	}

	params := getConditionalParamsByBlockKind(oldKind, nestedKind)

	nestedValue.AddArg(oldValue)
	nestedValue.Op = transformOpToConditionalComparisonOperation(nestedValue.Op)
	nestedValue.AuxInt = arm64ConditionalParamsToAuxInt(params)
}

func transformOpToConditionalComparisonOperation(op Op) Op {
	switch op {
	case OpARM64CMP:
		return OpARM64CCMP
	case OpARM64CMN:
		return OpARM64CCMN
	case OpARM64CMPconst:
		return OpARM64CCMPconst
	case OpARM64CMNconst:
		return OpARM64CCMNconst
	case OpARM64CMPW:
		return OpARM64CCMPW
	case OpARM64CMNW:
		return OpARM64CCMNW
	case OpARM64CMPWconst:
		return OpARM64CCMPWconst
	case OpARM64CMNWconst:
		return OpARM64CCMNWconst
	default:
		panic("Incorrect operation")
	}
}

func getConditionalParamsByBlockKind(intKind, exKind BlockKind) arm64ConditionalParams {
	cond := getCondByBlockKind(intKind)
	nzcv := getNzcvByBlockKind(exKind)
	return arm64ConditionalParamsAuxInt(cond, nzcv)
}

func getConditionalParamsWithConstantByBlockKind(intKind, exKind BlockKind, auxConstant uint8) arm64ConditionalParams {
	cond := getCondByBlockKind(intKind)
	nzcv := getNzcvByBlockKind(exKind)
	return arm64ConditionalParamsAuxIntWithValue(cond, nzcv, auxConstant)
}

func getCondByBlockKind(kind BlockKind) Op {
	switch kind {
	case BlockARM64EQ:
		return OpARM64Equal
	case BlockARM64NE:
		return OpARM64NotEqual
	case BlockARM64LT:
		return OpARM64LessThan
	case BlockARM64LE:
		return OpARM64LessEqual
	case BlockARM64GT:
		return OpARM64GreaterThan
	case BlockARM64GE:
		return OpARM64GreaterEqual
	case BlockARM64ULT:
		return OpARM64LessThanU
	case BlockARM64ULE:
		return OpARM64LessEqualU
	case BlockARM64UGT:
		return OpARM64GreaterThanU
	case BlockARM64UGE:
		return OpARM64GreaterEqualU
	default:
		panic("Incorrect kind of Block")
	}
}

func getNzcvByBlockKind(kind BlockKind) uint8 {
	switch kind {
	case BlockARM64EQ:
		return 0 // N=0,Z=0,C=0,V=0
	case BlockARM64NE:
		return 4 // N=0,Z=1,C=0,V=0
	case BlockARM64LT:
		return 0 // N=0,Z=0,C=0,V=0
	case BlockARM64LE:
		return 0 // N=0,Z=0,C=0,V=0
	case BlockARM64GT:
		return 4 // N=0,Z=1,C=0,V=0
	case BlockARM64GE:
		return 1 // N=0,Z=0,C=0,V=1
	case BlockARM64ULT:
		return 2 // N=0,Z=0,C=1,V=0
	case BlockARM64ULE:
		return 2 // N=0,Z=0,C=1,V=0
	case BlockARM64UGT:
		return 0 // N=0,Z=0,C=0,V=0
	case BlockARM64UGE:
		return 0 // N=0,Z=0,C=0,V=0
	default:
		panic("Incorrect kind of Block")
	}
}

func negateBlockKind(kind BlockKind) BlockKind {
	switch kind {
	case BlockARM64EQ:
		return BlockARM64NE
	case BlockARM64NE:
		return BlockARM64EQ
	case BlockARM64LT:
		return BlockARM64GE
	case BlockARM64LE:
		return BlockARM64GT
	case BlockARM64GT:
		return BlockARM64LE
	case BlockARM64GE:
		return BlockARM64LT
	case BlockARM64ULT:
		return BlockARM64UGE
	case BlockARM64ULE:
		return BlockARM64UGT
	case BlockARM64UGT:
		return BlockARM64ULE
	case BlockARM64UGE:
		return BlockARM64ULT
	default:
		panic("Incorrect kind of Block")
	}
}

func invertBlockKind(kind BlockKind) BlockKind {
	switch kind {
	case BlockARM64EQ:
		return BlockARM64EQ
	case BlockARM64NE:
		return BlockARM64NE
	case BlockARM64LT:
		return BlockARM64GT
	case BlockARM64LE:
		return BlockARM64GE
	case BlockARM64GT:
		return BlockARM64LT
	case BlockARM64GE:
		return BlockARM64LE
	case BlockARM64ULT:
		return BlockARM64UGT
	case BlockARM64ULE:
		return BlockARM64UGE
	case BlockARM64UGT:
		return BlockARM64ULT
	case BlockARM64UGE:
		return BlockARM64ULE
	default:
		panic("Incorrect kind of Block")
	}
}
