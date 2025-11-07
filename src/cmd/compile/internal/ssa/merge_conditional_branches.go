// Copyright 2025 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import (
	"cmd/compile/internal/types"
)

const (
	InvalidIndex = -1 + iota
	TrueConditionSuccIndex
	FalseConditionSuccIndex
)

// mergeConditionalBranches performs if-conversion optimization on ARM64 by
// transforming nested conditional branches into conditional comparison instructions.
//
// The optimization detects patterns where two consecutive conditional branches
// implement logical AND/OR operations and replaces them with CCMP/CCMN instructions
// that execute the second conditionally based on the first comparison result.
//
// Transformation Pattern:
//
// Original CFG:
//
//	  if1 (outer condition)
//	  /  \
//	 /    \
//	/      if2 (inner condition)
//	|     /   \
//	|    /     \
//	|   /       \
//	b1 (target)  b2 (target)
//
// Transformed CFG:
//
//	 new_if (conditional comparison)
//	  /  \
//	 /    \
//	/       p (empty plain block)
//	|        \
//	|         \
//	|          \
//	b1 (target)  b2 (target)
//
// Transformation Conditions:
// - Both if1 and if2 must be ARM64 conditional blocks
// - if2 must have exactly one predecessor from if1
// - if2 must not contain memory operations, side effects, or phi nodes
// - The transformation must preserve phi node consistency in successor blocks
//
// This optimization eliminates branch mispredictions and improves instruction-level
// parallelism by leveraging ARM64's conditional execution capabilities.
// The resulting code uses conditional comparison instructions that test the second
// condition only if the first condition evaluates to a specific value.
func mergeConditionalBranches(f *Func) {
	if f.Config.arch != "arm64" {
		return
	}

	blocks := f.postorder()

	for _, block := range blocks {
		extSuccIndex, intSuccIndex := detectNestedIfPattern(block)
		if extSuccIndex != InvalidIndex && intSuccIndex != InvalidIndex {
			transformNestedIfPattern(block, extSuccIndex, intSuccIndex)
		}
	}
}

func findFirstNonEmptyPlainBlock(parentBlock *Block, childIndex int) *Block {
	childBlock := parentBlock.Succs[childIndex].Block()
	for isEmptyPlainBlock(childBlock) {
		childBlock = childBlock.Succs[0].Block()
	}
	return childBlock
}

func isEmptyPlainBlock(block *Block) bool {
	if block.Kind == BlockPlain && len(block.Values) == 0 &&
		len(block.Preds) == 1 && len(block.Succs) == 1 {
		return true
	}
	return false
}

func deleteEmptyPlainBlockChain(parentBlock *Block, childIndex int) *Block {
	childBlock := parentBlock.Succs[childIndex].Block()
	for isEmptyPlainBlock(childBlock) {
		nextBlock := childBlock.Succs[0].Block()
		deleteEmptyPlainBlock(childBlock)
		childBlock = nextBlock
	}
	return childBlock
}

func deleteEmptyPlainBlock(block *Block) {
	prevEdge := block.Preds[0]
	nextEdge := block.Succs[0]

	prevEdge.b.Succs[prevEdge.i] = nextEdge
	nextEdge.b.Preds[nextEdge.i] = prevEdge

	block.removePred(0)
	block.removeSucc(0)
	block.Reset(BlockInvalid)
}

// detectNestedIfPattern detects nested if pattern that can be transformed to conditional comparison
// Returns external successor index and internal successor index
func detectNestedIfPattern(extBlock *Block) (int, int) {
	if !isIfBlock(extBlock) {
		// extBlock doesn't contain comparison
		return InvalidIndex, InvalidIndex
	}

	// Skip empty blocks to find actual conditional targets
	// Empty plain blocks are often inserted by previous optimizations
	thenBlock := findFirstNonEmptyPlainBlock(extBlock, TrueConditionSuccIndex)
	elseBlock := findFirstNonEmptyPlainBlock(extBlock, FalseConditionSuccIndex)
	if thenBlock == elseBlock {
		// transformation of this block will be invalid
		return InvalidIndex, InvalidIndex
	}

	if thenBlock == extBlock {
		return detectCyclePattern(extBlock, FalseConditionSuccIndex)
	} else if elseBlock == extBlock {
		return detectCyclePattern(extBlock, TrueConditionSuccIndex)
	}

	extSuccIndex := InvalidIndex
	if len(thenBlock.Preds) == 1 &&
		len(thenBlock.Succs) == 2 &&
		isIfBlock(thenBlock) &&
		canValuesBeMoved(thenBlock) {
		extSuccIndex = TrueConditionSuccIndex
	} else if len(elseBlock.Preds) == 1 &&
		len(elseBlock.Succs) == 2 &&
		isIfBlock(elseBlock) &&
		canValuesBeMoved(elseBlock) {
		extSuccIndex = FalseConditionSuccIndex
	}

	if extSuccIndex == InvalidIndex {
		return InvalidIndex, InvalidIndex
	}

	intBlock := findFirstNonEmptyPlainBlock(extBlock, extSuccIndex)
	notBothMetBlock := findFirstNonEmptyPlainBlock(extBlock, extSuccIndex^1)
	thenBlock = findFirstNonEmptyPlainBlock(intBlock, TrueConditionSuccIndex)
	elseBlock = findFirstNonEmptyPlainBlock(intBlock, FalseConditionSuccIndex)

	// Prevent infinite loops - if inner block refers to itself, transformation would break CFG
	if intBlock == thenBlock || intBlock == elseBlock {
		return InvalidIndex, InvalidIndex
	}

	// Determine which inner branch leads to the common merge point
	// This identifies the logical operation type (AND/OR)
	intSuccIndex := InvalidIndex
	if notBothMetBlock == elseBlock {
		intSuccIndex = TrueConditionSuccIndex
	} else if notBothMetBlock == thenBlock {
		intSuccIndex = FalseConditionSuccIndex
	}

	if intSuccIndex == InvalidIndex {
		return InvalidIndex, InvalidIndex
	}

	// Critical check: ensure phi nodes in merge blocks have consistent values
	// This guarantees semantic preservation after transformation
	if !checkSameValuesInPhiNodes(extBlock, intBlock, extSuccIndex^1, intSuccIndex^1) {
		return InvalidIndex, InvalidIndex
	}

	return extSuccIndex, intSuccIndex
}

// detectCyclePattern detects cyclic pattern where condition refers back to original block
func detectCyclePattern(extBlock *Block, exitIndex int) (int, int) {
	secondCondBlock := findFirstNonEmptyPlainBlock(extBlock, exitIndex)

	if len(secondCondBlock.Preds) != 1 ||
		len(secondCondBlock.Succs) != 2 ||
		!isIfBlock(secondCondBlock) ||
		!canValuesBeMoved(secondCondBlock) {
		return InvalidIndex, InvalidIndex
	}

	thenBlock := findFirstNonEmptyPlainBlock(secondCondBlock, TrueConditionSuccIndex)
	elseBlock := findFirstNonEmptyPlainBlock(secondCondBlock, FalseConditionSuccIndex)

	if thenBlock == elseBlock {
		// Both branches pointing to same block indicates degenerate case
		return InvalidIndex, InvalidIndex
	}

	if extBlock == thenBlock {
		if !checkSameValuesInPhiNodes(extBlock, secondCondBlock, exitIndex^1, TrueConditionSuccIndex) {
			return InvalidIndex, InvalidIndex
		}
		return exitIndex, FalseConditionSuccIndex
	} else if extBlock == elseBlock {
		if !checkSameValuesInPhiNodes(extBlock, secondCondBlock, exitIndex^1, FalseConditionSuccIndex) {
			return InvalidIndex, InvalidIndex
		}
		return exitIndex, TrueConditionSuccIndex
	}
	return InvalidIndex, InvalidIndex
}

// checkSameValuesInPhiNodes checks if phi nodes have same values for given successor indices
func checkSameValuesInPhiNodes(extBlock, intBlock *Block, extSuccIndex, intSuccIndex int) bool {
	// Skip empty blocks to find actual phi-containing merge blocks
	// Empty blocks don't affect phi nodes but complicate path tracking
	for isEmptyPlainBlock(extBlock.Succs[extSuccIndex].Block()) {
		extBlock = extBlock.Succs[extSuccIndex].Block()
		extSuccIndex = 0 // After empty block, only one path exists
	}

	for isEmptyPlainBlock(intBlock.Succs[intSuccIndex].Block()) {
		intBlock = intBlock.Succs[intSuccIndex].Block()
		intSuccIndex = 0
	}

	// Both paths must lead to the same merge block for transformation to be valid
	if extBlock.Succs[extSuccIndex].Block() != intBlock.Succs[intSuccIndex].Block() {
		return false
	}

	argIndex1 := extBlock.Succs[extSuccIndex].Index()
	argIndex2 := intBlock.Succs[intSuccIndex].Index()

	resultBlock := extBlock.Succs[extSuccIndex].Block()
	for _, v := range resultBlock.Values {
		if v.Op != OpPhi {
			continue
		}

		// If phi arguments from different paths don't match,
		// merging the conditions would produce wrong values
		if v.Args[argIndex1] != v.Args[argIndex2] {
			return false
		}
	}

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
	}
	if v.Type.IsMemory() {
		return false
	}
	if v.Op.HasSideEffects() {
		return false
	}
	if opcodeTable[v.Op].nilCheck {
		return false
	}
	if v.MemoryArg() != nil {
		return false
	}
	return true
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

func transformNestedIfPattern(extBlock *Block, extSuccIndex, intSuccIndex int) {
	clearPatternFromEmptyPlainBlocks(extBlock, extSuccIndex)
	intBlock := extBlock.Succs[extSuccIndex].Block()

	transformPrimaryComparisonValue(extBlock)
	transformDependentComparisonValue(intBlock)
	transformToConditionalComparisonValue(extBlock, extSuccIndex, intSuccIndex)
	fixComparisonWithConstant(intBlock, extSuccIndex)
	setNewControlValue(extBlock, intBlock, extSuccIndex, intSuccIndex)
	moveAllValues(extBlock, intBlock)
	elimNestedBlock(intBlock, intSuccIndex)
}

func clearPatternFromEmptyPlainBlocks(extBlock *Block, extSuccIndex int) {
	intBlock := deleteEmptyPlainBlockChain(extBlock, extSuccIndex)
	deleteEmptyPlainBlockChain(extBlock, extSuccIndex^1)

	deleteEmptyPlainBlockChain(intBlock, TrueConditionSuccIndex)
	deleteEmptyPlainBlockChain(intBlock, FalseConditionSuccIndex)
}

func moveAllValues(dest, src *Block) {
	for _, value := range src.Values {
		value.Block = dest
		dest.Values = append(dest.Values, value)
	}
	src.truncateValues(0)
}

func elimNestedBlock(b *Block, index int) {
	removedEdge := b.Succs[index^1]

	falseResultBlock := removedEdge.Block()
	i := removedEdge.Index()

	b.removeSucc(index ^ 1)
	falseResultBlock.removePred(i)
	for _, v := range falseResultBlock.Values {
		if v.Op != OpPhi {
			continue
		}
		falseResultBlock.removePhiArg(v, i)
	}

	b.Func.invalidateCFG()
	b.Reset(BlockPlain)
	b.Likely = BranchUnknown
}

func setNewControlValue(extBlock, intBlock *Block, extSuccIndex, intSuccIndex int) {
	extBlock.resetWithControl(intBlock.Kind, intBlock.Controls[0])
	if !checkLikelyAndIndex(extBlock, extSuccIndex) ||
		!checkLikelyAndIndex(intBlock, intSuccIndex) {
		extBlock.Likely = BranchUnknown
	}
}

func checkLikelyAndIndex(b *Block, index int) bool {
	if index == TrueConditionSuccIndex && b.Likely == BranchLikely {
		return true
	} else if index == FalseConditionSuccIndex && b.Likely == BranchUnlikely {
		return true
	}
	return false
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
	default:
		return
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
		default:
			return
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
	default:
		return
	}
}

func invertConditionsInBlock(block *Block, index int) arm64ConditionalParams {
	params := block.Controls[0].AuxArm64ConditionalParams()
	newKind := invertBlockKind(block.Kind)
	block.Kind = newKind
	if index == FalseConditionSuccIndex {
		newKind = negateBlockKind(newKind)
	}
	params.nzcv = nzcvByBlockKind(newKind)
	return params
}

func transformToConditionalComparisonValue(extBlock *Block, extSuccIndex, intSuccIndex int) {
	intBlock := extBlock.Succs[extSuccIndex].Block()

	if extSuccIndex != intSuccIndex {
		extBlock.Kind = negateBlockKind(extBlock.Kind)
		extBlock.swapSuccessors()
		extSuccIndex ^= 1
	}

	oldValue := extBlock.Controls[0]
	oldKind := extBlock.Kind

	newValue := intBlock.Controls[0]
	newKind := intBlock.Kind

	if extSuccIndex == FalseConditionSuccIndex {
		oldKind = negateBlockKind(oldKind)
		newKind = negateBlockKind(newKind)
	}

	params := getConditionalParamsByBlockKind(oldKind, newKind)

	newValue.AddArg(oldValue)
	newValue.Op = transformOpToConditionalComparisonOperation(newValue.Op)
	newValue.AuxInt = arm64ConditionalParamsToAuxInt(params)
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
	cond := condByBlockKind(intKind)
	nzcv := nzcvByBlockKind(exKind)
	return arm64ConditionalParamsAuxInt(cond, nzcv)
}

func getConditionalParamsWithConstantByBlockKind(intKind, exKind BlockKind, auxConstant uint8) arm64ConditionalParams {
	cond := condByBlockKind(intKind)
	nzcv := nzcvByBlockKind(exKind)
	return arm64ConditionalParamsAuxIntWithValue(cond, nzcv, auxConstant)
}

func condByBlockKind(kind BlockKind) Op {
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

func nzcvByBlockKind(kind BlockKind) uint8 {
	switch kind {
	case BlockARM64EQ:
		return packNZCV(false, false, false, false) // N=0,Z=0,C=0,V=0
	case BlockARM64NE:
		return packNZCV(false, true, false, false) // N=0,Z=1,C=0,V=0
	case BlockARM64LT:
		return packNZCV(false, false, false, false) // N=0,Z=0,C=0,V=0
	case BlockARM64LE:
		return packNZCV(false, false, false, false) // N=0,Z=0,C=0,V=0
	case BlockARM64GT:
		return packNZCV(false, true, false, false) // N=0,Z=1,C=0,V=0
	case BlockARM64GE:
		return packNZCV(false, false, false, true) // N=0,Z=0,C=0,V=1
	case BlockARM64ULT:
		return packNZCV(false, false, true, false) // N=0,Z=0,C=1,V=0
	case BlockARM64ULE:
		return packNZCV(false, false, true, false) // N=0,Z=0,C=1,V=0
	case BlockARM64UGT:
		return packNZCV(false, false, false, false) // N=0,Z=0,C=0,V=0
	case BlockARM64UGE:
		return packNZCV(false, false, false, false) // N=0,Z=0,C=0,V=0
	default:
		panic("Incorrect kind of Block")
	}
}

func packNZCV(N, Z, C, V bool) uint8 {
	var NZCVFlags uint8 = 0
	if N {
		NZCVFlags |= 1 << 3
	}
	if Z {
		NZCVFlags |= 1 << 2
	}
	if C {
		NZCVFlags |= 1 << 1
	}
	if V {
		NZCVFlags |= 1
	}
	return NZCVFlags
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
