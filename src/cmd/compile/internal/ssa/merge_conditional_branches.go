// Copyright 2025 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import (
	"cmd/compile/internal/types"
)

const (
	InvalidIndex            = -1 + iota
	TrueConditionSuccIndex  // Index for true condition successor in block's successor list
	FalseConditionSuccIndex // Index for false condition successor in block's successor list
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
// - if2 must not contain memory operations or side effects
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

	// We iterate in postorder to ensure we process inner conditional blocks before
	// their outer counterparts. This is crucial because:
	// 1. Transformations create new conditional comparisons that combine inner and outer conditions
	// 2. Processing inner blocks first ensures we don't miss nested patterns
	// 3. It maintains the integrity of the CFG during transformations
	// Reverse order (from leaves to root) allows safe modification without affecting
	// yet-to-be-processed outer structures.
	blocks := f.postorder()

	for _, block := range blocks {
		// extSuccIndex: index of the outedge from if1 to if2
		// intSuccIndex: index of the outedge from if2 to b2
		extSuccIndex, intSuccIndex := detectNestedIfPattern(block)

		if extSuccIndex != InvalidIndex && intSuccIndex != InvalidIndex {
			transformNestedIfPattern(block, extSuccIndex, intSuccIndex)
		}
	}
}

// findFirstNonEmptyPlainBlock finds the first non-empty block in a chain of empty plain blocks
// starting from the specified child index of the parent block. It skips over empty blocks
// that serve only as pass-through nodes in the control flow graph.
func findFirstNonEmptyPlainBlock(parentBlock *Block, childIndex int) *Block {
	childBlock := parentBlock.Succs[childIndex].Block()
	for isEmptyPlainBlock(childBlock) {
		childBlock = childBlock.Succs[0].Block()
	}
	return childBlock
}

// isEmptyPlainBlock checks if a block is empty (contains no values), has exactly one
// predecessor and one successor, and is of kind BlockPlain. Such blocks are typically
// artifacts of previous optimizations and can be safely removed or bypassed.
func isEmptyPlainBlock(block *Block) bool {
	if block.Kind == BlockPlain && len(block.Values) == 0 &&
		len(block.Preds) == 1 {
		return true
	}
	return false
}

// removeEmptyPlainBlockChain removes a chain of empty plain blocks starting from
// the specified child index of the parent block. It traverses through consecutive
// empty blocks and deletes them from the control flow graph, connecting the parent
// directly to the first non-empty block in the chain.
func removeEmptyPlainBlockChain(parentBlock *Block, childIndex int) *Block {
	childBlock := parentBlock.Succs[childIndex].Block()
	for isEmptyPlainBlock(childBlock) {
		nextBlock := childBlock.Succs[0].Block()
		removeEmptyPlainBlock(childBlock)
		childBlock = nextBlock
	}
	return childBlock
}

// removeEmptyPlainBlock removes a single empty plain block from the control flow graph.
// It connects the block's predecessor directly to its successor, effectively bypassing
// the empty block, and then marks the block as invalid for future cleanup.
func removeEmptyPlainBlock(block *Block) {
	prevEdge := block.Preds[0]
	nextEdge := block.Succs[0]

	prevEdge.b.Succs[prevEdge.i] = nextEdge
	nextEdge.b.Preds[nextEdge.i] = prevEdge

	block.removePred(0)
	block.removeSucc(0)
	block.Reset(BlockInvalid)
}

// detectNestedIfPattern detects nested if patterns that can be transformed to conditional comparisons.
// It examines the external block to see if it contains a nested conditional structure that matches
// the pattern for if-conversion. Returns the external successor index (which branch contains the
// nested condition) and internal successor index (which branch of the nested condition leads to
// the common merge point), or InvalidIndex if no pattern is detected.
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
		// Both branches lead to the same block, cannot transform
		return InvalidIndex, InvalidIndex
	}

	// Check for cyclic patterns where a condition refers back to the original block
	if thenBlock == extBlock {
		// True branch forms a cycle back to extBlock
		return detectCyclePattern(extBlock, FalseConditionSuccIndex)
	} else if elseBlock == extBlock {
		// False branch forms a cycle back to extBlock
		return detectCyclePattern(extBlock, TrueConditionSuccIndex)
	}

	extSuccIndex := InvalidIndex

	// Check if the true branch contains a nested conditional that can be moved
	if len(thenBlock.Preds) == 1 &&
		len(thenBlock.Succs) == 2 &&
		isIfBlock(thenBlock) &&
		canValuesBeMoved(thenBlock) {
		// True branch contains a valid nested condition
		extSuccIndex = TrueConditionSuccIndex
	} else if len(elseBlock.Preds) == 1 &&
		len(elseBlock.Succs) == 2 &&
		isIfBlock(elseBlock) &&
		canValuesBeMoved(elseBlock) {
		// False branch contains a valid nested condition
		extSuccIndex = FalseConditionSuccIndex
	}

	if extSuccIndex == InvalidIndex {
		// This chain of blocks is not in pattern.
		return InvalidIndex, InvalidIndex
	}

	// Tree structure:
	//
	//                 extBlock
	//                 /      \
	//                /        \
	//     notBothMetBlock   intBlock
	//                        /     \
	//                       /       \
	//                 thenBlock    elseBlock
	//
	// extBlock: The outer conditional block being examined
	// intBlock: The inner conditional block (nested condition)
	// notBothMetBlock: The block reached when the outer condition is not met
	// thenBlock/elseBlock: Successors of the inner conditional block
	intBlock := findFirstNonEmptyPlainBlock(extBlock, extSuccIndex)
	notBothMetBlock := findFirstNonEmptyPlainBlock(extBlock, extSuccIndex^1)
	thenBlock = findFirstNonEmptyPlainBlock(intBlock, TrueConditionSuccIndex)
	elseBlock = findFirstNonEmptyPlainBlock(intBlock, FalseConditionSuccIndex)

	// Determine which inner branch leads to the common merge point
	// This identifies the logical operation type (AND/OR)
	intSuccIndex := InvalidIndex
	if notBothMetBlock == elseBlock {
		// Pattern: if (A && B) - notBothMetBlock is reached when A is false,
		// which is the same as the else branch of the inner condition
		intSuccIndex = TrueConditionSuccIndex
	} else if notBothMetBlock == thenBlock {
		// Pattern: if (A || B) - notBothMetBlock is reached when A is false,
		// which is the same as the then branch of the inner condition
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

// detectCyclePattern detects cyclic patterns where a conditional block's successor
// refers back to the original block. This handles special cases where the control
// flow forms a loop-like structure that can still be optimized with conditional comparisons.
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

	// Check if the cycle connects back to the original block and verify phi consistency
	if extBlock == thenBlock {
		// True branch of second condition leads back to extBlock
		if !checkSameValuesInPhiNodes(extBlock, secondCondBlock, exitIndex^1, TrueConditionSuccIndex) {
			return InvalidIndex, InvalidIndex
		}
		return exitIndex, FalseConditionSuccIndex
	} else if extBlock == elseBlock {
		// False branch of second condition leads back to extBlock
		if !checkSameValuesInPhiNodes(extBlock, secondCondBlock, exitIndex^1, FalseConditionSuccIndex) {
			return InvalidIndex, InvalidIndex
		}
		return exitIndex, TrueConditionSuccIndex
	}
	return InvalidIndex, InvalidIndex
}

// checkSameValuesInPhiNodes checks if phi nodes in merge blocks have the same values
// for the given successor indices. This ensures that after transformation, phi nodes
// will receive the correct values from both paths. Returns true if all phi nodes
// have consistent arguments for the specified paths.
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
		// TODO: Fix the panic message!
		panic("The invalid pointers to block!")
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

// canValuesBeMoved checks if all values in a block can be safely moved to another block.
// This is necessary because during transformation, values from the inner conditional
// block are moved to the outer block. Values with side effects, memory operations,
// or phi nodes cannot be moved.
func canValuesBeMoved(b *Block) bool {
	for _, v := range b.Values {
		if !canValueBeMoved(v) {
			return false
		}
	}
	return true
}

// canValueBeMoved checks if a single value can be safely moved to another block.
// Returns false for values that have side effects, are memory operations, phi nodes,
// or nil checks, as moving these could change program semantics.
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

// isIfBlock checks if a block is a conditional block that can participate in
// if-conversion. This includes all ARM64 conditional block kinds (EQ, NE, LT, etc.)
// and zero/non-zero test blocks (Z, NZ, ZW, NZW).
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
		if len(b.Controls) != 1 {
			// Must have exactly one control value for predictable transformation
			return false
		}
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

// isComparisonOperation checks if a value represents a comparison operation
// that can be used in conditional execution. Also ensures the value has only
// one use to prevent unexpected side effects from transformation.
func isComparisonOperation(value *Value) bool {
	if value.Uses != 1 {
		// This value can be transformed to another value.
		// New value can get another results, not which are expected.
		// That why we need to check this case.
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

// transformNestedIfPattern transforms a detected nested if pattern into a
// conditional comparison. This is the main transformation function that
// coordinates all the steps needed to convert the nested conditionals into
// a single conditional comparison instruction.
func transformNestedIfPattern(extBlock *Block, extSuccIndex, intSuccIndex int) {
	clearPatternFromEmptyPlainBlocks(extBlock, extSuccIndex)
	intBlock := extBlock.Succs[extSuccIndex].Block()

	// Transform the control flow step by step:
	// 1. Transform primary comparison to standard form if needed
	// 2. Transform dependent comparison to work with conditional execution
	// 3. Convert to conditional comparison operation (CCMP/CCMN)
	// 4. Fix comparisons with constants to use constant forms when possible
	// 5. Set the new control value for the transformed block
	// 6. Move all values from inner block to outer block
	// 7. Eliminate the now-redundant nested block
	transformPrimaryComparisonValue(extBlock)
	transformDependentComparisonValue(intBlock)
	transformToConditionalComparisonValue(extBlock, extSuccIndex, intSuccIndex)
	fixComparisonWithConstant(intBlock, extSuccIndex)
	setNewControlValue(extBlock, intBlock, extSuccIndex, intSuccIndex)
	moveAllValues(extBlock, intBlock)
	elimNestedBlock(intBlock, intSuccIndex)
}

// clearPatternFromEmptyPlainBlocks removes all empty plain blocks from the
// detected pattern to simplify the control flow graph before transformation.
func clearPatternFromEmptyPlainBlocks(extBlock *Block, extSuccIndex int) {
	intBlock := removeEmptyPlainBlockChain(extBlock, extSuccIndex)
	removeEmptyPlainBlockChain(extBlock, extSuccIndex^1)

	removeEmptyPlainBlockChain(intBlock, TrueConditionSuccIndex)
	removeEmptyPlainBlockChain(intBlock, FalseConditionSuccIndex)
}

// moveAllValues moves all values from the source block to the destination block.
// This is used to consolidate the computations from the inner conditional block
// into the outer block as part of the if-conversion process.
func moveAllValues(dest, src *Block) {
	for _, value := range src.Values {
		value.Block = dest
		dest.Values = append(dest.Values, value)
	}
	src.truncateValues(0)
}

// elimNestedBlock eliminates a nested block that has been incorporated into
// the outer block through if-conversion. It removes the specified successor
// edge and updates phi nodes in the target block to remove the corresponding argument.
func elimNestedBlock(b *Block, index int) {
	removedEdge := b.Succs[index^1]

	notBothMetBlock := removedEdge.Block()
	i := removedEdge.Index()

	b.removeSucc(index ^ 1)
	notBothMetBlock.removePred(i)
	for _, v := range notBothMetBlock.Values {
		if v.Op != OpPhi {
			continue
		}
		notBothMetBlock.removePhiArg(v, i)
	}

	b.Func.invalidateCFG()
	b.Reset(BlockPlain)
	b.Likely = BranchUnknown
}

// setNewControlValue sets the new control value for the transformed block
// based on the inner block's control value. It also updates the branch
// likelihood based on the original block's branch prediction.
func setNewControlValue(extBlock, intBlock *Block, extSuccIndex, intSuccIndex int) {
	extBlock.resetWithControl(intBlock.Kind, intBlock.Controls[0])
	if !checkLikelyAndIndex(extBlock, extSuccIndex) ||
		!checkLikelyAndIndex(intBlock, intSuccIndex) {
		extBlock.Likely = BranchUnknown
	}
}

// checkLikelyAndIndex checks if the branch likelihood matches the expected
// index. Returns true if the likelihood is consistent with the branch direction.
func checkLikelyAndIndex(b *Block, index int) bool {
	if index == TrueConditionSuccIndex && b.Likely == BranchLikely {
		return true
	} else if index == FalseConditionSuccIndex && b.Likely == BranchUnlikely {
		return true
	}
	return false
}

// transformPrimaryComparisonValue transforms special block kinds (Z, NZ, ZW, NZW)
// into standard comparison operations. These block kinds test for zero/non-zero
// and need to be converted to explicit comparisons with zero for conditional execution.
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

// transformDependentComparisonValue transforms the comparison in the dependent
// (inner) block to prepare it for conditional execution. This involves converting
// constant comparisons to register comparisons and handling special block kinds.
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

		switch value.Op {
		case OpARM64CMPconst:
			arg0 := value.Args[0]
			auxConstant := auxIntToInt64(value.AuxInt)
			value.reset(OpARM64CMP)
			constantValue := block.Func.constVal(OpARM64MOVDconst, typ.UInt64, auxConstant, true)
			value.AddArg2(arg0, constantValue)
		case OpARM64CMNconst:
			arg0 := value.Args[0]
			auxConstant := auxIntToInt64(value.AuxInt)
			value.reset(OpARM64CMN)
			constantValue := block.Func.constVal(OpARM64MOVDconst, typ.UInt64, auxConstant, true)
			value.AddArg2(arg0, constantValue)
		case OpARM64CMPWconst:
			arg0 := value.Args[0]
			auxConstant := auxIntToInt32(value.AuxInt)
			value.reset(OpARM64CMPW)
			constantValue := block.Func.constVal(OpARM64MOVDconst, typ.UInt64, int64(auxConstant), true)
			value.AddArg2(arg0, constantValue)
		case OpARM64CMNWconst:
			arg0 := value.Args[0]
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

// fixComparisonWithConstant optimizes conditional comparisons by converting
// them to constant forms when one operand is a small constant. This generates
// more efficient CCMPconst/CCMNconst instructions.
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
			if imm&^0x1f == 0 { // Check if constant fits in 5 bits
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
			if imm&^0x1f == 0 { // Check if constant fits in 5 bits
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
		// Similar optimization for CCMN operations
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
		// 32-bit version of CCMP constant optimization
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
		// 32-bit version of CCMN constant optimization
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

// invertConditionsInBlock inverts the condition in a block and returns updated
// conditional parameters. This is used when swapping operands in constant
// optimizations to maintain correct semantics.
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

// transformToConditionalComparisonValue transforms the comparison operations
// to conditional comparison operations (CCMP/CCMN). This is the core transformation
// that creates the conditional execution pattern by combining the outer and inner
// conditions into a single conditional comparison instruction.
func transformToConditionalComparisonValue(extBlock *Block, extSuccIndex, intSuccIndex int) {
	intBlock := extBlock.Succs[extSuccIndex].Block()

	// Adjust block kinds and successors if needed to match expected pattern
	if extSuccIndex != intSuccIndex {
		extBlock.Kind = negateBlockKind(extBlock.Kind)
		extBlock.swapSuccessors()
		extSuccIndex ^= 1
	}

	oldValue := extBlock.Controls[0]
	oldKind := extBlock.Kind

	newValue := intBlock.Controls[0]
	newKind := intBlock.Kind

	// Adjust conditions based on successor index
	if extSuccIndex == FalseConditionSuccIndex {
		oldKind = negateBlockKind(oldKind)
		newKind = negateBlockKind(newKind)
	}

	// Get conditional parameters and transform the operation
	params := getConditionalParamsByBlockKind(oldKind, newKind)

	newValue.AddArg(oldValue)
	newValue.Op = transformOpToConditionalComparisonOperation(newValue.Op)
	newValue.AuxInt = arm64ConditionalParamsToAuxInt(params)
}

// transformOpToConditionalComparisonOperation maps standard comparison operations
// to their conditional comparison counterparts (e.g., CMP -> CCMP, CMN -> CCMN).
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

// getConditionalParamsByBlockKind generates conditional parameters for
// conditional comparison operations based on the block kinds (conditions).
func getConditionalParamsByBlockKind(intKind, exKind BlockKind) arm64ConditionalParams {
	cond := condByBlockKind(intKind)
	nzcv := nzcvByBlockKind(exKind)
	return arm64ConditionalParamsAuxInt(cond, nzcv)
}

// condByBlockKind maps block kinds to their corresponding condition codes
// for ARM64 conditional execution.
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

// nzcvByBlockKind maps block kinds to their corresponding NZCV flag values
// for conditional comparison operations. NZCV flags represent the condition
// codes: Negative, Zero, Carry, Overflow.
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

// packNZCV packs boolean condition flags into a single byte representing
// the ARM64 NZCV condition flags: Negative, Zero, Carry, Overflow.
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

// negateBlockKind returns the logical negation of a block kind
// (e.g., EQ becomes NE, LT becomes GE).
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

// invertBlockKind inverts the operands of a comparison block kind
// (e.g., LT becomes GT, LE becomes GE).
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
