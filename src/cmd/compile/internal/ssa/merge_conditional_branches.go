package ssa

import (
	"os"
)

func skipEmptyPlains(f *Func) {
	blocks := f.Blocks
	for _, block := range blocks {
		if isEmptyPlainBlock(block) {
			deleteEmptyPlainBlock(block)
		}
	}
}

func isEmptyPlainBlock(block *Block) bool {
	if block.Kind == BlockPlain && len(block.Values) == 0 && len(block.Preds) == 1 {
		return true
	}
	return false
}

func deleteEmptyPlainBlock(block *Block) {
	prevEdge := block.Preds[0]
	nextEdge := block.Succs[0]

	prevEdge.b.Succs[prevEdge.i] = nextEdge
	nextEdge.b.Preds[nextEdge.i] = prevEdge

	invalidateEmptyPlainBlock(block)
}

func invalidateEmptyPlainBlock(block *Block) {
	block.removePred(0)
	block.removeSucc(0)
	block.Reset(BlockInvalid)
}

func mergeConditionalBranches(f *Func) {
	if envVar := os.Getenv("CCMP_GEN"); envVar != "YES" {
		return
	}

	skipEmptyPlains(f)

	blocks := f.postorder()

	for _, block := range blocks {
		if detectNestedIfBlock(block, 0) {
			transformNestedIfBlock(block, 0)
		} else {
			if detectNestedIfBlock(block, 1) {
				transformNestedIfBlock(block, 1)
			}
		}
	}
}

func detectNestedIfBlock(b *Block, index int) bool {
	if !isIfBlock(b) {
		return false
	}

	nestedBlock := b.Succs[index].Block()
	if nestedBlock == b || nestedBlock == b.Succs[index^1].Block() {
		return false
	}

	if !isIfBlock(nestedBlock) ||
		!canValuesBeMoved(nestedBlock) ||
		len(nestedBlock.Preds) != 1 {
		return false
	}

	if b.Succs[index^1].Block() == nestedBlock.Succs[index^1].Block() {
		return !hasPhi(b.Succs[index^1].Block())
	}
	return false
}

func canValuesBeMoved(b *Block) bool {
	for _, v := range b.Values {
		for _, a := range v.Args {
			if a.Type.IsMemory() {
				return false
			}
		}
	}

	for _, v := range b.Controls[0].Args {
		for _, a := range v.Args {
			if a.Type.IsMemory() {
				return false
			}
		}
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
		return isComparisonOperation(b)
	default:
		return false
	}
}

func isComparisonOperation(b *Block) bool {
	value := b.Controls[0]
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
	nestedBlock := b.Succs[index].Block()

	transformControlValue(b)
	transformControlValue(nestedBlock)
	transformToConditionalComparisonValue(b, nestedBlock)
	setNewControlValue(b, nestedBlock)
	moveAllValues(b, nestedBlock)
	elimNestedBlock(nestedBlock, index)
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

	removedEdge.b.removePred(removedEdge.i)

	b.removePred(0)
	b.removeSucc(1)
	b.removeSucc(0)
	b.Reset(BlockInvalid)
}

func setNewControlValue(block, nestedBlock *Block) {
	block.resetWithControl(nestedBlock.Kind, nestedBlock.Controls[0])
	block.Likely = BranchUnknown
	nestedBlock.Likely = BranchUnknown
}

func transformControlValue(block *Block) {
	value := block.Controls[0]
	typ := &block.Func.Config.Types
	arg0 := value.Args[0]

	switch value.Op {
	case OpARM64CMPconst:
		auxConstant := auxIntToInt64(value.AuxInt)
		value.reset(OpARM64CMP)
		constantValue := block.NewValue0(value.Pos, OpARM64MOVDconst, typ.UInt64)
		constantValue.AuxInt = int64ToAuxInt(auxConstant)
		value.AddArg2(arg0, constantValue)
	case OpARM64CMNconst:
		auxConstant := auxIntToInt64(value.AuxInt)
		value.reset(OpARM64CMN)
		constantValue := block.NewValue0(value.Pos, OpARM64MOVDconst, typ.UInt64)
		constantValue.AuxInt = int64ToAuxInt(auxConstant)
		value.AddArg2(arg0, constantValue)
	case OpARM64CMPWconst:
		auxConstant := auxIntToInt32(value.AuxInt)
		value.reset(OpARM64CMPW)
		constantValue := block.NewValue0(value.Pos, OpARM64MOVDconst, typ.UInt64)
		constantValue.AuxInt = int64ToAuxInt(int64(auxConstant))
		value.AddArg2(arg0, constantValue)
	case OpARM64CMNWconst:
		auxConstant := auxIntToInt32(value.AuxInt)
		value.reset(OpARM64CMNW)
		constantValue := block.NewValue0(value.Pos, OpARM64MOVDconst, typ.UInt64)
		constantValue.AuxInt = int64ToAuxInt(int64(auxConstant))
		value.AddArg2(arg0, constantValue)
	}
}

func transformToConditionalComparisonValue(block, nestedBlock *Block) {
	oldValue := block.Controls[0]
	oldKind := block.Kind

	nestedValue := nestedBlock.Controls[0]
	nestedKind := nestedBlock.Kind

	if nestedBlock == block.Succs[1].Block() {
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
		return 0
	case BlockARM64NE:
		return 4
	case BlockARM64LT:
		return 0
	case BlockARM64LE:
		return 0
	case BlockARM64GT:
		return 4
	case BlockARM64GE:
		return 1
	case BlockARM64ULT:
		return 2
	case BlockARM64ULE:
		return 2
	case BlockARM64UGT:
		return 0
	case BlockARM64UGE:
		return 0
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
