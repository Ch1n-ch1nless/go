package ssa

func skipEmptyPlains(f *Func) {
	blocks := f.Blocks()
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
	block.removePred(0)
	block.Reset(BlockInvalid)
}

func mergeConditionalBranches(f *Func) {
	skipEmptyPlains(f)
}
