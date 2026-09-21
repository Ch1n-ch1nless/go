// Copyright 2026 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package runtime

import "unsafe"

const (
	// Size of Goroutine Allocation Buffer
	gabBufferSize = 64 << 10
	gabPageNumber = gabBufferSize >> _PageShift

	// Maximum size of noscan object, which can be allocated in G.A.B.
	gabObjectMaxSize = 128

	// Alignment for all objects in G.A.B.
	gabAlign     = 8
	gabAlignMask = gabAlign - 1
)

type gabAllocState struct {
	base uintptr
	top  uintptr
	end  uintptr
}

func gabAllocEnabled(size uintptr, typ *_type) bool {
	if typ != nil && !typ.Pointers() {
		return size < gabObjectMaxSize
	}
	return false
}

func gabAlloc(size uintptr) (unsafe.Pointer, uintptr) {
	size = (size + gabAlignMask) &^ gabAlignMask
	g := getg()
	if g == nil {
		return nil, 0
	}
	s := &g.gabAlloc

	if s.base == 0 || s.top+size > s.end {
		s.base = 0
		s.top = 0
		var rawSpan *mspan
		systemstack(func() {
			rawSpan = mheap_.allocManual(gabPageNumber, spanAllocGAB)
		})
		if rawSpan == nil {
			return nil, 0
		}

		s.base = rawSpan.base()
		s.top = s.base
		s.end = s.base + gabBufferSize

		if rawSpan.needzero != 0 {
			memclrNoHeapPointers(unsafe.Pointer(s.base), gabBufferSize)
		}
	}

	p := s.top
	s.top = p + size

	return unsafe.Pointer(p), size
}

//go:nosplit
func inGab(p uintptr) bool {
	s := spanOf(p)
	return s != nil && s.state.get() == mSpanManual && p >= s.base() && p < s.limit
}
