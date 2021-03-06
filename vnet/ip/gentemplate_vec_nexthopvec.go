// autogenerated: do not edit!
// generated from gentemplate [gentemplate -d Package=ip -id nextHopVec -d VecType=nextHopVec -d Type=nextHop github.com/platinasystems/go/elib/vec.tmpl]

// Copyright 2016 Platina Systems, Inc. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ip

import (
	"github.com/platinasystems/go/elib"
)

type nextHopVec []nextHop

func (p *nextHopVec) Resize(n uint) {
	c := elib.Index(cap(*p))
	l := elib.Index(len(*p)) + elib.Index(n)
	if l > c {
		c = elib.NextResizeCap(l)
		q := make([]nextHop, l, c)
		copy(q, *p)
		*p = q
	}
	*p = (*p)[:l]
}

func (p *nextHopVec) validate(new_len uint, zero nextHop) *nextHop {
	c := elib.Index(cap(*p))
	lʹ := elib.Index(len(*p))
	l := elib.Index(new_len)
	if l <= c {
		// Need to reslice to larger length?
		if l > lʹ {
			*p = (*p)[:l]
			for i := lʹ; i < l; i++ {
				(*p)[i] = zero
			}
		}
		return &(*p)[l-1]
	}
	return p.validateSlowPath(zero, c, l, lʹ)
}

func (p *nextHopVec) validateSlowPath(zero nextHop, c, l, lʹ elib.Index) *nextHop {
	if l > c {
		cNext := elib.NextResizeCap(l)
		q := make([]nextHop, cNext, cNext)
		copy(q, *p)
		for i := c; i < cNext; i++ {
			q[i] = zero
		}
		*p = q[:l]
	}
	if l > lʹ {
		*p = (*p)[:l]
	}
	return &(*p)[l-1]
}

func (p *nextHopVec) Validate(i uint) *nextHop {
	var zero nextHop
	return p.validate(i+1, zero)
}

func (p *nextHopVec) ValidateInit(i uint, zero nextHop) *nextHop {
	return p.validate(i+1, zero)
}

func (p *nextHopVec) ValidateLen(l uint) (v *nextHop) {
	if l > 0 {
		var zero nextHop
		v = p.validate(l, zero)
	}
	return
}

func (p *nextHopVec) ValidateLenInit(l uint, zero nextHop) (v *nextHop) {
	if l > 0 {
		v = p.validate(l, zero)
	}
	return
}

func (p nextHopVec) Len() uint { return uint(len(p)) }
