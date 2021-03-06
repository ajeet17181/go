// autogenerated: do not edit!
// generated from gentemplate [gentemplate -d Package=vnet -id enqueue -d VecType=enqueue_vec -d Type=*enqueue github.com/platinasystems/go/elib/vec.tmpl]

// Copyright 2016 Platina Systems, Inc. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package vnet

import (
	"github.com/platinasystems/go/elib"
)

type enqueue_vec []*enqueue

func (p *enqueue_vec) Resize(n uint) {
	c := elib.Index(cap(*p))
	l := elib.Index(len(*p)) + elib.Index(n)
	if l > c {
		c = elib.NextResizeCap(l)
		q := make([]*enqueue, l, c)
		copy(q, *p)
		*p = q
	}
	*p = (*p)[:l]
}

func (p *enqueue_vec) validate(new_len uint, zero *enqueue) **enqueue {
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

func (p *enqueue_vec) validateSlowPath(zero *enqueue, c, l, lʹ elib.Index) **enqueue {
	if l > c {
		cNext := elib.NextResizeCap(l)
		q := make([]*enqueue, cNext, cNext)
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

func (p *enqueue_vec) Validate(i uint) **enqueue {
	var zero *enqueue
	return p.validate(i+1, zero)
}

func (p *enqueue_vec) ValidateInit(i uint, zero *enqueue) **enqueue {
	return p.validate(i+1, zero)
}

func (p *enqueue_vec) ValidateLen(l uint) (v **enqueue) {
	if l > 0 {
		var zero *enqueue
		v = p.validate(l, zero)
	}
	return
}

func (p *enqueue_vec) ValidateLenInit(l uint, zero *enqueue) (v **enqueue) {
	if l > 0 {
		v = p.validate(l, zero)
	}
	return
}

func (p enqueue_vec) Len() uint { return uint(len(p)) }
