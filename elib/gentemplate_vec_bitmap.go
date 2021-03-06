// autogenerated: do not edit!
// generated from gentemplate [gentemplate -d Package=elib -id Bitmap -d VecType=BitmapVec -d Type=Bitmap vec.tmpl]

// Copyright 2016 Platina Systems, Inc. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package elib

type BitmapVec []Bitmap

func (p *BitmapVec) Resize(n uint) {
	c := Index(cap(*p))
	l := Index(len(*p)) + Index(n)
	if l > c {
		c = NextResizeCap(l)
		q := make([]Bitmap, l, c)
		copy(q, *p)
		*p = q
	}
	*p = (*p)[:l]
}

func (p *BitmapVec) validate(new_len uint, zero Bitmap) *Bitmap {
	c := Index(cap(*p))
	lʹ := Index(len(*p))
	l := Index(new_len)
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

func (p *BitmapVec) validateSlowPath(zero Bitmap, c, l, lʹ Index) *Bitmap {
	if l > c {
		cNext := NextResizeCap(l)
		q := make([]Bitmap, cNext, cNext)
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

func (p *BitmapVec) Validate(i uint) *Bitmap {
	var zero Bitmap
	return p.validate(i+1, zero)
}

func (p *BitmapVec) ValidateInit(i uint, zero Bitmap) *Bitmap {
	return p.validate(i+1, zero)
}

func (p *BitmapVec) ValidateLen(l uint) (v *Bitmap) {
	if l > 0 {
		var zero Bitmap
		v = p.validate(l, zero)
	}
	return
}

func (p *BitmapVec) ValidateLenInit(l uint, zero Bitmap) (v *Bitmap) {
	if l > 0 {
		v = p.validate(l, zero)
	}
	return
}

func (p BitmapVec) Len() uint { return uint(len(p)) }
