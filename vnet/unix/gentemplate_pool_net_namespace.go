// autogenerated: do not edit!
// generated from gentemplate [gentemplate -d Package=unix -id net_namespace -d PoolType=net_namespace_pool -d Type=*net_namespace -d Data=entries github.com/platinasystems/go/elib/pool.tmpl]

// Copyright 2016 Platina Systems, Inc. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package unix

import (
	"github.com/platinasystems/go/elib"
)

type net_namespace_pool struct {
	elib.Pool
	entries []*net_namespace
}

func (p *net_namespace_pool) GetIndex() (i uint) {
	l := uint(len(p.entries))
	i = p.Pool.GetIndex(l)
	if i >= l {
		p.Validate(i)
	}
	return i
}

func (p *net_namespace_pool) PutIndex(i uint) (ok bool) {
	return p.Pool.PutIndex(i)
}

func (p *net_namespace_pool) IsFree(i uint) (v bool) {
	v = i >= uint(len(p.entries))
	if !v {
		v = p.Pool.IsFree(i)
	}
	return
}

func (p *net_namespace_pool) Resize(n uint) {
	c := elib.Index(cap(p.entries))
	l := elib.Index(len(p.entries) + int(n))
	if l > c {
		c = elib.NextResizeCap(l)
		q := make([]*net_namespace, l, c)
		copy(q, p.entries)
		p.entries = q
	}
	p.entries = p.entries[:l]
}

func (p *net_namespace_pool) Validate(i uint) {
	c := elib.Index(cap(p.entries))
	l := elib.Index(i) + 1
	if l > c {
		c = elib.NextResizeCap(l)
		q := make([]*net_namespace, l, c)
		copy(q, p.entries)
		p.entries = q
	}
	if l > elib.Index(len(p.entries)) {
		p.entries = p.entries[:l]
	}
}

func (p *net_namespace_pool) Elts() uint {
	return uint(len(p.entries)) - p.FreeLen()
}

func (p *net_namespace_pool) Len() uint {
	return uint(len(p.entries))
}

func (p *net_namespace_pool) Foreach(f func(x *net_namespace)) {
	for i := range p.entries {
		if !p.Pool.IsFree(uint(i)) {
			f(p.entries[i])
		}
	}
}

func (p *net_namespace_pool) ForeachIndex(f func(i uint)) {
	for i := range p.entries {
		if !p.Pool.IsFree(uint(i)) {
			f(uint(i))
		}
	}
}
