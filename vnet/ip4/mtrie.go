// Copyright 2016 Platina Systems, Inc. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ip4

import (
	"github.com/platinasystems/go/elib"
	"github.com/platinasystems/go/vnet/ip"
)

type leaf uint32

const (
	empty_leaf     leaf = leaf(1 + 2*ip.AdjMiss)
	root_ply_index uint = 0
)

func (l leaf) isTerminal() bool    { return l&1 != 0 }
func (l leaf) ResultIndex() ip.Adj { return ip.Adj(l >> 1) }
func setResult(i ip.Adj) leaf      { return leaf(1 + 2*i) }
func (l *leaf) setResult(i ip.Adj) { *l = setResult(i) }
func (l leaf) isPly() bool         { return !l.isTerminal() }
func (l leaf) plyIndex() uint      { return uint(l >> 1) }
func setPlyIndex(i uint) leaf      { return leaf(0 + 2*i) }
func (l *leaf) setPlyIndex(i uint) { *l = setPlyIndex(i) }

type ply struct {
	// Ply has 2^log2_n_leafs leaves.
	log2_n_leafs uint8

	// True when ply is free in pool of size log2_n_leafs.
	isFree bool

	leaves []leaf

	// Prefix length of leaves.
	lens []uint8

	// Number of non-empty leaves.
	n_non_empty int

	pool_index uint
}

//go:generate gentemplate -d Package=ip4 -id ply -d VecType=ply_vec -d Type=ply -d Data=plys github.com/platinasystems/go/elib/vec.tmpl

type mtrie struct {
	// Vector of plies.  Index zero is root ply.
	plys ply_vec

	ply_pool_by_log2_n_leafs []elib.Pool

	// Log2 size of each ply.  e.g. 8-8-8-8 for ip4 lookup in 4 strides.
	log2_n_leafs []uint8

	// Special case leaf for default route 0.0.0.0/0.
	// This is to avoid having to paint default leaf in all plys of trie.
	default_leaf leaf
}

func (m *mtrie) LookupStep(l leaf, key uint) (lʹ leaf) {
	pi := uint(0)
	wasTerm := l.isTerminal()
	if !wasTerm {
		pi = l.plyIndex()
	}
	lʹ = m.plys[pi].leaves[key]
	if wasTerm {
		lʹ = l
	}
	return
}

func (p *ply) init(l leaf, n, log2_n_leaf uint8) {
	p.n_non_empty = 0
	n_leaf := 1 << log2_n_leaf
	if l != empty_leaf {
		p.n_non_empty = n_leaf
	}
	i := 0
	if n_leaf < 4 {
		panic("n_leafs should be power of 2 >= 4")
	}
	n_left := n_leaf
	for n_left >= 4 {
		p.lens[i+0] = n
		p.lens[i+1] = n
		p.lens[i+2] = n
		p.lens[i+3] = n
		p.leaves[i+0] = l
		p.leaves[i+1] = l
		p.leaves[i+2] = l
		p.leaves[i+3] = l
		n_left -= 4
		i += 4
	}
}

func (m *mtrie) newPly(l leaf, n, log2_n_leaf uint8) (lʹ leaf, ply *ply) {
	pi := m.ply_pool_by_log2_n_leafs[log2_n_leaf].GetIndex(m.plys.Len())
	m.plys.Validate(pi)
	ply = &m.plys[pi]
	ply.pool_index = pi
	ply.log2_n_leafs = log2_n_leaf
	ply.init(l, n, log2_n_leaf)
	lʹ = setPlyIndex(pi)
	return
}

func (m *mtrie) plyForLeaf(l leaf) *ply { return &m.plys[l.plyIndex()] }

func (m *mtrie) freePly(p *ply) {
	isRoot := p.pool_index == 0
	for _, l := range p.leaves {
		if !l.isTerminal() {
			m.freePly(m.plyForLeaf(l))
		}
	}
	if isRoot {
		p.init(empty_leaf, 0, m.log2_n_leafs[0])
	} else {
		p.isFree = true
		m.ply_pool_by_log2_n_leafs[p.log2_n_leafs].PutIndex(p.pool_index)
	}
}

func (m *mtrie) Free() { m.freePly(&m.plys[0]) }

func (m *mtrie) lookup(dst elib.Bitmap) ip.Adj {
	p := &m.plys[0]
	dst_offset := uint(0)
	for i := range m.log2_n_leafs {
		n_bits := uint(m.log2_n_leafs[i])
		key := uint(dst.GetMultiple(dst_offset, n_bits))
		dst_offset += n_bits
		l := p.leaves[key]
		if l.isTerminal() {
			return l.ResultIndex()
		}
		p = m.plyForLeaf(l)
	}
	panic("no terminal leaf found")
}

func (m *mtrie) setPlyWithMoreSpecificLeaf(p *ply, l leaf, n uint8) {
	for i, pl := range p.leaves {
		if !pl.isTerminal() {
			m.setPlyWithMoreSpecificLeaf(m.plyForLeaf(pl), l, n)
		} else if n >= p.lens[i] {
			p.leaves[i] = l
			p.lens[i] = n
			if pl != empty_leaf {
				p.n_non_empty++
			}
		}
	}
}

func (p *ply) replaceLeaf(new, old leaf, i uint8) {
	p.leaves[i] = new
	if old != empty_leaf {
		p.n_non_empty++
	}
}

type addDelLeaf struct {
	key    Address
	keyLen uint8
	result ip.Adj
}

func (s *addDelLeaf) setLeafHelper(m *mtrie, oldPlyIndex, keyByteIndex uint) {
	nBits := int(s.keyLen) - 8*int(keyByteIndex+1)
	k := s.key[keyByteIndex]
	oldPly := &m.plys[oldPlyIndex]

	// Number of bits next plies <= 0 => insert leaves this ply.
	if nBits <= 0 {
		nBits = -nBits
		for i := k; i < k+1<<uint(nBits); i++ {
			oldLeaf := oldPly.leaves[i]
			oldTerm := oldLeaf.isTerminal()

			// Is leaf to be inserted more specific?
			if s.keyLen >= oldPly.lens[i] {
				newLeaf := setResult(s.result)
				if oldTerm {
					oldPly.lens[i] = s.keyLen
					oldPly.replaceLeaf(newLeaf, oldLeaf, i)
				} else {
					// Existing leaf points to another ply.
					// We need to place new_leaf into all more specific slots.
					newPly := m.plyForLeaf(oldLeaf)
					m.setPlyWithMoreSpecificLeaf(newPly, newLeaf, s.keyLen)
				}
			} else if !oldTerm {
				s.setLeafHelper(m, oldLeaf.plyIndex(), keyByteIndex+1)
			}
		}
	} else {
		oldLeaf := oldPly.leaves[k]
		oldTerm := oldLeaf.isTerminal()
		var newPly *ply
		if !oldTerm {
			newPly = m.plyForLeaf(oldLeaf)
		} else {
			var newLeaf leaf
			newLeaf, newPly = m.newPly(oldLeaf, oldPly.lens[k], 99) // fixme
			// Refetch since newPly may move pool.
			oldPly = &m.plys[oldPlyIndex]
			oldPly.leaves[k] = newLeaf
			oldPly.lens[k] = 0
			if oldLeaf != empty_leaf {
				oldPly.n_non_empty--
			}
			// Account for the ply we just created.
			oldPly.n_non_empty++
		}
		s.setLeafHelper(m, newPly.pool_index, keyByteIndex+1)
	}
}

func (s *addDelLeaf) unsetLeafHelper(m *mtrie, old_ply_index, keyByteIndex uint) (old_ply_was_deleted bool) {
	k := s.key[keyByteIndex]
	nBits := int(s.keyLen) - 8*int(keyByteIndex+1)
	if nBits <= 0 {
		nBits = -nBits
		k &^= 1<<uint(nBits) - 1
		if nBits > 8 {
			nBits = 8
		}
	}
	del_leaf := setResult(s.result)
	old_ply := &m.plys[old_ply_index]
	for i := k; i < k+1<<uint(nBits); i++ {
		old_leaf := old_ply.leaves[i]
		old_term := old_leaf.isTerminal()
		if old_leaf == del_leaf ||
			(!old_term && s.unsetLeafHelper(m, old_leaf.plyIndex(), keyByteIndex+1)) {
			old_ply.leaves[i] = empty_leaf
			old_ply.lens[i] = 0
			old_ply.n_non_empty--
			old_ply_was_deleted = old_ply.n_non_empty == 0 && keyByteIndex > 0
			if old_ply_was_deleted {
				m.ply_pool_by_log2_n_leafs[old_ply.log2_n_leafs].PutIndex(old_ply.pool_index)
				// Nothing more to do.
				break
			}
		}
	}

	return
}

func (s *addDelLeaf) set(m *mtrie)        { s.setLeafHelper(m, root_ply_index, 0) }
func (s *addDelLeaf) unset(m *mtrie) bool { return s.unsetLeafHelper(m, root_ply_index, 0) }

func (l *leaf) remap(from, to ip.Adj) (remapEmpty int) {
	if l.isTerminal() {
		if adj := l.ResultIndex(); adj == from {
			if to == ip.AdjNil {
				remapEmpty = 1
				*l = empty_leaf
			} else {
				l.setResult(to)
			}
		}
	}
	return
}

func (p *ply) remap(from, to ip.Adj) {
	nRemapEmpty := 0
	for i := range p.leaves {
		nRemapEmpty += p.leaves[i].remap(from, to)
	}
	p.n_non_empty -= nRemapEmpty
}

func (t *mtrie) remapAdjacency(from, to ip.Adj) {
	for i := uint(0); i < t.plys.Len(); i++ {
		p := &t.plys[i]
		if !p.isFree {
			p.remap(from, to)
		}
	}
}

func (m *mtrie) is_initialized() bool { return len(m.log2_n_leafs) == 0 }

func (m *mtrie) init(log2_n_leafs []uint8) {
	m.default_leaf = empty_leaf
	m.log2_n_leafs = log2_n_leafs

	max_l := uint8(0)
	for _, l := range m.log2_n_leafs {
		if l > max_l {
			max_l = l
		}
	}
	m.ply_pool_by_log2_n_leafs = make([]elib.Pool, max_l+1)

	// Make root ply.
	l, _ := m.newPly(empty_leaf, 0, m.log2_n_leafs[0])
	if l.plyIndex() != 0 {
		panic("root ply must be index 0")
	}
}
