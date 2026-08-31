// Abelian subgroup lattice enumeration
// for the lemma sweep engine.
//
// For a finite abelian group A =
// Z/d1 x Z/d2 x ... x Z/dk specified
// by invariant tuple (d1, ..., dk),
// enumerate ALL subgroups. Each subgroup
// is returned as its order and the set
// of elements (packed exponent vectors
// reduced mod invariants).
//
// The algorithm generates subgroups by
// closure: compute cyclic subgroups for
// every element, then iteratively combine
// pairs by adding generators until fixed
// point.
//
// This replaces the GAP
// ConjugacyClassesSubgroups(AbelianGroup(invs))
// call in the Sage prototype.
package tpp

import (
	"encoding/binary"
	"fmt"
	"sort"
)

// AbelianSubgroup is one subgroup of a
// finite abelian group, represented as
// an order and a set of exponent-vector
// keys.
type AbelianSubgroup struct {
	Order    int
	Elements map[uint64]struct{} // set of packed exponent vectors
}

// AbelianLattice enumerates all subgroups of Z/d1
// x ... x Z/dk. For empty invs (trivial group),
// returns a single trivial subgroup.
func AbelianLattice(invs []int) []AbelianSubgroup {
	k := len(invs)
	if k == 0 {
		return []AbelianSubgroup{
			{Order: 1, Elements: map[uint64]struct{}{0: {}}},
		}
	}

	// Enumerate all elements.
	allElts := enumElements(invs)

	// Subgroup registry keyed by canonical form.
	type subEntry struct {
		sub *AbelianSubgroup
	}
	registry := map[string]*AbelianSubgroup{}

	canonKey := func(s *AbelianSubgroup) string {
		sorted := make([]uint64, 0, len(s.Elements))
		for pk := range s.Elements {
			sorted = append(sorted, pk)
		}
		sort.Slice(sorted, func(i, j int) bool { return sorted[i] < sorted[j] })
		buf := make([]byte, 8*len(sorted))
		for i, v := range sorted {
			binary.LittleEndian.PutUint64(buf[i*8:], v)
		}
		return string(buf)
	}

	// Generate the subgroup closure from a set of generators.
	closeSub := func(gens []uint64) *AbelianSubgroup {
		members := map[uint64]struct{}{0: {}} // identity always present
		queue := []uint64{0}
		for _, g := range gens {
			if _, ok := members[g]; !ok {
				members[g] = struct{}{}
				queue = append(queue, g)
			}
		}
		for i := 0; i < len(queue); i++ {
			cur := queue[i]
			for _, g := range gens {
				sum := addPacked(cur, g, invs)
				if _, ok := members[sum]; !ok {
					members[sum] = struct{}{}
					queue = append(queue, sum)
				}
			}
		}
		return &AbelianSubgroup{Order: len(members), Elements: members}
	}

	// Register, return true if new.
	addSub := func(s *AbelianSubgroup) bool {
		ck := canonKey(s)
		if _, ok := registry[ck]; ok {
			return false
		}
		registry[ck] = s
		return true
	}

	// Phase 1: cyclic subgroup for each element.
	for _, elt := range allElts {
		pk := packVec(elt, invs)
		sub := closeSub([]uint64{pk})
		addSub(sub)
	}

	// Phase 2: combine existing subgroups
	// with additional generators until
	// stable.
	for {
		changed := false
		subs := make([]*AbelianSubgroup, 0, len(registry))
		for _, s := range registry {
			subs = append(subs, s)
		}

		for _, s1 := range subs {
			// Collect s1's elements as generator set.
			s1gens := make([]uint64, 0, len(s1.Elements))
			for pk := range s1.Elements {
				s1gens = append(s1gens, pk)
			}

			for _, elt := range allElts {
				pk := packVec(elt, invs)
				if _, ok := s1.Elements[pk]; ok {
					continue
				}
				combined := closeSub(append(s1gens, pk))
				if combined.Order > s1.Order {
					if addSub(combined) {
						changed = true
					}
				}
			}
		}
		if !changed {
			break
		}
	}

	result := make([]AbelianSubgroup, 0, len(registry))
	for _, s := range registry {
		result = append(result, *s)
	}
	return result
}

// packVec packs an exponent vector into a
// uint64 key. Each component is reduced
// mod its invariant and packed into a
// byte. Supports up to 8 components with
// invariant <= 255.
func packVec(v []int, invs []int) uint64 {
	var packed uint64
	for i, e := range v {
		r := e % invs[i]
		if r < 0 {
			r += invs[i]
		}
		packed |= uint64(r) << (uint(i) * 8)
	}
	return packed
}

// unpackVec unpacks a uint64 key back to an
// exponent vector.
func unpackVec(packed uint64, invs []int) []int {
	v := make([]int, len(invs))
	for i := range invs {
		v[i] = int((packed >> (uint(i) * 8)) & 0xFF)
	}
	return v
}

// addPacked adds two packed exponent vectors mod
// invariants, returning the packed result.
func addPacked(a, b uint64, invs []int) uint64 {
	var r uint64
	for i, d := range invs {
		shift := uint(i) * 8
		ai := int((a >> shift) & 0xFF)
		bi := int((b >> shift) & 0xFF)
		s := (ai + bi) % d
		r |= uint64(s) << shift
	}
	return r
}

// enumElements enumerates all elements
// of Z/d1 x ... x Z/dk.
func enumElements(invs []int) [][]int {
	total := 1
	for _, d := range invs {
		total *= d
	}
	result := make([][]int, 0, total)
	vec := make([]int, len(invs))
	for i := 0; i < total; i++ {
		elt := make([]int, len(invs))
		copy(elt, vec)
		result = append(result, elt)
		for j := len(invs) - 1; j >= 0; j-- {
			vec[j]++
			if vec[j] < invs[j] {
				break
			}
			vec[j] = 0
		}
	}
	return result
}

// PackExponentVec packs a raw exponent vector (from
// the export data) into the same uint64 key format
// used by AbelianLattice. The vector is reduced mod
// the corresponding invariants. Panics if len(v) >
// 8 or any invariant > 255 (packing overflow).
func PackExponentVec(v []int, invs []int) uint64 {
	if len(v) > 8 {
		panic(fmt.Sprintf("PackExponentVec: %d components exceeds uint64 packing limit of 8", len(v)))
	}
	for i, d := range invs {
		if d > 255 {
			panic(fmt.Sprintf("PackExponentVec: invariant[%d]=%d exceeds byte packing limit of 255", i, d))
		}
	}
	return packVec(v, invs)
}
