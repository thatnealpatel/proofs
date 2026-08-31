// Package tpp implements bitset-based TPP (triple product property) search
// over precomputed finite group data.
//
// Mathematical background: rho_0(G) = beta_0(G)/|G| where
// beta_0(G) = max |S||T||U| over subgroup triples (S,T,U) satisfying
// the triple product property (Murthy convention, arXiv:2602.15796
// eqs 2.5-2.6).
//
// TPP for subgroups S, T, U of G:
//
//	TPP(S,T,U)  <=>  S cap TU = {1}  AND  T cap U = {1}
//
// where TU = {tu : t in T, u in U} and 1 = identity.
//
// The brute-force O(|S||T||U|) checker verifies: for all (s,t,u) in
// SxTxU, stu = 1 implies s = t = u = 1.
//
// Search-space reduction: TPP is invariant under simultaneous
// conjugation (S,T,U) -> (S^g, T^g, U^g), so the maximum is attained
// with S fixed to a class representative; T and U range over ALL
// subgroups in their conjugacy classes.
//
// Pruning (citations in Murthy26, Neumann):
//   - Neumann Obs 3.1: |S|(|T|+|U|-1) <= |G|, all three rotations.
//   - Descending-product bucket order with early global break.
//   - Murthy26 Prop 2.19(2): in a nontrivial triple all members non-normal.
package tpp

import (
	"math/bits"
)

// Bitset represents a subset of group elements as a packed bit array.
// Element i is in the set iff bit i of Words[i/64] is set.
type Bitset struct {
	Words []uint64
}

// NewBitset allocates a bitset for a group of order n.
func NewBitset(n int) Bitset {
	return Bitset{Words: make([]uint64, (n+63)/64)}
}

// Set sets element i.
func (b *Bitset) Set(i int) {
	b.Words[i/64] |= 1 << (uint(i) % 64)
}

// Has returns true if element i is in the set.
func (b *Bitset) Has(i int) bool {
	return b.Words[i/64]&(1<<(uint(i)%64)) != 0
}

// Count returns the number of set bits (popcount).
func (b *Bitset) Count() int {
	n := 0
	for _, w := range b.Words {
		n += bits.OnesCount64(w)
	}
	return n
}

// Elements returns the sorted list of set element indices.
func (b *Bitset) Elements() []uint16 {
	out := make([]uint16, 0, b.Count())
	for wi, w := range b.Words {
		base := wi * 64
		for w != 0 {
			tz := bits.TrailingZeros64(w)
			out = append(out, uint16(base+tz))
			w &= w - 1 // clear lowest set bit
		}
	}
	return out
}

// Intersects returns true if b and other share any set bit.
func (b *Bitset) Intersects(other *Bitset) bool {
	for i := range b.Words {
		if b.Words[i]&other.Words[i] != 0 {
			return true
		}
	}
	return false
}

// IntersectsExcluding returns true if b and other share a set bit
// other than element 0 (the identity).
func (b *Bitset) IntersectsExcluding(other *Bitset) bool {
	if len(b.Words) == 0 {
		return false
	}
	// Check word 0 excluding bit 0.
	mask0 := b.Words[0] & other.Words[0] & ^uint64(1)
	if mask0 != 0 {
		return true
	}
	for i := 1; i < len(b.Words); i++ {
		if b.Words[i]&other.Words[i] != 0 {
			return true
		}
	}
	return false
}

// Group holds the precomputed multiplication table and subgroup data
// for a finite group, loaded from the Sage exporter's JSON output.
type Group struct {
	ID          string
	Description string
	Category    string
	ExpRho0     string // expected rho_0 as string rational, or ""
	N           int    // group order

	// Table[i*N+j] = index of element i * element j. Element 0 = identity.
	Table []uint16
	// Inv[i] = index of element i's inverse.
	Inv []uint16

	// Subgroups indexed by a flat subgroup ID.
	Subgroups []Subgroup
	// Classes[c] = list of subgroup indices in conjugacy class c.
	Classes [][]int
	// ClassRep[c] = index of the representative subgroup for class c.
	ClassRep []int
}

// Subgroup holds precomputed data for one subgroup.
type Subgroup struct {
	Elts     Bitset   // membership bitset
	EltList  []uint16 // sorted element indices
	Order    int
	Class    int  // conjugacy class index
	IsRep    bool // true if this is the class representative
	IsNormal bool

	// Abelianization data (Fg5: lemma sweep).
	// DerivedOrder is |H'| where H' = [H,H].
	DerivedOrder int
	// AbelianInvariants of H/H' (GAP AbelianInvariants ordering).
	AbelianInvariants []int
	// ExponentVectors maps element index -> exponent vector in H/H'.
	// The vector has len(AbelianInvariants) components.
	ExponentVectors map[uint16][]int
}

// Mul returns the product of elements a and b in the group.
func (g *Group) Mul(a, b uint16) uint16 {
	return g.Table[int(a)*g.N+int(b)]
}

// TPPSetCheck checks TPP(S,T,U) using the set characterization:
//
//	TPP(S,T,U)  <=>  S cap TU = {1}  AND  T cap U = {1}
//
// This is O(|T||U|) to build TU plus O(nWords) for the intersection tests.
func (g *Group) TPPSetCheck(s, t, u *Subgroup) bool {
	// Fast check: T cap U = {1}.
	if t.Elts.IntersectsExcluding(&u.Elts) {
		return false
	}

	// Build TU = {Mul(ti, uj) : ti in T, uj in U} as a bitset.
	tu := NewBitset(g.N)
	for _, ti := range t.EltList {
		row := int(ti) * g.N
		for _, uj := range u.EltList {
			tu.Set(int(g.Table[row+int(uj)]))
		}
	}

	// Check S cap TU = {1}: no non-identity element in both.
	return !s.Elts.IntersectsExcluding(&tu)
}

// TPPBruteCheck checks TPP(S,T,U) by brute force:
// for all (s,t,u) in SxTxU, stu = 1 => s = t = u = 1.
// Returns true iff TPP holds.
func (g *Group) TPPBruteCheck(s, t, u *Subgroup) bool {
	for _, si := range s.EltList {
		for _, ti := range t.EltList {
			st := g.Mul(si, ti)
			for _, ui := range u.EltList {
				if g.Mul(st, ui) == 0 { // identity = element 0
					if si != 0 || ti != 0 || ui != 0 {
						return false
					}
				}
			}
		}
	}
	return true
}

// BucketTriple holds the order-triple for a search bucket.
type BucketTriple struct {
	Product    int // oS * oT * oU
	OS, OT, OU int
}

// Result holds the search result for a single target group.
type Result struct {
	ID              string  `json:"id"`
	Description     string  `json:"description"`
	Order           int     `json:"order"`
	Rho0Exact       string  `json:"rho0_exact"`
	Rho0Float       float64 `json:"rho0_float"`
	AchievingTriple [3]int  `json:"achieving_triple_type"`
	ExpectedRho0    string  `json:"expected_rho0"`
	Category        string  `json:"category"`
	Stats           Stats   `json:"search_stats"`
	RuntimeSeconds  float64 `json:"runtime_seconds"`
	TimedOut        bool    `json:"timed_out"`
	Semantics       string  `json:"semantics"` // "exact" or "lower_bound"
	Error           string  `json:"error,omitempty"`
}

// Stats holds search statistics.
type Stats struct {
	NConjClasses   int   `json:"n_conjugacy_classes"`
	NSubgroups     int   `json:"n_subgroups"`
	NTriplesTested int64 `json:"n_triples_tested"`
	NPrunedNeumann int64 `json:"n_pruned_neumann"`
	NPrunedNormal  int64 `json:"n_pruned_normal"`
	NTPPChecks     int64 `json:"n_tpp_checks"`
	NCandidates    int64 `json:"n_candidates"`
}

// Rational represents a non-negative rational number p/q in lowest terms.
type Rational struct {
	P, Q int64
}

func gcd(a, b int64) int64 {
	for b != 0 {
		a, b = b, a%b
	}
	if a < 0 {
		return -a
	}
	return a
}

// NewRational creates a rational p/q in lowest terms.
func NewRational(p, q int64) Rational {
	if q == 0 {
		panic("zero denominator")
	}
	g := gcd(p, q)
	return Rational{P: p / g, Q: q / g}
}

// String returns the rational as "p/q" or "p" if q=1.
func (r Rational) String() string {
	if r.Q == 1 {
		return itoa(r.P)
	}
	return itoa(r.P) + "/" + itoa(r.Q)
}

// Float64 returns the floating-point value.
func (r Rational) Float64() float64 {
	return float64(r.P) / float64(r.Q)
}

// Greater returns true if r > other.
func (r Rational) Greater(other Rational) bool {
	return r.P*other.Q > other.P*r.Q
}

func itoa(n int64) string {
	if n == 0 {
		return "0"
	}
	neg := false
	if n < 0 {
		neg = true
		n = -n
	}
	buf := [20]byte{}
	i := len(buf)
	for n > 0 {
		i--
		buf[i] = byte('0' + n%10)
		n /= 10
	}
	if neg {
		i--
		buf[i] = '-'
	}
	return string(buf[i:])
}
