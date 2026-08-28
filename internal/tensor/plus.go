package tensor

import (
	"fmt"
	"slices"

	"patel.codes/proofs/internal/ring"
)

func NewPlusReplacement(scheme Scheme, p, q int) (Replacement, error) {
	if err := scheme.validateStructure(); err != nil {
		return Replacement{}, fmt.Errorf("Plus source scheme: %w", err)
	}
	if scheme.Ring() != ring.Z2 {
		return Replacement{}, fmt.Errorf("Plus replacement requires ring Z2, got %d", scheme.Ring())
	}
	if p < 0 || p >= scheme.TermCount() {
		return Replacement{}, fmt.Errorf("Plus source slot p is out of range: %d for %d terms", p, scheme.TermCount())
	}
	if q < 0 || q >= scheme.TermCount() {
		return Replacement{}, fmt.Errorf("Plus source slot q is out of range: %d for %d terms", q, scheme.TermCount())
	}
	if p == q {
		return Replacement{}, fmt.Errorf("Plus source slots must be distinct, got %d twice", p)
	}

	first := scheme.Term(p)
	second := scheme.Term(q)
	a1, b1, c1 := first.Factor(0), first.Factor(1), first.Factor(2)
	a2, b2, c2 := second.Factor(0), second.Factor(1), second.Factor(2)
	for factor, pair := range [][2]Matrix{{a1, a2}, {b1, b2}, {c1, c2}} {
		if slices.Equal(pair[0].Entries(), pair[1].Entries()) {
			return Replacement{}, fmt.Errorf("Plus source matrices must differ at factor %d", factor)
		}
	}

	b1b2, err := addMatrices(b1, b2)
	if err != nil {
		return Replacement{}, fmt.Errorf("Plus b1+b2: %w", err)
	}
	a1a2, err := addMatrices(a1, a2)
	if err != nil {
		return Replacement{}, fmt.Errorf("Plus a1+a2: %w", err)
	}
	c1c2, err := addMatrices(c1, c2)
	if err != nil {
		return Replacement{}, fmt.Errorf("Plus c1+c2: %w", err)
	}

	inserted := make([]RankOneTerm, 3)
	inserted[0], err = NewRankOneTerm(a1, b1b2, c1)
	if err != nil {
		return Replacement{}, fmt.Errorf("Plus inserted term 0: %w", err)
	}
	inserted[1], err = NewRankOneTerm(a1a2, b2, c2)
	if err != nil {
		return Replacement{}, fmt.Errorf("Plus inserted term 1: %w", err)
	}
	inserted[2], err = NewRankOneTerm(a1, b2, c1c2)
	if err != nil {
		return Replacement{}, fmt.Errorf("Plus inserted term 2: %w", err)
	}

	removed := []int{p, q}
	if removed[0] > removed[1] {
		removed[0], removed[1] = removed[1], removed[0]
	}
	replacement, err := NewReplacement(removed, inserted)
	if err != nil {
		return Replacement{}, fmt.Errorf("construct Plus replacement: %w", err)
	}
	if err := ValidateReplacement(scheme, replacement); err != nil {
		return Replacement{}, fmt.Errorf("validate Plus replacement: %w", err)
	}
	return replacement, nil
}

func addMatrices(first, second Matrix) (Matrix, error) {
	return addScaledMatrix(first, 1, second)
}
