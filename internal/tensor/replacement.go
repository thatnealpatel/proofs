package tensor

import (
	"fmt"

	"patel.codes/proofs/internal/ring"
)

type Replacement struct {
	removedSlots  []int
	insertedTerms []RankOneTerm
}

func NewReplacement(removedSlots []int, insertedTerms []RankOneTerm) (Replacement, error) {
	replacement := Replacement{
		removedSlots:  append([]int(nil), removedSlots...),
		insertedTerms: make([]RankOneTerm, len(insertedTerms)),
	}
	for i := range insertedTerms {
		replacement.insertedTerms[i] = insertedTerms[i].clone()
	}
	if err := replacement.validateStructure(); err != nil {
		return Replacement{}, err
	}
	return replacement, nil
}

func (r Replacement) RemovedSlots() []int {
	return append([]int(nil), r.removedSlots...)
}

func (r Replacement) InsertedTerms() []RankOneTerm {
	terms := make([]RankOneTerm, len(r.insertedTerms))
	for i := range r.insertedTerms {
		terms[i] = r.insertedTerms[i].clone()
	}
	return terms
}

func ValidateReplacement(scheme Scheme, replacement Replacement) error {
	if err := scheme.validateStructure(); err != nil {
		return err
	}
	if err := replacement.validateStructure(); err != nil {
		return err
	}
	for i, slot := range replacement.removedSlots {
		if slot >= len(scheme.terms) {
			return fmt.Errorf("removed slot %d is %d, but scheme has %d terms", i, slot, len(scheme.terms))
		}
	}
	for i, term := range replacement.insertedTerms {
		if err := validateTermFitsScheme(term, scheme); err != nil {
			return fmt.Errorf("inserted term %d: %w", i, err)
		}
	}
	factorSizes := [3]int{}
	for factor := range 3 {
		size, err := matrixSize(scheme.dimensions[factor], scheme.dimensions[(factor+1)%3])
		if err != nil {
			return fmt.Errorf("scheme factor %d dimensions: %w", factor, err)
		}
		factorSizes[factor] = size
	}
	for first := range factorSizes[0] {
		for second := range factorSizes[1] {
			for third := range factorSizes[2] {
				removed := 0
				for _, slot := range replacement.removedSlots {
					removed = scheme.ring.Add(removed, rankOneCoefficient(scheme.ring, scheme.terms[slot], first, second, third))
				}
				inserted := 0
				for _, term := range replacement.insertedTerms {
					inserted = scheme.ring.Add(inserted, rankOneCoefficient(scheme.ring, term, first, second, third))
				}
				if removed != inserted {
					return fmt.Errorf(
						"replacement tensor sums differ at coefficient (%d,%d,%d): removed sum %d, inserted sum %d",
						first,
						second,
						third,
						removed,
						inserted,
					)
				}
			}
		}
	}
	return nil
}

func ApplyReplacement(scheme Scheme, replacement Replacement) (Scheme, error) {
	if err := ValidateReplacement(scheme, replacement); err != nil {
		return Scheme{}, err
	}
	survivorCount := len(scheme.terms) - len(replacement.removedSlots)
	maxInt := int(^uint(0) >> 1)
	if len(replacement.insertedTerms) > maxInt-survivorCount {
		return Scheme{}, fmt.Errorf("replacement result length overflows int")
	}
	resultCount := survivorCount + len(replacement.insertedTerms)
	terms := make([]RankOneTerm, 0, resultCount)
	removed := 0
	for slot, term := range scheme.terms {
		if removed < len(replacement.removedSlots) && slot == replacement.removedSlots[removed] {
			removed++
			continue
		}
		terms = append(terms, term)
	}
	terms = append(terms, replacement.insertedTerms...)
	return newScheme(scheme.ring, scheme.dimensions, terms)
}

func (r Replacement) validateStructure() error {
	for i, slot := range r.removedSlots {
		if slot < 0 {
			return fmt.Errorf("removed slot %d is negative: %d", i, slot)
		}
		if i > 0 && slot <= r.removedSlots[i-1] {
			return fmt.Errorf("removed slots are not strictly increasing at index %d", i)
		}
	}
	for i, term := range r.insertedTerms {
		if err := term.validateStructure(); err != nil {
			return fmt.Errorf("inserted term %d: %w", i, err)
		}
	}
	return nil
}

func validateTermFitsScheme(term RankOneTerm, scheme Scheme) error {
	for factor := range 3 {
		matrix := term.factors[factor]
		if matrix.ring != scheme.ring {
			return fmt.Errorf("factor %d uses ring %d, want %d", factor, matrix.ring, scheme.ring)
		}
		wantRows := scheme.dimensions[factor]
		wantColumns := scheme.dimensions[(factor+1)%3]
		if matrix.rows != wantRows || matrix.columns != wantColumns {
			return fmt.Errorf(
				"factor %d dimensions are %dx%d, want %dx%d",
				factor,
				matrix.rows,
				matrix.columns,
				wantRows,
				wantColumns,
			)
		}
	}
	return nil
}

func rankOneCoefficient(r ring.Ring, term RankOneTerm, first, second, third int) int {
	return r.Mul(
		r.Mul(term.factors[0].entries[first], term.factors[1].entries[second]),
		term.factors[2].entries[third],
	)
}
