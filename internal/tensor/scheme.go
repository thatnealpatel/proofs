package tensor

import (
	"fmt"

	"patel.codes/proofs/internal/ring"
)

type RankOneTerm struct {
	factors [3]Matrix
}

func NewRankOneTerm(first, second, third Matrix) (RankOneTerm, error) {
	term := RankOneTerm{factors: [3]Matrix{first.clone(), second.clone(), third.clone()}}
	if err := term.validateStructure(); err != nil {
		return RankOneTerm{}, err
	}
	return term, nil
}

func (t RankOneTerm) validateStructure() error {
	for i, factor := range t.factors {
		size, err := matrixSize(factor.rows, factor.columns)
		if err != nil || len(factor.entries) != size {
			return fmt.Errorf("factor %d is not a valid matrix", i)
		}
	}
	if t.factors[0].ring != t.factors[1].ring || t.factors[0].ring != t.factors[2].ring {
		return fmt.Errorf("term factors use different rings")
	}
	if t.factors[0].columns != t.factors[1].rows ||
		t.factors[1].columns != t.factors[2].rows ||
		t.factors[2].columns != t.factors[0].rows {
		return fmt.Errorf(
			"term factor dimensions %dx%d, %dx%d, %dx%d are not cyclic",
			t.factors[0].rows,
			t.factors[0].columns,
			t.factors[1].rows,
			t.factors[1].columns,
			t.factors[2].rows,
			t.factors[2].columns,
		)
	}
	return nil
}

func (t RankOneTerm) Factor(index int) Matrix {
	if index < 0 || index >= len(t.factors) {
		panic("factor index out of range")
	}
	return t.factors[index].clone()
}

func (t RankOneTerm) Factors() []Matrix {
	factors := make([]Matrix, len(t.factors))
	for i := range t.factors {
		factors[i] = t.factors[i].clone()
	}
	return factors
}

func (t RankOneTerm) clone() RankOneTerm {
	for i := range t.factors {
		t.factors[i] = t.factors[i].clone()
	}
	return t
}

type Scheme struct {
	ring       ring.Ring
	dimensions [3]int
	terms      []RankOneTerm
}

func NewScheme(terms []RankOneTerm) (Scheme, error) {
	if len(terms) == 0 {
		return Scheme{}, fmt.Errorf("scheme must contain at least one term")
	}
	first := terms[0]
	return newScheme(
		first.factors[0].ring,
		[3]int{first.factors[0].rows, first.factors[1].rows, first.factors[2].rows},
		terms,
	)
}

func NewEmptyScheme(r ring.Ring, dimensions [3]int) (Scheme, error) {
	return newScheme(r, dimensions, nil)
}

func newScheme(r ring.Ring, dimensions [3]int, terms []RankOneTerm) (Scheme, error) {
	if !r.Valid() {
		return Scheme{}, fmt.Errorf("unsupported ring %d", r)
	}
	for factor := range 3 {
		if _, err := matrixSize(dimensions[factor], dimensions[(factor+1)%3]); err != nil {
			return Scheme{}, fmt.Errorf("scheme factor %d dimensions: %w", factor, err)
		}
	}
	copied := make([]RankOneTerm, len(terms))
	for i, term := range terms {
		if err := term.validateStructure(); err != nil {
			return Scheme{}, fmt.Errorf("term %d: %w", i, err)
		}
		if term.factors[0].ring != r || term.factors[1].ring != r || term.factors[2].ring != r {
			return Scheme{}, fmt.Errorf("term %d uses a different ring", i)
		}
		if term.factors[0].rows != dimensions[0] || term.factors[0].columns != dimensions[1] ||
			term.factors[1].rows != dimensions[1] || term.factors[1].columns != dimensions[2] ||
			term.factors[2].rows != dimensions[2] || term.factors[2].columns != dimensions[0] {
			return Scheme{}, fmt.Errorf("term %d has different factor dimensions", i)
		}
		copied[i] = term.clone()
	}
	return Scheme{ring: r, dimensions: dimensions, terms: copied}, nil
}

func (s Scheme) Ring() ring.Ring {
	return s.ring
}

func (s Scheme) Dimensions() [3]int {
	return s.dimensions
}

func (s Scheme) TermCount() int {
	return len(s.terms)
}

func (s Scheme) Term(index int) RankOneTerm {
	if index < 0 || index >= len(s.terms) {
		panic("term index out of range")
	}
	return s.terms[index].clone()
}

func (s Scheme) Terms() []RankOneTerm {
	terms := make([]RankOneTerm, len(s.terms))
	for i := range s.terms {
		terms[i] = s.terms[i].clone()
	}
	return terms
}
