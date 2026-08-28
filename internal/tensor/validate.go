package tensor

import "fmt"

func ValidateBrent(scheme Scheme) error {
	if err := scheme.validateStructure(); err != nil {
		return err
	}
	m, n, p := scheme.dimensions[0], scheme.dimensions[1], scheme.dimensions[2]
	for i := range m {
		for j := range n {
			for secondJ := range n {
				for k := range p {
					for thirdK := range p {
						for thirdI := range m {
							total := 0
							for _, term := range scheme.terms {
								coefficient := scheme.ring.Mul(
									scheme.ring.Mul(term.factors[0].At(i, j), term.factors[1].At(secondJ, k)),
									term.factors[2].At(thirdK, thirdI),
								)
								total = scheme.ring.Add(total, coefficient)
							}
							want := 0
							if i == thirdI && j == secondJ && k == thirdK {
								want = 1
							}
							if total != want {
								return fmt.Errorf(
									"Brent equation (%d,%d,%d,%d,%d,%d) is %d, want %d",
									i,
									j,
									secondJ,
									k,
									thirdK,
									thirdI,
									total,
									want,
								)
							}
						}
					}
				}
			}
		}
	}
	return nil
}

func ValidateNonzeroTerms(scheme Scheme) error {
	if err := scheme.validateStructure(); err != nil {
		return err
	}
	for termIndex, term := range scheme.terms {
		for factorIndex, factor := range term.factors {
			nonzero := false
			for _, entry := range factor.entries {
				if entry != 0 {
					nonzero = true
					break
				}
			}
			if !nonzero {
				return fmt.Errorf("term %d has zero factor %d", termIndex, factorIndex)
			}
		}
	}
	return nil
}

func ValidateDistinctTensors(scheme Scheme) error {
	if err := scheme.validateStructure(); err != nil {
		return err
	}
	for first := range scheme.terms {
		for second := first + 1; second < len(scheme.terms); second++ {
			if equalRankOneTensors(scheme, first, second) {
				return fmt.Errorf("terms %d and %d define the same rank-one tensor", first, second)
			}
		}
	}
	return nil
}

func equalRankOneTensors(scheme Scheme, first, second int) bool {
	left := scheme.terms[first]
	right := scheme.terms[second]
	for i := range left.factors[0].entries {
		for j := range left.factors[1].entries {
			for k := range left.factors[2].entries {
				leftEntry := scheme.ring.Mul(
					scheme.ring.Mul(left.factors[0].entries[i], left.factors[1].entries[j]),
					left.factors[2].entries[k],
				)
				rightEntry := scheme.ring.Mul(
					scheme.ring.Mul(right.factors[0].entries[i], right.factors[1].entries[j]),
					right.factors[2].entries[k],
				)
				if leftEntry != rightEntry {
					return false
				}
			}
		}
	}
	return true
}

func (s Scheme) validateStructure() error {
	if !s.ring.Valid() {
		return fmt.Errorf("unsupported ring %d", s.ring)
	}
	for factor := range 3 {
		if _, err := matrixSize(s.dimensions[factor], s.dimensions[(factor+1)%3]); err != nil {
			return fmt.Errorf("scheme factor %d dimensions: %w", factor, err)
		}
	}
	for i, term := range s.terms {
		if term.factors[0].ring != s.ring || term.factors[1].ring != s.ring || term.factors[2].ring != s.ring {
			return fmt.Errorf("term %d uses a different ring", i)
		}
		for factor := range 3 {
			matrix := term.factors[factor]
			if matrix.rows != s.dimensions[factor] || matrix.columns != s.dimensions[(factor+1)%3] {
				return fmt.Errorf("term %d factor %d has invalid dimensions", i, factor)
			}
			size, err := matrixSize(matrix.rows, matrix.columns)
			if err != nil || len(matrix.entries) != size {
				return fmt.Errorf("term %d factor %d has invalid storage", i, factor)
			}
		}
	}
	return nil
}
