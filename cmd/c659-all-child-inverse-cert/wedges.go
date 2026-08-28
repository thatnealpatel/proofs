package main

type colorLeg struct {
	color int
	leg   int
}

type typedWedge struct {
	center   int
	a, b     colorLeg
	residual int
	pass     bool
}

func enumerateTypedWedges(terms []triple, observe func(int, int, triple) error) ([]typedWedge, error) {
	buckets := [3]map[uint16][]int{}
	for mode := range 3 {
		buckets[mode] = make(map[uint16][]int)
	}
	for color, term := range terms {
		for mode := range 3 {
			buckets[mode][term[mode]] = append(buckets[mode][term[mode]], color)
			if err := observe(mode, color, term); err != nil {
				return nil, err
			}
		}
	}
	result := make([]typedWedge, 0)
	for center, centerTerm := range terms {
		legsByColor := make([][]int, len(terms))
		for mode := range 3 {
			for _, color := range buckets[mode][centerTerm[mode]] {
				if color != center {
					legsByColor[color] = append(legsByColor[color], mode)
				}
			}
		}
		colors := make([]colorLeg, 0)
		for color, legs := range legsByColor {
			if len(legs) == 1 {
				colors = append(colors, colorLeg{color, legs[0]})
			}
		}
		for ai := range colors {
			for bi := ai + 1; bi < len(colors); bi++ {
				a, b := colors[ai], colors[bi]
				if a.leg == b.leg {
					continue
				}
				residual := 3 - a.leg - b.leg
				result = append(result, typedWedge{center, a, b, residual, centerTerm[residual] == terms[a.color][residual]^terms[b.color][residual]})
			}
		}
	}
	return result, nil
}
