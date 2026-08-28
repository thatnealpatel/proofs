package main

import (
	"fmt"
	"math/bits"
)

var complementaryModeOrder = [3][2]int{{1, 2}, {0, 2}, {0, 1}}

func complementaryRows(terms []wordTriple, slots []int, sharedMode int) ([]uint16, [2]int, error) {
	if sharedMode < 0 || sharedMode >= 3 {
		return nil, [2]int{}, fmt.Errorf("shared mode %d is out of range", sharedMode)
	}
	modes := complementaryModeOrder[sharedMode]
	rows := make([]uint16, 16)
	for _, slot := range slots {
		if slot < 0 || slot >= len(terms) {
			return nil, [2]int{}, fmt.Errorf("slot %d is out of range for %d terms", slot, len(terms))
		}
		left := terms[slot][modes[0]]
		right := terms[slot][modes[1]]
		for row := range 16 {
			if left&(uint16(1)<<row) != 0 {
				rows[row] ^= right
			}
		}
	}
	return rows, modes, nil
}

func eliminateRows(rows []uint16) eliminationCertificate {
	basisByPivot := [16]uint16{}
	pivots := make([]int, 0, 16)
	basisRows := make([]uint16, 0, 16)
	residuals := make([]uint16, len(rows))
	for index, row := range rows {
		residual := row
		for residual != 0 {
			pivot := bits.Len16(residual) - 1
			if basisByPivot[pivot] != 0 {
				residual ^= basisByPivot[pivot]
				continue
			}
			basisByPivot[pivot] = residual
			pivots = append(pivots, pivot)
			basisRows = append(basisRows, residual)
			break
		}
		residuals[index] = residual
	}
	return eliminationCertificate{
		Algorithm:      "gf2_input_order_highest_set_bit_xor_v1",
		InputRowOrder:  "row indices 0 through 15",
		PivotRule:      "highest set bit; xor the prior basis row at that pivot",
		PivotColumns:   pivots,
		BasisRows:      basisRows,
		InputResiduals: residuals,
		Rank:           len(pivots),
	}
}
