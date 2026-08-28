package main

import (
	"fmt"
	"sync"

	"patel.codes/proofs/internal/ring"
	"patel.codes/proofs/internal/tensor"
)

type tensorBits [64]uint64

var outerCache sync.Map

func factorWord(matrix tensor.Matrix) (uint16, error) {
	if matrix.Rows() != 4 || matrix.Columns() != 4 {
		return 0, fmt.Errorf("factor dimensions are %dx%d", matrix.Rows(), matrix.Columns())
	}
	var word uint16
	entries := matrix.Entries()
	if len(entries) != 16 {
		return 0, fmt.Errorf("factor has %d entries", len(entries))
	}
	for index, entry := range entries {
		if entry != 0 && entry != 1 {
			return 0, fmt.Errorf("factor entry %d is %d", index, entry)
		}
		word |= uint16(entry) << index
	}
	return word, nil
}

func termWords(term tensor.RankOneTerm) (triple, error) {
	var result triple
	for mode := range 3 {
		word, err := factorWord(term.Factor(mode))
		if err != nil {
			return result, fmt.Errorf("factor %d: %w", mode, err)
		}
		result[mode] = word
	}
	return result, nil
}

func schemeWords(scheme tensor.Scheme) ([]triple, error) {
	result := make([]triple, scheme.TermCount())
	for slot := range result {
		value, err := termWords(scheme.Term(slot))
		if err != nil {
			return nil, fmt.Errorf("term %d: %w", slot, err)
		}
		result[slot] = value
	}
	return result, nil
}

func matrixFromWord(word uint16) (tensor.Matrix, error) {
	entries := make([]int, 16)
	for bit := range 16 {
		entries[bit] = int(word >> bit & 1)
	}
	return tensor.NewMatrix(ring.Z2, 4, 4, entries)
}

func termFromWords(value triple) (tensor.RankOneTerm, error) {
	var matrices [3]tensor.Matrix
	for mode := range 3 {
		matrix, err := matrixFromWord(value[mode])
		if err != nil {
			return tensor.RankOneTerm{}, err
		}
		matrices[mode] = matrix
	}
	return tensor.NewRankOneTerm(matrices[0], matrices[1], matrices[2])
}

func schemeFromWords(words []triple) (tensor.Scheme, error) {
	terms := make([]tensor.RankOneTerm, len(words))
	for index, word := range words {
		term, err := termFromWords(word)
		if err != nil {
			return tensor.Scheme{}, fmt.Errorf("term %d: %w", index, err)
		}
		terms[index] = term
	}
	return tensor.NewScheme(terms)
}

func validateExactScheme(words []triple, brent bool) error {
	scheme, err := schemeFromWords(words)
	if err != nil {
		return err
	}
	if err := tensor.ValidateNonzeroTerms(scheme); err != nil {
		return err
	}
	if err := tensor.ValidateDistinctTensors(scheme); err != nil {
		return err
	}
	if brent {
		if err := tensor.ValidateBrent(scheme); err != nil {
			return err
		}
	}
	return nil
}

func outer(value triple) tensorBits {
	if found, ok := outerCache.Load(value); ok {
		return found.(tensorBits)
	}
	var result tensorBits
	for a := range 16 {
		if value[0]&(1<<a) == 0 {
			continue
		}
		for b := range 16 {
			if value[1]&(1<<b) == 0 {
				continue
			}
			for c := range 16 {
				if value[2]&(1<<c) == 0 {
					continue
				}
				bit := (a*16+b)*16 + c
				result[bit/64] |= uint64(1) << (bit % 64)
			}
		}
	}
	outerCache.Store(value, result)
	return result
}

func tensorSum(terms []triple) tensorBits {
	var result tensorBits
	for _, term := range terms {
		value := outer(term)
		for index := range result {
			result[index] ^= value[index]
		}
	}
	return result
}

func tensorBytes(value tensorBits) []byte {
	result := make([]byte, 512)
	for index, word := range value {
		for byteIndex := range 8 {
			result[index*8+byteIndex] = byte(word >> (8 * byteIndex))
		}
	}
	return result
}

func targetTensor() tensorBits {
	var result tensorBits
	for i := range 4 {
		for j := range 4 {
			for k := range 4 {
				bit := (((4*i+j)*16)+(4*j+k))*16 + (4*k + i)
				result[bit/64] |= uint64(1) << (bit % 64)
			}
		}
	}
	return result
}

func validTerms(terms []triple) bool {
	seen := make(map[triple]bool, len(terms))
	for _, term := range terms {
		if term[0] == 0 || term[1] == 0 || term[2] == 0 || seen[term] {
			return false
		}
		seen[term] = true
	}
	return true
}

func sourceLegal(sources [2]triple) bool {
	for source := range 2 {
		for mode := range 3 {
			if sources[source][mode] == 0 {
				return false
			}
		}
	}
	for mode := range 3 {
		if sources[0][mode] == sources[1][mode] {
			return false
		}
	}
	return true
}

func plus(first, second triple, positions [3]int, variant int) [3]triple {
	a1, b1, c1 := first[positions[0]], first[positions[1]], first[positions[2]]
	a2, b2, c2 := second[positions[0]], second[positions[1]], second[positions[2]]
	var oriented [3]triple
	switch variant {
	case 0:
		oriented = [3]triple{{a1, b1 ^ b2, c1}, {a1 ^ a2, b2, c2}, {a1, b2, c1 ^ c2}}
	case 1:
		oriented = [3]triple{{a1, b1, c1 ^ c2}, {a2, b1 ^ b2, c2}, {a1 ^ a2, b1, c2}}
	case 2:
		oriented = [3]triple{{a1 ^ a2, b1, c1}, {a2, b2, c1 ^ c2}, {a2, b1 ^ b2, c1}}
	default:
		panic("invalid Plus variant")
	}
	var result [3]triple
	for output := range 3 {
		for coordinate, mode := range positions {
			result[output][mode] = oriented[output][coordinate]
		}
	}
	return result
}

func inverse(outputs [3]triple, positions [3]int, variant int) ([2]triple, [3]triple, uint16) {
	var oriented [3]triple
	for output := range 3 {
		for coordinate, mode := range positions {
			oriented[output][coordinate] = outputs[output][mode]
		}
	}
	first, second := oriented[0], oriented[1]
	var a1, b1, c1, a2, b2, c2 uint16
	switch variant {
	case 0:
		a1, b2, c1 = first[0], second[1], first[2]
		a2, b1, c2 = second[0]^a1, first[1]^b2, second[2]
	case 1:
		a1, b1, c2 = first[0], first[1], second[2]
		c1, a2, b2 = first[2]^c2, second[0], second[1]^b1
	case 2:
		a2, b1, c1 = second[0], first[1], first[2]
		a1, b2, c2 = first[0]^a2, second[1], second[2]^c1
	default:
		panic("invalid inverse variant")
	}
	orientedSources := [2]triple{{a1, b1, c1}, {a2, b2, c2}}
	var sources [2]triple
	for source := range 2 {
		for coordinate, mode := range positions {
			sources[source][mode] = orientedSources[source][coordinate]
		}
	}
	replay := plus(sources[0], sources[1], positions, variant)
	var mask uint16
	coordinate := uint(0)
	for output := range 3 {
		for factor := range 3 {
			if replay[output][positions[factor]] == oriented[output][factor] {
				mask |= 1 << coordinate
			}
			coordinate++
		}
	}
	return sources, replay, mask
}

func orient(value triple, positions [3]int) triple {
	return triple{value[positions[0]], value[positions[1]], value[positions[2]]}
}

func unorient(value triple, positions [3]int) triple {
	var result triple
	for coordinate, mode := range positions {
		result[mode] = value[coordinate]
	}
	return result
}

func exactPlusConstructor(first, second triple, positions [3]int) ([3]triple, error) {
	scheme, err := schemeFromWords([]triple{orient(first, positions), orient(second, positions)})
	if err != nil {
		return [3]triple{}, err
	}
	replacement, err := tensor.NewPlusReplacement(scheme, 0, 1)
	if err != nil {
		return [3]triple{}, err
	}
	inserted := replacement.InsertedTerms()
	if len(inserted) != 3 {
		return [3]triple{}, fmt.Errorf("tensor Plus inserted %d terms", len(inserted))
	}
	var outputs [3]triple
	for index, term := range inserted {
		word, err := termWords(term)
		if err != nil {
			return [3]triple{}, err
		}
		outputs[index] = unorient(word, positions)
	}
	return outputs, nil
}

func exactInverseConstructor(outputs [3]triple, positions [3]int, variant int) ([2]triple, error) {
	orientedOutputs := make([]triple, 3)
	for index := range outputs {
		orientedOutputs[index] = orient(outputs[index], positions)
	}
	scheme, err := schemeFromWords(orientedOutputs)
	if err != nil {
		return [2]triple{}, err
	}
	replacement, err := tensor.NewInversePlusReplacement(scheme, [3]int{0, 1, 2}, tensor.PlusVariant(variant))
	if err != nil {
		return [2]triple{}, err
	}
	inserted := replacement.InsertedTerms()
	if len(inserted) != 2 {
		return [2]triple{}, fmt.Errorf("tensor inverse Plus inserted %d terms", len(inserted))
	}
	var sources [2]triple
	for index, term := range inserted {
		word, err := termWords(term)
		if err != nil {
			return [2]triple{}, err
		}
		sources[index] = unorient(word, positions)
	}
	return sources, nil
}
