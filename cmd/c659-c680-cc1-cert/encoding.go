package main

import (
	"encoding/binary"
	"fmt"
	"slices"

	"patel.codes/proofs/internal/ring"
	"patel.codes/proofs/internal/tensor"
)

func appendU16(destination []byte, values ...uint16) []byte {
	for _, value := range values {
		destination = binary.LittleEndian.AppendUint16(destination, value)
	}
	return destination
}

func appendU32(destination []byte, values ...uint32) []byte {
	for _, value := range values {
		destination = binary.LittleEndian.AppendUint32(destination, value)
	}
	return destination
}

func compareTriple(first, second triple) int {
	for mode := range 3 {
		if first[mode] < second[mode] {
			return -1
		}
		if first[mode] > second[mode] {
			return 1
		}
	}
	return 0
}

func orderedPayload(terms []triple) []byte {
	value := appendU16(nil, 4, 4, 4, uint16(len(terms)))
	for mode := range 3 {
		for _, term := range terms {
			value = appendU16(value, term[mode])
		}
	}
	return value
}

func canonicalPayload(terms []triple) []byte {
	canonical := append([]triple(nil), terms...)
	slices.SortFunc(canonical, compareTriple)
	value := appendU16(nil, 4, 4, 4, uint16(len(canonical)))
	for _, term := range canonical {
		value = appendU16(value, term[0], term[1], term[2])
	}
	return value
}

func factorWord(matrix tensor.Matrix) (uint16, error) {
	if matrix.Rows() != 4 || matrix.Columns() != 4 {
		return 0, fmt.Errorf("factor dimensions are %dx%d", matrix.Rows(), matrix.Columns())
	}
	entries := matrix.Entries()
	if len(entries) != 16 {
		return 0, fmt.Errorf("factor has %d entries", len(entries))
	}
	var word uint16
	for index, entry := range entries {
		if entry != 0 && entry != 1 {
			return 0, fmt.Errorf("factor entry %d is %d", index, entry)
		}
		word |= uint16(entry) << index
	}
	return word, nil
}

func termWords(term tensor.RankOneTerm) (triple, error) {
	var words triple
	for mode := range 3 {
		word, err := factorWord(term.Factor(mode))
		if err != nil {
			return triple{}, fmt.Errorf("factor %d: %w", mode, err)
		}
		words[mode] = word
	}
	return words, nil
}

func schemeWords(scheme tensor.Scheme) ([]triple, error) {
	words := make([]triple, scheme.TermCount())
	for slot := range words {
		word, err := termWords(scheme.Term(slot))
		if err != nil {
			return nil, fmt.Errorf("term %d: %w", slot, err)
		}
		words[slot] = word
	}
	return words, nil
}

func matrixFromWord(word uint16) (tensor.Matrix, error) {
	entries := make([]int, 16)
	for index := range entries {
		entries[index] = int(word >> index & 1)
	}
	return tensor.NewMatrix(ring.Z2, 4, 4, entries)
}

func termFromWords(words triple) (tensor.RankOneTerm, error) {
	var factors [3]tensor.Matrix
	for mode := range 3 {
		factor, err := matrixFromWord(words[mode])
		if err != nil {
			return tensor.RankOneTerm{}, fmt.Errorf("factor %d: %w", mode, err)
		}
		factors[mode] = factor
	}
	return tensor.NewRankOneTerm(factors[0], factors[1], factors[2])
}

func schemeFromWords(words []triple) (tensor.Scheme, error) {
	terms := make([]tensor.RankOneTerm, len(words))
	for index, words := range words {
		term, err := termFromWords(words)
		if err != nil {
			return tensor.Scheme{}, fmt.Errorf("term %d: %w", index, err)
		}
		terms[index] = term
	}
	return tensor.NewScheme(terms)
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
