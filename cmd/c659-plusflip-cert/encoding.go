package main

import (
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"slices"

	"patel.codes/proofs/internal/tensor"
)

func sha256Hex(data []byte) string {
	sum := sha256.Sum256(data)
	return hex.EncodeToString(sum[:])
}

func factorWord(matrix tensor.Matrix) (uint16, error) {
	if matrix.Rows() != 4 || matrix.Columns() != 4 {
		return 0, fmt.Errorf("factor dimensions are %dx%d, want 4x4", matrix.Rows(), matrix.Columns())
	}
	entries := matrix.Entries()
	if len(entries) != 16 {
		return 0, fmt.Errorf("factor has %d entries, want 16", len(entries))
	}
	var word uint16
	for index, entry := range entries {
		if entry != 0 && entry != 1 {
			return 0, fmt.Errorf("factor entry %d is %d, want binary", index, entry)
		}
		word |= uint16(entry) << index
	}
	return word, nil
}

func termWords(term tensor.RankOneTerm) (wordTriple, error) {
	var words wordTriple
	for mode := range 3 {
		word, err := factorWord(term.Factor(mode))
		if err != nil {
			return wordTriple{}, fmt.Errorf("factor %d: %w", mode, err)
		}
		words[mode] = word
	}
	return words, nil
}

func schemeWords(scheme tensor.Scheme) ([]wordTriple, error) {
	words := make([]wordTriple, scheme.TermCount())
	for slot := range scheme.TermCount() {
		triple, err := termWords(scheme.Term(slot))
		if err != nil {
			return nil, fmt.Errorf("term %d: %w", slot, err)
		}
		words[slot] = triple
	}
	return words, nil
}

func appendSchemeHeader(data []byte, scheme tensor.Scheme) ([]byte, error) {
	dimensions := scheme.Dimensions()
	values := [4]int{dimensions[0], dimensions[1], dimensions[2], scheme.TermCount()}
	for index, value := range values {
		if value < 0 || value > 65535 {
			return nil, fmt.Errorf("header value %d is %d, outside uint16", index, value)
		}
		data = binary.LittleEndian.AppendUint16(data, uint16(value))
	}
	return data, nil
}

func canonicalBytes(scheme tensor.Scheme) ([]byte, error) {
	words, err := schemeWords(scheme)
	if err != nil {
		return nil, err
	}
	slices.SortFunc(words, func(first, second wordTriple) int {
		for mode := range 3 {
			if first[mode] < second[mode] {
				return -1
			}
			if first[mode] > second[mode] {
				return 1
			}
		}
		return 0
	})
	data, err := appendSchemeHeader(make([]byte, 0, 8+6*len(words)), scheme)
	if err != nil {
		return nil, err
	}
	for _, triple := range words {
		for mode := range 3 {
			data = binary.LittleEndian.AppendUint16(data, triple[mode])
		}
	}
	return data, nil
}

func canonicalHash(scheme tensor.Scheme) (string, []byte, error) {
	data, err := canonicalBytes(scheme)
	if err != nil {
		return "", nil, err
	}
	return sha256Hex(data), data, nil
}

func orderedFactorMajorBytes(scheme tensor.Scheme) ([]byte, error) {
	words, err := schemeWords(scheme)
	if err != nil {
		return nil, err
	}
	data, err := appendSchemeHeader(make([]byte, 0, 8+6*len(words)), scheme)
	if err != nil {
		return nil, err
	}
	for mode := range 3 {
		for _, triple := range words {
			data = binary.LittleEndian.AppendUint16(data, triple[mode])
		}
	}
	return data, nil
}

func rowsHash(rows []uint16) string {
	data := make([]byte, 0, 2*len(rows))
	for _, row := range rows {
		data = binary.LittleEndian.AppendUint16(data, row)
	}
	return sha256Hex(data)
}
