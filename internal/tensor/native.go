package tensor

import (
	"fmt"
	"io"
	"strconv"
	"strings"

	"patel.codes/proofs/internal/ring"
)

func ParseNative(r ring.Ring, reader io.Reader) (Scheme, error) {
	if !r.Valid() {
		return Scheme{}, fmt.Errorf("unsupported ring %d", r)
	}
	data, err := io.ReadAll(reader)
	if err != nil {
		return Scheme{}, fmt.Errorf("read native scheme: %w", err)
	}
	text := string(data)
	if strings.HasSuffix(text, "\n") {
		text = strings.TrimSuffix(text, "\n")
	}
	lines := strings.Split(text, "\n")
	if len(lines) != 4 {
		return Scheme{}, fmt.Errorf("native scheme has %d lines, want 4", len(lines))
	}
	header := strings.Fields(lines[0])
	if len(header) != 4 {
		return Scheme{}, fmt.Errorf("native header has %d fields, want 4", len(header))
	}
	values := [4]int{}
	for i, token := range header {
		value, err := parsePositiveDecimal(token)
		if err != nil {
			return Scheme{}, fmt.Errorf("native header field %d: %w", i, err)
		}
		values[i] = value
	}
	dimensions := [3]int{values[0], values[1], values[2]}
	termCount := values[3]
	factorSizes := [3]int{}
	for factor := range factorSizes {
		size, err := matrixSize(dimensions[factor], dimensions[(factor+1)%3])
		if err != nil {
			return Scheme{}, fmt.Errorf("native factor %d: %w", factor, err)
		}
		factorSizes[factor] = size
	}
	parsed := [3][]int{}
	for factor := range parsed {
		tokens := strings.Fields(lines[factor+1])
		expected, err := product(termCount, factorSizes[factor])
		if err != nil {
			return Scheme{}, fmt.Errorf("native factor %d coefficient count: %w", factor, err)
		}
		if len(tokens) != expected {
			return Scheme{}, fmt.Errorf("native factor %d has %d coefficients, want %d", factor, len(tokens), expected)
		}
		parsed[factor] = make([]int, expected)
		for i, token := range tokens {
			value, err := parseSignedDecimal(token)
			if err != nil {
				return Scheme{}, fmt.Errorf("native factor %d coefficient %d: %w", factor, i, err)
			}
			parsed[factor][i] = r.Normalize(value)
		}
	}
	terms := make([]RankOneTerm, termCount)
	for termIndex := range terms {
		matrices := [3]Matrix{}
		for factor := range matrices {
			start := termIndex * factorSizes[factor]
			matrix, err := NewMatrix(
				r,
				dimensions[factor],
				dimensions[(factor+1)%3],
				parsed[factor][start:start+factorSizes[factor]],
			)
			if err != nil {
				return Scheme{}, fmt.Errorf("native term %d factor %d: %w", termIndex, factor, err)
			}
			matrices[factor] = matrix
		}
		term, err := NewRankOneTerm(matrices[0], matrices[1], matrices[2])
		if err != nil {
			return Scheme{}, fmt.Errorf("native term %d: %w", termIndex, err)
		}
		terms[termIndex] = term
	}
	return NewScheme(terms)
}

func WriteNative(writer io.Writer, scheme Scheme) error {
	if err := scheme.validateStructure(); err != nil {
		return err
	}
	var text strings.Builder
	fmt.Fprintf(
		&text,
		"%d %d %d %d\n",
		scheme.dimensions[0],
		scheme.dimensions[1],
		scheme.dimensions[2],
		len(scheme.terms),
	)
	for factor := range 3 {
		first := true
		for _, term := range scheme.terms {
			for _, entry := range term.factors[factor].entries {
				if !first {
					text.WriteByte(' ')
				}
				first = false
				text.WriteString(strconv.Itoa(entry))
			}
		}
		text.WriteByte('\n')
	}
	written, err := io.WriteString(writer, text.String())
	if err != nil {
		return fmt.Errorf("write native scheme: %w", err)
	}
	if written != text.Len() {
		return fmt.Errorf("write native scheme: %w", io.ErrShortWrite)
	}
	return nil
}

func parsePositiveDecimal(token string) (int, error) {
	if token == "" || token[0] < '1' || token[0] > '9' {
		return 0, fmt.Errorf("invalid positive decimal %q", token)
	}
	for i := 1; i < len(token); i++ {
		if token[i] < '0' || token[i] > '9' {
			return 0, fmt.Errorf("invalid positive decimal %q", token)
		}
	}
	value, err := strconv.Atoi(token)
	if err != nil {
		return 0, fmt.Errorf("invalid positive decimal %q", token)
	}
	return value, nil
}

func parseSignedDecimal(token string) (int, error) {
	if token == "" {
		return 0, fmt.Errorf("invalid signed decimal %q", token)
	}
	start := 0
	if token[0] == '+' || token[0] == '-' {
		start = 1
	}
	if start == len(token) {
		return 0, fmt.Errorf("invalid signed decimal %q", token)
	}
	for i := start; i < len(token); i++ {
		if token[i] < '0' || token[i] > '9' {
			return 0, fmt.Errorf("invalid signed decimal %q", token)
		}
	}
	value, err := strconv.Atoi(token)
	if err != nil {
		return 0, fmt.Errorf("invalid signed decimal %q", token)
	}
	return value, nil
}

func product(first, second int) (int, error) {
	maxInt := int(^uint(0) >> 1)
	if first < 0 || second < 0 || first != 0 && second > maxInt/first {
		return 0, fmt.Errorf("integer overflow")
	}
	return first * second, nil
}
