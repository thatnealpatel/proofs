package tensor

import (
	"fmt"

	"patel.codes/proofs/internal/ring"
)

type Matrix struct {
	ring    ring.Ring
	rows    int
	columns int
	entries []int
}

func NewMatrix(r ring.Ring, rows, columns int, entries []int) (Matrix, error) {
	if !r.Valid() {
		return Matrix{}, fmt.Errorf("unsupported ring %d", r)
	}
	size, err := matrixSize(rows, columns)
	if err != nil {
		return Matrix{}, err
	}
	if len(entries) != size {
		return Matrix{}, fmt.Errorf("matrix has %d entries, want %d", len(entries), size)
	}
	normalized := make([]int, len(entries))
	for i, entry := range entries {
		normalized[i] = r.Normalize(entry)
	}
	return Matrix{ring: r, rows: rows, columns: columns, entries: normalized}, nil
}

func (m Matrix) Ring() ring.Ring {
	return m.ring
}

func (m Matrix) Rows() int {
	return m.rows
}

func (m Matrix) Columns() int {
	return m.columns
}

func (m Matrix) At(row, column int) int {
	if row < 0 || row >= m.rows || column < 0 || column >= m.columns {
		panic("matrix index out of range")
	}
	return m.entries[row*m.columns+column]
}

func (m Matrix) Entries() []int {
	return append([]int(nil), m.entries...)
}

func (m Matrix) clone() Matrix {
	m.entries = append([]int(nil), m.entries...)
	return m
}

func matrixSize(rows, columns int) (int, error) {
	if rows <= 0 || columns <= 0 {
		return 0, fmt.Errorf("matrix dimensions must be positive, got %d by %d", rows, columns)
	}
	maxInt := int(^uint(0) >> 1)
	if rows > maxInt/columns {
		return 0, fmt.Errorf("matrix dimensions overflow: %d by %d", rows, columns)
	}
	return rows * columns, nil
}
