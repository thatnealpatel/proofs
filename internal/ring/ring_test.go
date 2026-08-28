package ring

import "testing"

func TestZ2OperationTables(t *testing.T) {
	testOperationTables(t, Z2,
		[][]int{{0, 1}, {1, 0}},
		[][]int{{0, 1}, {1, 0}},
		[][]int{{0, 0}, {0, 1}},
	)
}

func TestZ3OperationTables(t *testing.T) {
	testOperationTables(t, Z3,
		[][]int{{0, 1, 2}, {1, 2, 0}, {2, 0, 1}},
		[][]int{{0, 2, 1}, {1, 0, 2}, {2, 1, 0}},
		[][]int{{0, 0, 0}, {0, 1, 2}, {0, 2, 1}},
	)
}

func testOperationTables(t *testing.T, r Ring, add, sub, mul [][]int) {
	t.Helper()
	for a := range int(r) {
		for b := range int(r) {
			if got := r.Add(a, b); got != add[a][b] {
				t.Errorf("%v.Add(%d, %d) = %d, want %d", r, a, b, got, add[a][b])
			}
			if got := r.Sub(a, b); got != sub[a][b] {
				t.Errorf("%v.Sub(%d, %d) = %d, want %d", r, a, b, got, sub[a][b])
			}
			if got := r.Mul(a, b); got != mul[a][b] {
				t.Errorf("%v.Mul(%d, %d) = %d, want %d", r, a, b, got, mul[a][b])
			}
		}
	}
}

func TestNegativeAndNoncanonicalValues(t *testing.T) {
	tests := []struct {
		name string
		got  int
		want int
	}{
		{"Z2 normalize negative", Z2.Normalize(-5), 1},
		{"Z2 normalize positive", Z2.Normalize(8), 0},
		{"Z2 add", Z2.Add(-5, 8), 1},
		{"Z2 sub", Z2.Sub(-5, 8), 1},
		{"Z2 mul", Z2.Mul(-5, 7), 1},
		{"Z3 normalize negative", Z3.Normalize(-7), 2},
		{"Z3 normalize positive", Z3.Normalize(8), 2},
		{"Z3 add", Z3.Add(-7, 8), 1},
		{"Z3 sub", Z3.Sub(-7, 8), 0},
		{"Z3 mul", Z3.Mul(-7, 8), 1},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			if test.got != test.want {
				t.Errorf("got %d, want %d", test.got, test.want)
			}
		})
	}
}

func TestIntegerExtremes(t *testing.T) {
	maxInt := int(^uint(0) >> 1)
	minInt := -maxInt - 1
	tests := []struct {
		name string
		got  int
		want int
	}{
		{"Z2 normalize MinInt", Z2.Normalize(minInt), 0},
		{"Z2 normalize MaxInt", Z2.Normalize(maxInt), 1},
		{"Z2 add extremes", Z2.Add(minInt, maxInt), 1},
		{"Z2 sub extremes", Z2.Sub(minInt, maxInt), 1},
		{"Z2 mul extremes", Z2.Mul(minInt, maxInt), 0},
		{"Z3 normalize MinInt", Z3.Normalize(minInt), 1},
		{"Z3 normalize MaxInt", Z3.Normalize(maxInt), 1},
		{"Z3 add extremes", Z3.Add(minInt, maxInt), 2},
		{"Z3 sub extremes", Z3.Sub(minInt, maxInt), 0},
		{"Z3 mul extremes", Z3.Mul(minInt, maxInt), 1},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			if test.got != test.want {
				t.Errorf("got %d, want %d", test.got, test.want)
			}
		})
	}
}

func TestRingValidity(t *testing.T) {
	for _, r := range []Ring{Z2, Z3} {
		if !r.Valid() {
			t.Errorf("Ring(%d).Valid() = false", r)
		}
	}
	for _, r := range []Ring{-3, 0, 1, 4} {
		if r.Valid() {
			t.Errorf("Ring(%d).Valid() = true", r)
		}
	}
}

func TestInvalidRingPanics(t *testing.T) {
	for _, r := range []Ring{-3, 0, 1, 4} {
		operations := map[string]func(){
			"Normalize": func() { r.Normalize(1) },
			"Add":       func() { r.Add(1, 2) },
			"Sub":       func() { r.Sub(1, 2) },
			"Mul":       func() { r.Mul(1, 2) },
		}
		for name, operation := range operations {
			t.Run(name, func(t *testing.T) {
				defer func() {
					if recover() == nil {
						t.Errorf("Ring(%d).%s did not panic", r, name)
					}
				}()
				operation()
			})
		}
	}
}
