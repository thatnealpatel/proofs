package tpp

import (
	"testing"
)

func TestAbelianLatticeZ2(t *testing.T) {
	// Z/2 has 2 subgroups: {0}, {0,1}.
	lat := AbelianLattice([]int{2})
	if len(lat) != 2 {
		t.Fatalf("Z/2: got %d subgroups, want 2", len(lat))
	}
}

func TestAbelianLatticeZ4(t *testing.T) {
	// Z/4 has 3 subgroups: {0}, {0,2}, {0,1,2,3}.
	lat := AbelianLattice([]int{4})
	if len(lat) != 3 {
		t.Fatalf("Z/4: got %d subgroups, want 3", len(lat))
	}
}

func TestAbelianLatticeZ2xZ2(t *testing.T) {
	// Z/2 x Z/2 has 5 subgroups.
	lat := AbelianLattice([]int{2, 2})
	if len(lat) != 5 {
		t.Fatalf("Z/2 x Z/2: got %d subgroups, want 5", len(lat))
	}
}

func TestAbelianLatticeZ6(t *testing.T) {
	// Z/6 has 4 subgroups.
	lat := AbelianLattice([]int{6})
	if len(lat) != 4 {
		t.Fatalf("Z/6: got %d subgroups, want 4", len(lat))
	}
}

func TestAbelianLatticeZ2xZ2xZ2(t *testing.T) {
	// Z/2^3 has 16 subgroups.
	lat := AbelianLattice([]int{2, 2, 2})
	if len(lat) != 16 {
		t.Fatalf("Z/2^3: got %d subgroups, want 16", len(lat))
	}
}

func TestAbelianLatticeTrivial(t *testing.T) {
	lat := AbelianLattice(nil)
	if len(lat) != 1 {
		t.Fatalf("trivial: got %d subgroups, want 1", len(lat))
	}
	if lat[0].Order != 1 {
		t.Fatalf("trivial: subgroup order %d, want 1", lat[0].Order)
	}
}

func TestAbelianLatticeZ3xZ3(t *testing.T) {
	// Z/3 x Z/3 has 6 subgroups.
	lat := AbelianLattice([]int{3, 3})
	if len(lat) != 6 {
		t.Fatalf("Z/3 x Z/3: got %d subgroups, want 6", len(lat))
	}
}

func TestAbelianLatticeZ2xZ4(t *testing.T) {
	// Z/2 x Z/4 has 8 subgroups (validated against GAP).
	lat := AbelianLattice([]int{2, 4})
	if len(lat) != 8 {
		t.Fatalf("Z/2 x Z/4: got %d subgroups, want 8", len(lat))
	}
}

func TestAbelianLatticeZ2xZ2xZ3(t *testing.T) {
	// Z/2 x Z/2 x Z/3 has 10 subgroups
	// (validated against GAP).
	lat := AbelianLattice([]int{2, 2, 3})
	if len(lat) != 10 {
		t.Fatalf("Z/2 x Z/2 x Z/3: got %d subgroups, want 10", len(lat))
	}
}

func TestAbelianLatticeZ12(t *testing.T) {
	// Z/12 ~ Z/4 x Z/3 has 6 subgroups.
	lat := AbelianLattice([]int{12})
	if len(lat) != 6 {
		t.Fatalf("Z/12: got %d subgroups, want 6", len(lat))
	}
}

func TestAbelianLatticeZ2xZ2xZ2xZ2(t *testing.T) {
	// Z/2^4 has 67 subgroups (well-known).
	lat := AbelianLattice([]int{2, 2, 2, 2})
	if len(lat) != 67 {
		t.Fatalf("Z/2^4: got %d subgroups, want 67", len(lat))
	}
}

func TestPackUnpackRoundtrip(t *testing.T) {
	invs := []int{6, 4, 3}
	v := []int{5, 3, 2}
	pk := packVec(v, invs)
	got := unpackVec(pk, invs)
	for i := range v {
		if got[i] != v[i] {
			t.Errorf("component %d: got %d, want %d", i, got[i], v[i])
		}
	}
}

func TestAddPacked(t *testing.T) {
	invs := []int{3, 4}
	a := packVec([]int{2, 3}, invs)
	b := packVec([]int{2, 2}, invs)
	sum := addPacked(a, b, invs)
	got := unpackVec(sum, invs)
	// (2+2)%3 = 1, (3+2)%4 = 1
	if got[0] != 1 || got[1] != 1 {
		t.Errorf("got (%d,%d), want (1,1)", got[0], got[1])
	}
}

func TestAbelianSubgroupClosure(t *testing.T) {
	// Every subgroup must contain the
	// identity and be closed under addition.
	invs := []int{2, 3}
	lat := AbelianLattice(invs)
	zero := packVec([]int{0, 0}, invs)
	for i, sub := range lat {
		if _, ok := sub.Elements[zero]; !ok {
			t.Errorf("subgroup %d: missing identity", i)
		}
		// Check closure.
		for a := range sub.Elements {
			for b := range sub.Elements {
				sum := addPacked(a, b, invs)
				if _, ok := sub.Elements[sum]; !ok {
					t.Errorf("subgroup %d: not closed under addition", i)
				}
			}
		}
	}
}
