package tpp

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"strconv"
)

// jsonGroup is the on-disk JSON format
// written by export_tpp.sage.
type jsonGroup struct {
	ID          string  `json:"id"`
	Description string  `json:"description"`
	Category    string  `json:"category"`
	ExpRho0     *string `json:"expected_rho0"`
	N           int     `json:"n"`
	CayleyTable []int   `json:"cayley_table"`
	InvTable    []int   `json:"inverse_table"`
	NConjClass  int     `json:"n_conjugacy_classes"`
	NSubgroups  int     `json:"n_subgroups"`
	Subgroups   []struct {
		Elements []int `json:"elements"`
		Order    int   `json:"order"`
		Class    int   `json:"class"`
		IsRep    bool  `json:"is_rep"`
		IsNormal bool  `json:"is_normal"`
	} `json:"subgroups"`
	Abelianization []struct {
		DerivedOrder      int              `json:"derived_order"`
		AbelianInvariants []int            `json:"abelian_invariants"`
		ExponentVectors   map[string][]int `json:"exponent_vectors"`
	} `json:"abelianization"`
}

// LoadGroup loads a group from a JSON file
// produced by export_tpp.sage.
func LoadGroup(path string) (*Group, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, fmt.Errorf("read %s: %w", path, err)
	}

	var jg jsonGroup
	if err := json.Unmarshal(data, &jg); err != nil {
		return nil, fmt.Errorf("parse %s: %w", path, err)
	}

	if jg.N <= 0 {
		return nil, fmt.Errorf("%s: invalid group order %d", path, jg.N)
	}

	n := jg.N

	// Convert Cayley table.
	if len(jg.CayleyTable) != n*n {
		return nil, fmt.Errorf("%s: cayley table has %d entries, want %d",
			path, len(jg.CayleyTable), n*n)
	}
	table := make([]uint16, n*n)
	for i, v := range jg.CayleyTable {
		if v < 0 || v >= n {
			return nil, fmt.Errorf("%s: cayley table entry %d out of range [0,%d)", path, v, n)
		}
		table[i] = uint16(v)
	}

	// Convert inverse table.
	if len(jg.InvTable) != n {
		return nil, fmt.Errorf("%s: inverse table has %d entries, want %d",
			path, len(jg.InvTable), n)
	}
	inv := make([]uint16, n)
	for i, v := range jg.InvTable {
		if v < 0 || v >= n {
			return nil, fmt.Errorf("%s: inv table entry %d out of range", path, v)
		}
		inv[i] = uint16(v)
	}

	// Build subgroups.
	subs := make([]Subgroup, len(jg.Subgroups))
	classMap := map[int][]int{} // class index -> subgroup indices
	classRep := map[int]int{}   // class index -> rep subgroup index

	for si, js := range jg.Subgroups {
		bs := NewBitset(n)
		eltList := make([]uint16, len(js.Elements))
		for ei, e := range js.Elements {
			if e < 0 || e >= n {
				return nil, fmt.Errorf("%s: subgroup %d element %d out of range", path, si, e)
			}
			bs.Set(e)
			eltList[ei] = uint16(e)
		}
		sort.Slice(eltList, func(a, b int) bool { return eltList[a] < eltList[b] })

		subs[si] = Subgroup{
			Elts:     bs,
			EltList:  eltList,
			Order:    js.Order,
			Class:    js.Class,
			IsRep:    js.IsRep,
			IsNormal: js.IsNormal,
		}

		// Populate abelianization data if present.
		if si < len(jg.Abelianization) {
			ab := jg.Abelianization[si]
			subs[si].DerivedOrder = ab.DerivedOrder
			subs[si].AbelianInvariants = ab.AbelianInvariants
			evecs := make(map[uint16][]int, len(ab.ExponentVectors))
			for kStr, vec := range ab.ExponentVectors {
				idx, err := strconv.Atoi(kStr)
				if err != nil {
					return nil, fmt.Errorf("%s: subgroup %d: bad exponent vector key %q: %w", path, si, kStr, err)
				}
				evecs[uint16(idx)] = vec
			}
			subs[si].ExponentVectors = evecs
		}

		classMap[js.Class] = append(classMap[js.Class], si)
		if js.IsRep {
			classRep[js.Class] = si
		}
	}

	// Build ordered class lists.
	nClasses := jg.NConjClass
	classSlices := make([][]int, nClasses)
	classReps := make([]int, nClasses)
	for c := 0; c < nClasses; c++ {
		classSlices[c] = classMap[c]
		rep, ok := classRep[c]
		if !ok {
			// No explicit rep; pick the first member.
			if len(classMap[c]) == 0 {
				return nil, fmt.Errorf("%s: empty conjugacy class %d", path, c)
			}
			rep = classMap[c][0]
		}
		classReps[c] = rep
	}

	expRho0 := ""
	if jg.ExpRho0 != nil {
		expRho0 = *jg.ExpRho0
	}

	return &Group{
		ID:          jg.ID,
		Description: jg.Description,
		Category:    jg.Category,
		ExpRho0:     expRho0,
		N:           n,
		Table:       table,
		Inv:         inv,
		Subgroups:   subs,
		Classes:     classSlices,
		ClassRep:    classReps,
	}, nil
}

// jsonManifestEntry is one entry in the
// exporter's manifest.json.
type jsonManifestEntry struct {
	ID          string  `json:"id"`
	Description string  `json:"description"`
	Category    string  `json:"category"`
	ExpRho0     *string `json:"expected_rho0"`
}

// ManifestEntry describes one target from the manifest.
type ManifestEntry struct {
	ID          string
	Description string
	Category    string
	ExpRho0     string
}

// LoadManifest reads the manifest.json file from the data
// directory.
func LoadManifest(dataDir string) ([]ManifestEntry, error) {
	path := filepath.Join(dataDir, "manifest.json")
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, fmt.Errorf("read manifest: %w", err)
	}

	var entries []jsonManifestEntry
	if err := json.Unmarshal(data, &entries); err != nil {
		return nil, fmt.Errorf("parse manifest: %w", err)
	}

	result := make([]ManifestEntry, len(entries))
	for i, e := range entries {
		exp := ""
		if e.ExpRho0 != nil {
			exp = *e.ExpRho0
		}
		result[i] = ManifestEntry{
			ID:          e.ID,
			Description: e.Description,
			Category:    e.Category,
			ExpRho0:     exp,
		}
	}
	return result, nil
}

// GroupPath returns the expected JSON file
// path for a target ID.
func GroupPath(dataDir, id string) string {
	return filepath.Join(dataDir, id+".json")
}
