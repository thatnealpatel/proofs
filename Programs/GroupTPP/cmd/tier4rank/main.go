// Command tier4rank computes the tier-4 ranking over sieve survivors.
//
// It reads checkpoint JSONL (orders 2..511) and census shards, computes
// qr(G) = log(n_G)/log(|G|), validates against known rho_0 anchors, and
// produces a ranked survivor table (ceiling desc, qr asc).
package main

import (
	"bufio"
	"encoding/json"
	"flag"
	"fmt"
	"math"
	"os"
	"path/filepath"
	"sort"
	"strings"
)

// checkpointRecord is a single record from an order_N.jsonl checkpoint.
type checkpointRecord struct {
	ID           [2]int             `json:"id"`
	Order        int                `json:"order"`
	NilClass     *int               `json:"nil_class"`
	CenterOrder  int                `json:"center_order"`
	GZIndex      int                `json:"gz_index"`
	DerivedOrder int                `json:"derived_order"`
	PGroup       *int               `json:"p_group"`
	Tier         string             `json:"tier"`
	Action       string             `json:"action"`
	Flags        []string           `json:"flags"`
	Ceilings     map[string]float64 `json:"ceilings"`
	CD           []int              `json:"cd"`
	NG           int                `json:"n_G"`
	Ceiling      float64            `json:"ceiling"`
}

// censusRecord is a record from the survivors-census shards.
type censusRecord struct {
	ID                    [2]int   `json:"id"`
	Order                 int      `json:"order"`
	Tier                  string   `json:"tier"`
	Action                string   `json:"action"`
	NDirectFactors        int      `json:"n_direct_factors"`
	HasAbelianFactor      bool     `json:"has_abelian_factor"`
	AbelianFactorOrders   []int    `json:"abelian_factor_orders"`
	NonabelianComplements [][2]int `json:"nonabelian_complements"`
	ExtraspecialType      string   `json:"extraspecial_type"`
	T3bP                  int      `json:"t3b_p"`
	T3bK                  int      `json:"t3b_k"`
	T3bCapRational        string   `json:"t3b_cap_rational"`
}

// survivor merges checkpoint and census data for ranking.
type survivor struct {
	ID               [2]int
	Order            int
	Tier             string
	Action           string
	Ceiling          float64
	NG               int
	CD               []int
	QR               float64 // log(n_G)/log(order)
	NilClass         *int
	PGroup           *int
	GZIndex          int
	CenterOrder      int
	Flags            []string
	Ceilings         map[string]float64
	ExtraspecialType string
	HasAbelianFactor bool
	NDirectFactors   int
	T3bCapRational   string
}

// anchor represents a known rho_0 value for validation.
type anchor struct {
	ID     [2]int
	Rho0   float64
	Source string
}

func main() {
	topN := flag.Int("top", 50, "number of top survivors to display")
	checkpointDir := flag.String("checkpoints", "", "path to checkpoints/ directory")
	censusGlob := flag.String("census", "", "glob for survivors-census.shard*.jsonl")
	flag.Parse()

	if *checkpointDir == "" || *censusGlob == "" {
		fmt.Fprintf(os.Stderr, "Usage: tier4rank -checkpoints DIR -census 'GLOB'\n")
		os.Exit(1)
	}

	// Load census data into a map keyed by [order, id].
	censusMap, err := loadCensus(*censusGlob)
	if err != nil {
		fmt.Fprintf(os.Stderr, "ERROR loading census: %v\n", err)
		os.Exit(1)
	}
	fmt.Fprintf(os.Stderr, "[census] loaded %d records\n", len(censusMap))

	// Load checkpoint survivors (SURVIVE + CAP).
	survivors, err := loadCheckpointSurvivors(*checkpointDir, censusMap)
	if err != nil {
		fmt.Fprintf(os.Stderr, "ERROR loading checkpoints: %v\n", err)
		os.Exit(1)
	}
	fmt.Fprintf(os.Stderr, "[checkpoints] loaded %d survivors (SURVIVE + CAP)\n", len(survivors))

	// Compute qr(G) for all survivors.
	for i := range survivors {
		s := &survivors[i]
		if s.Order > 1 && s.NG > 0 {
			s.QR = math.Log(float64(s.NG)) / math.Log(float64(s.Order))
		}
	}

	// Sort: ceiling descending, qr ascending as secondary key.
	sort.Slice(survivors, func(i, j int) bool {
		if survivors[i].Ceiling != survivors[j].Ceiling {
			return survivors[i].Ceiling > survivors[j].Ceiling
		}
		return survivors[i].QR < survivors[j].QR
	})

	// Validate against known rho_0 anchors.
	anchors := knownAnchors()
	fmt.Println("=== ANCHOR VALIDATION ===")
	fmt.Println()
	validationPass := true
	survMap := make(map[[2]int]*survivor)
	for i := range survivors {
		survMap[survivors[i].ID] = &survivors[i]
	}
	for _, a := range anchors {
		s, found := survMap[a.ID]
		if !found {
			// Check if it was rejected (rho_0 = 1 groups get REJECT'd)
			if a.Rho0 == 1.0 {
				fmt.Printf("  [%d,%d] rho_0=%.4f (%s): REJECT (correct, not in survivors)\n",
					a.ID[0], a.ID[1], a.Rho0, a.Source)
			} else {
				fmt.Printf("  [%d,%d] rho_0=%.4f (%s): NOT FOUND IN SURVIVORS — ERROR\n",
					a.ID[0], a.ID[1], a.Rho0, a.Source)
				validationPass = false
			}
			continue
		}
		status := "OK"
		if a.Rho0 > s.Ceiling {
			status = "INCONSISTENT (rho_0 > ceiling)"
			validationPass = false
		}
		fmt.Printf("  [%d,%d] rho_0=%.4f ceiling=%.4f qr=%.4f tier=%s (%s): %s\n",
			a.ID[0], a.ID[1], a.Rho0, s.Ceiling, s.QR, s.Tier, a.Source, status)
	}
	fmt.Println()
	if validationPass {
		fmt.Println("VALIDATION: PASS — all anchors consistent (rho_0 <= ceiling)")
	} else {
		fmt.Println("VALIDATION: FAIL — inconsistencies found")
	}
	fmt.Println()

	// Class-2 ceiling agreement check: Murthy26 Thm 3.1 says rho_0 < sqrt(|G:Z|)
	// BCGPU Cor 3.8 says rho_0 <= sqrt(|G:Z|) for subgroup triples.
	// Both appear as "class2_strict" and "subgroup_packing" in ceilings.
	fmt.Println("=== CLASS-2 CEILING AGREEMENT ===")
	fmt.Println()
	class2Agree := 0
	class2Total := 0
	for i := range survivors {
		s := &survivors[i]
		if s.NilClass == nil {
			continue
		}
		if *s.NilClass != 2 {
			continue
		}
		class2Total++
		c2strict, hasC2 := s.Ceilings["class2_strict"]
		subPack, hasSP := s.Ceilings["subgroup_packing"]
		if hasC2 && hasSP {
			// class2_strict = sqrt(|G:Z|) from Murthy26 Thm 3.1
			// subgroup_packing = sqrt(|G:Z|) from BCGPU Cor 3.8
			// They should agree (both are sqrt(|G:Z|) for class-2 groups)
			if math.Abs(c2strict-subPack) < 1e-9 {
				class2Agree++
			} else {
				fmt.Printf("  DISAGREEMENT [%d,%d]: class2_strict=%.6f subgroup_packing=%.6f\n",
					s.ID[0], s.ID[1], c2strict, subPack)
			}
		}
	}
	fmt.Printf("  Class-2 survivors checked: %d, ceilings agree: %d\n", class2Total, class2Agree)
	fmt.Println()

	// Print ranked table.
	fmt.Println("=== RANKED SURVIVOR TABLE (top N by ceiling desc, qr asc) ===")
	fmt.Println()
	fmt.Printf("%-12s %5s %4s %8s %6s %6s %5s %6s %s\n",
		"Group", "Order", "n_G", "Ceiling", "qr", "|G:Z|", "Class", "Type", "Notes")
	fmt.Println(strings.Repeat("-", 80))

	n := *topN
	if n > len(survivors) {
		n = len(survivors)
	}
	for i := 0; i < n; i++ {
		s := &survivors[i]
		classStr := "-"
		if s.NilClass != nil {
			classStr = fmt.Sprintf("%d", *s.NilClass)
		}
		typeStr := ""
		if s.ExtraspecialType != "" {
			typeStr = "ES" + s.ExtraspecialType
		}
		notes := ""
		if s.HasAbelianFactor {
			notes += "abfac "
		}
		if s.T3bCapRational != "" {
			notes += "T3b:" + s.T3bCapRational + " "
		}
		if s.Action != "SURVIVE" {
			notes += s.Action + " "
		}
		fmt.Printf("[%-4d,%-4d] %5d %4d %8.4f %6.4f %6d %5s %6s %s\n",
			s.ID[0], s.ID[1], s.Order, s.NG, s.Ceiling, s.QR, s.GZIndex, classStr, typeStr, notes)
	}

	// Summary stats.
	fmt.Println()
	fmt.Println("=== SUMMARY STATISTICS ===")
	fmt.Println()
	surviveCount := 0
	capCount := 0
	for i := range survivors {
		if survivors[i].Action == "SURVIVE" {
			surviveCount++
		} else {
			capCount++
		}
	}
	fmt.Printf("  Total in ranking: %d (SURVIVE: %d, CAP: %d)\n", len(survivors), surviveCount, capCount)
	if len(survivors) > 0 {
		fmt.Printf("  Ceiling range: [%.4f, %.4f]\n", survivors[len(survivors)-1].Ceiling, survivors[0].Ceiling)
		fmt.Printf("  qr range: [%.4f, %.4f]\n",
			minQR(survivors), maxQR(survivors))
	}

	// Per-order coverage caveat.
	fmt.Println()
	fmt.Println("=== CAVEATS ===")
	fmt.Println()
	fmt.Println("  - Orders 256/384 were re-run to completion; legacy orders lack sentinels")
	fmt.Println("    but are treated as complete (Im4 verification confirms 510/510 orders,")
	fmt.Println("    91774 nonabelian records, zero discrepancies).")
	fmt.Println("  - Per-tier counts are CASCADE-ATTRIBUTION, not disjoint mathematical")
	fmt.Println("    classes (Isaacs-Passman overlap: T1b partially shadows T2a/T3a).")
	fmt.Println("  - Ceilings are upper bounds: high ceiling = 'not yet excluded', never 'promising'.")
	fmt.Println("  - Stratum B (order 512) is pending USER run, not included.")
}

func knownAnchors() []anchor {
	return []anchor{
		// Murthy26 / reading-papers: [32,49] extraspecial+ achieves rho_0=2
		{ID: [2]int{32, 49}, Rho0: 2.0, Source: "Murthy26 Thm 4.1 (T1c sharp)"},
		// [32,50] extraspecial- has rho_0=1
		{ID: [2]int{32, 50}, Rho0: 1.0, Source: "Murthy26 (extraspecial- known)"},
		// HM Table 2: [64,226] D8^2, rho_0=2 (beta_g=128, |G|=64)
		{ID: [2]int{64, 226}, Rho0: 2.0, Source: "HM12 Table 2 (beta_g/|G|=2)"},
		// HM Table 2: [128,2194] C2xD8^2, rho_0=2
		{ID: [2]int{128, 2194}, Rho0: 2.0, Source: "HM12 Table 2 (beta_g/|G|=2)"},
		// HM Table 1 selected anchors (order < 25):
		// All rho_0 values here are beta_g/|G| (SUBGROUP TPP ratio),
		// which is what Murthy25/26 and BCGPU bound.
		// [6,1] S3: beta_g=8, rho_0 = 8/6 = 4/3
		{ID: [2]int{6, 1}, Rho0: 4.0 / 3.0, Source: "HM12 Table 1 (beta_g)"},
		// [8,3] D8: beta_g=8, rho_0 = 8/8 = 1
		{ID: [2]int{8, 3}, Rho0: 1.0, Source: "HM12 Table 1 (beta_g)"},
		// [8,4] Q8: beta_g=8, rho_0 = 8/8 = 1
		{ID: [2]int{8, 4}, Rho0: 1.0, Source: "HM12 Table 1 (beta_g)"},
		// [10,1] D10: beta_g=10, rho_0 = 10/10 = 1 (subset rho=1.2 higher!)
		{ID: [2]int{10, 1}, Rho0: 1.0, Source: "HM12 Table 1 (beta_g; subset beta=12)"},
		// [12,3] A4: beta_g=18, rho_0 = 18/12 = 1.5
		{ID: [2]int{12, 3}, Rho0: 1.5, Source: "HM12 Table 1 (beta_g)"},
		// [20,3] C5oC4: beta_g=32, rho_0 = 32/20 = 1.6
		{ID: [2]int{20, 3}, Rho0: 1.6, Source: "HM12 Table 1 (beta_g)"},
		// [24,3] SL2F3: beta_g=36, rho_0 = 36/24 = 1.5
		{ID: [2]int{24, 3}, Rho0: 1.5, Source: "HM12 Table 1 (beta_g)"},
		// [24,12] S4: beta_g=36, rho_0 = 36/24 = 1.5
		{ID: [2]int{24, 12}, Rho0: 1.5, Source: "HM12 Table 1 (beta_g)"},
		// [24,10] C3xD8: beta_g=24, rho_0 = 24/24 = 1
		{ID: [2]int{24, 10}, Rho0: 1.0, Source: "HM12 Table 1 (beta_g)"},
		// [24,11] C3xQ8: beta_g=24, rho_0 = 24/24 = 1
		{ID: [2]int{24, 11}, Rho0: 1.0, Source: "HM12 Table 1 (beta_g)"},
	}
}

func loadCensus(glob string) (map[[2]int]*censusRecord, error) {
	files, err := filepath.Glob(glob)
	if err != nil {
		return nil, err
	}
	if len(files) == 0 {
		return nil, fmt.Errorf("no files match glob %q", glob)
	}
	m := make(map[[2]int]*censusRecord)
	for _, f := range files {
		fh, err := os.Open(f)
		if err != nil {
			return nil, err
		}
		scanner := bufio.NewScanner(fh)
		scanner.Buffer(make([]byte, 1<<20), 1<<20)
		for scanner.Scan() {
			line := scanner.Bytes()
			if len(line) == 0 {
				continue
			}
			var rec censusRecord
			if err := json.Unmarshal(line, &rec); err != nil {
				fh.Close()
				return nil, fmt.Errorf("parse %s: %w", f, err)
			}
			key := [2]int{rec.ID[0], rec.ID[1]}
			m[key] = &rec
		}
		if err := scanner.Err(); err != nil {
			fh.Close()
			return nil, err
		}
		fh.Close()
	}
	return m, nil
}

func loadCheckpointSurvivors(dir string, census map[[2]int]*censusRecord) ([]survivor, error) {
	files, err := filepath.Glob(filepath.Join(dir, "order_*.jsonl"))
	if err != nil {
		return nil, err
	}
	var survivors []survivor
	for _, f := range files {
		fh, err := os.Open(f)
		if err != nil {
			return nil, err
		}
		scanner := bufio.NewScanner(fh)
		scanner.Buffer(make([]byte, 1<<20), 1<<20)
		for scanner.Scan() {
			line := scanner.Bytes()
			if len(line) == 0 {
				continue
			}
			// Skip sentinel lines
			if strings.Contains(string(line), "order_complete") {
				continue
			}
			var rec checkpointRecord
			if err := json.Unmarshal(line, &rec); err != nil {
				fh.Close()
				return nil, fmt.Errorf("parse %s: %w", f, err)
			}
			if rec.Action == "REJECT" || rec.Action == "ERROR" {
				continue
			}
			s := survivor{
				ID:          rec.ID,
				Order:       rec.Order,
				Tier:        rec.Tier,
				Action:      rec.Action,
				Ceiling:     rec.Ceiling,
				NG:          rec.NG,
				CD:          rec.CD,
				NilClass:    rec.NilClass,
				PGroup:      rec.PGroup,
				GZIndex:     rec.GZIndex,
				CenterOrder: rec.CenterOrder,
				Flags:       rec.Flags,
				Ceilings:    rec.Ceilings,
			}
			// Merge census data.
			key := [2]int{rec.ID[0], rec.ID[1]}
			if c, ok := census[key]; ok {
				s.ExtraspecialType = c.ExtraspecialType
				s.HasAbelianFactor = c.HasAbelianFactor
				s.NDirectFactors = c.NDirectFactors
				s.T3bCapRational = c.T3bCapRational
			}
			survivors = append(survivors, s)
		}
		if err := scanner.Err(); err != nil {
			fh.Close()
			return nil, err
		}
		fh.Close()
	}
	return survivors, nil
}

func minQR(ss []survivor) float64 {
	m := math.Inf(1)
	for i := range ss {
		if ss[i].QR < m {
			m = ss[i].QR
		}
	}
	return m
}

func maxQR(ss []survivor) float64 {
	m := math.Inf(-1)
	for i := range ss {
		if ss[i].QR > m {
			m = ss[i].QR
		}
	}
	return m
}
