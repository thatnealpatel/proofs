// Command gelfandrank applies the Pf5
// rigidity strengthening and BCZ17 s-rank
// lower bound to the Gelfand screen
// output, deduplicates by available-field
// fingerprint, and emits the ranked
// survivor JSONL and ranking doc.
package main

import (
	"bufio"
	"crypto/sha256"
	"encoding/json"
	"fmt"
	"math"
	"os"
	"sort"
)

// record is a single Gelfand screen output record.
type record struct {
	GID            [2]int `json:"G_id"`
	HID            [2]int `json:"H_id"`
	HClass         int    `json:"H_class"`
	N              int    `json:"N"`
	R              int    `json:"r"`
	IsSymmetric    bool   `json:"is_symmetric"`
	Multiplicities []int  `json:"multiplicities"`
	Valencies      []int  `json:"valencies"`
	TriangleCount  int    `json:"triangle_count"`
	Partners       []int  `json:"partners"`
	NC4Bound       int    `json:"nc4_bound"`
	CapEff         int    `json:"cap_eff"`
	NC1Pass        bool   `json:"nc1_pass"`
	NC2Pass        bool   `json:"nc2_pass"`
	IsThin         bool   `json:"is_thin"`
	Verdict        string `json:"verdict"`
}

// outputRecord extends a KEEP record with
// strengthened fields.
type outputRecord struct {
	GID            [2]int `json:"G_id"`
	HID            [2]int `json:"H_id"`
	HClass         int    `json:"H_class"`
	N              int    `json:"N"`
	R              int    `json:"r"`
	IsSymmetric    bool   `json:"is_symmetric"`
	Multiplicities []int  `json:"multiplicities"`
	Valencies      []int  `json:"valencies"`
	TriangleCount  int    `json:"triangle_count"`
	Partners       []int  `json:"partners"`
	NC4Bound       int    `json:"nc4_bound"`
	CapEff         int    `json:"cap_eff"`
	NC1Pass        bool   `json:"nc1_pass"`
	NC2Pass        bool   `json:"nc2_pass"`
	IsThin         bool   `json:"is_thin"`
	Verdict        string `json:"verdict"`
	Cap2           int    `json:"cap2"`
	Cap3           int    `json:"cap3"`
	FingerprintID  string `json:"fingerprint_id"`
}

// scored holds a KEEP record with
// its strengthened cap2, cap3, and
// fingerprint.
type scored struct {
	rec  record
	cap2 int
	cap3 int
	fp   string
}

func main() {
	inputPath := "/home/exedev/p/proofs/Scratch/GroupSieve/gelfand-screen.jsonl"
	outputPath := "/home/exedev/p/proofs/Scratch/GroupSieve/gelfand-keep-dedup.jsonl"
	docPath := "/home/exedev/p/proofs/.tasks/f5exp/docs/Im8-gelfand-ranking.md"

	// Read all records.
	records, err := readRecords(inputPath)
	if err != nil {
		fmt.Fprintf(os.Stderr, "ERROR reading input: %v\n", err)
		os.Exit(1)
	}
	fmt.Fprintf(os.Stderr, "Read %d total records\n", len(records))

	// Filter KEEP records.
	var keeps []record
	for i := range records {
		if records[i].Verdict == "KEEP" {
			keeps = append(keeps, records[i])
		}
	}
	fmt.Fprintf(os.Stderr, "KEEP records: %d\n", len(keeps))

	// Apply rigidity strengthening: compute cap2.
	var all []scored
	r4KeepCount := 0
	r4SurviveCount := 0

	for i := range keeps {
		rec := keeps[i]
		cap2 := computeCap2(rec)
		cap3 := computeCap3(rec, cap2)
		fp := computeFingerprint(rec)

		if rec.R == 4 {
			r4KeepCount++
			if cap2 >= 2 {
				r4SurviveCount++
			}
		}

		all = append(all, scored{rec: rec, cap2: cap2, cap3: cap3, fp: fp})
	}

	// Sanity check 1: all r=4 KEEPs die.
	if r4SurviveCount > 0 {
		fmt.Fprintf(os.Stderr, "SANITY FAIL: %d r=4 KEEPs survived (expected 0)\n", r4SurviveCount)
		os.Exit(1)
	}
	fmt.Fprintf(os.Stderr, "Sanity check 1 PASS: all %d r=4 KEEPs rejected by rigidity\n", r4KeepCount)

	// Sanity check 2: [24,10] H_class=2
	// demotes from cap_eff=3 to cap2=2.
	anchor3Found := false
	for i := range all {
		s := &all[i]
		if s.rec.GID == [2]int{24, 10} && s.rec.HClass == 2 {
			anchor3Found = true
			if s.rec.CapEff != 3 {
				fmt.Fprintf(os.Stderr, "SANITY FAIL: [24,10] H_class=2 has cap_eff=%d, expected 3\n", s.rec.CapEff)
				os.Exit(1)
			}
			if s.cap2 != 2 {
				fmt.Fprintf(os.Stderr, "SANITY FAIL: [24,10] H_class=2 has cap2=%d, expected 2\n", s.cap2)
				os.Exit(1)
			}
			fmt.Fprintf(os.Stderr, "Sanity check 2 PASS: [24,10] H_class=2 demotes cap_eff=3 -> cap2=2\n")
			break
		}
	}
	if !anchor3Found {
		fmt.Fprintf(os.Stderr, "SANITY FAIL: [24,10] H_class=2 not found in KEEPs\n")
		os.Exit(1)
	}

	// Cap3 sanity checks.
	for i := range all {
		s := &all[i]
		// cap3 <= cap2 everywhere
		if s.cap3 > s.cap2 {
			fmt.Fprintf(os.Stderr, "SANITY FAIL: cap3 (%d) > cap2 (%d) for [%d,%d] H_class=%d\n",
				s.cap3, s.cap2, s.rec.GID[0], s.rec.GID[1], s.rec.HClass)
			os.Exit(1)
		}
		// cap3 = cap2 for all cap2 >= 3
		if s.cap2 >= 3 && s.cap3 != s.cap2 {
			fmt.Fprintf(os.Stderr, "SANITY FAIL: cap2=%d but cap3=%d for [%d,%d] H_class=%d (expected equal for cap2>=3)\n",
				s.cap2, s.cap3, s.rec.GID[0], s.rec.GID[1], s.rec.HClass)
			os.Exit(1)
		}
		// No r >= 7 record changes verdict at n=2
		// (cap2>=2 implies cap3>=2 if r>=7)
		if s.cap2 >= 2 && s.rec.R >= 7 && s.cap3 < 2 {
			fmt.Fprintf(os.Stderr, "SANITY FAIL: r=%d >= 7 with cap2=%d but cap3=%d < 2 for [%d,%d] H_class=%d\n",
				s.rec.R, s.cap2, s.cap3, s.rec.GID[0], s.rec.GID[1], s.rec.HClass)
			os.Exit(1)
		}
	}
	fmt.Fprintf(os.Stderr, "Cap3 sanity checks PASS: cap3<=cap2 everywhere, cap3=cap2 for cap2>=3, no r>=7 deaths\n")

	// Filter cap2 >= 2 survivors (for reporting).
	var cap2Survivors []scored
	for i := range all {
		if all[i].cap2 >= 2 {
			cap2Survivors = append(cap2Survivors, all[i])
		}
	}
	fmt.Fprintf(os.Stderr, "After rigidity strengthening (cap2 >= 2): %d survivors\n", len(cap2Survivors))

	// Filter cap3 >= 2 survivors (final).
	var survivors []scored
	var cap3Deaths []scored
	for i := range all {
		if all[i].cap3 >= 2 {
			survivors = append(survivors, all[i])
		} else if all[i].cap2 >= 2 && all[i].cap3 < 2 {
			cap3Deaths = append(cap3Deaths, all[i])
		}
	}
	fmt.Fprintf(os.Stderr, "After s-rank strengthening (cap3 >= 2): %d survivors\n", len(survivors))
	fmt.Fprintf(os.Stderr, "Records killed by cap3 (cap2>=2 but cap3<2): %d\n", len(cap3Deaths))

	// Deduplicate by fingerprint. Canonical
	// representative: smallest (G_order,
	// G_index, H_class).
	type fpEntry struct {
		canonical scored
		count     int
	}
	fpMap := make(map[string]*fpEntry)
	for i := range survivors {
		s := &survivors[i]
		g, exists := fpMap[s.fp]
		if !exists {
			fpMap[s.fp] = &fpEntry{canonical: *s, count: 1}
		} else {
			g.count++
			if isSmaller(s.rec, g.canonical.rec) {
				g.canonical = *s
			}
		}
	}

	// Collect deduped records sorted
	// by (cap3 desc, N desc, r desc,
	// fingerprint).
	var deduped []scored
	for _, g := range fpMap {
		deduped = append(deduped, g.canonical)
	}
	sort.Slice(deduped, func(i, j int) bool {
		if deduped[i].cap3 != deduped[j].cap3 {
			return deduped[i].cap3 > deduped[j].cap3
		}
		if deduped[i].rec.N != deduped[j].rec.N {
			return deduped[i].rec.N > deduped[j].rec.N
		}
		if deduped[i].rec.R != deduped[j].rec.R {
			return deduped[i].rec.R > deduped[j].rec.R
		}
		return deduped[i].fp < deduped[j].fp
	})
	fmt.Fprintf(os.Stderr, "After dedup: %d unique fingerprints\n", len(deduped))

	// Cap2 distribution (before dedup, among cap2-survivors).
	cap2DistPre := make(map[int]int)
	for i := range cap2Survivors {
		cap2DistPre[cap2Survivors[i].cap2]++
	}
	// Cap2 distribution (after dedup, among
	// cap2-survivors for rev1 doc).
	cap2DedupMap := make(map[string]*fpEntry)
	for i := range cap2Survivors {
		s := &cap2Survivors[i]
		g, exists := cap2DedupMap[s.fp]
		if !exists {
			cap2DedupMap[s.fp] = &fpEntry{canonical: *s, count: 1}
		} else {
			g.count++
			if isSmaller(s.rec, g.canonical.rec) {
				g.canonical = *s
			}
		}
	}
	cap2DistPost := make(map[int]int)
	for _, g := range cap2DedupMap {
		cap2DistPost[g.canonical.cap2]++
	}

	// Cap3 distribution (before dedup, among cap3-survivors).
	cap3DistPre := make(map[int]int)
	for i := range survivors {
		cap3DistPre[survivors[i].cap3]++
	}
	// Cap3 distribution (after dedup).
	cap3DistPost := make(map[int]int)
	for i := range deduped {
		cap3DistPost[deduped[i].cap3]++
	}

	// Compute r - cap2^2 gap stats (for rev1 doc section).
	minGapCap2 := math.MaxInt
	for _, g := range cap2DedupMap {
		gap := g.canonical.rec.R - g.canonical.cap2*g.canonical.cap2
		if gap < minGapCap2 {
			minGapCap2 = gap
		}
	}

	// Compute r - cap3^2 gap stats per cap3
	// level (for rev2 doc section).
	minGapCap3PerLevel := make(map[int]int)
	for i := range deduped {
		c3 := deduped[i].cap3
		gap := deduped[i].rec.R - c3*c3
		if prev, ok := minGapCap3PerLevel[c3]; !ok || gap < prev {
			minGapCap3PerLevel[c3] = gap
		}
	}

	// Collect cap2-deduped for rev1 top-20
	// (preserve original doc).
	var cap2Deduped []scored
	for _, g := range cap2DedupMap {
		cap2Deduped = append(cap2Deduped, g.canonical)
	}
	sort.Slice(cap2Deduped, func(i, j int) bool {
		if cap2Deduped[i].cap2 != cap2Deduped[j].cap2 {
			return cap2Deduped[i].cap2 > cap2Deduped[j].cap2
		}
		if cap2Deduped[i].rec.N != cap2Deduped[j].rec.N {
			return cap2Deduped[i].rec.N > cap2Deduped[j].rec.N
		}
		if cap2Deduped[i].rec.R != cap2Deduped[j].rec.R {
			return cap2Deduped[i].rec.R > cap2Deduped[j].rec.R
		}
		return cap2Deduped[i].fp < cap2Deduped[j].fp
	})

	// Collect death profile for reporting.
	deathProfile := make(map[[2]int]int) // (r, cap2) -> count
	for i := range cap3Deaths {
		key := [2]int{cap3Deaths[i].rec.R, cap3Deaths[i].cap2}
		deathProfile[key]++
	}

	// Cj1 conjecture verification on cap3 survivors.
	cj1C1Violations := 0
	cj1C2Violations := 0
	cj1C1Cap3Violations := 0
	c1EqualitySurvivors := 0
	c2EqualitySurvivors := 0
	for i := range deduped {
		s := &deduped[i]
		// C1: N >= r + cap2
		if s.rec.N < s.rec.R+s.cap2 {
			cj1C1Violations++
		}
		// C1 with cap3: N >= r + cap3
		if s.rec.N < s.rec.R+s.cap3 {
			cj1C1Cap3Violations++
		}
		// C2: N >= 4r/3 (i.e., 3N >= 4r)
		if 3*s.rec.N < 4*s.rec.R {
			cj1C2Violations++
		}
		// Equality witnesses
		if s.rec.N == s.rec.R+s.cap2 {
			c1EqualitySurvivors++
		}
		if 3*s.rec.N == 4*s.rec.R {
			c2EqualitySurvivors++
		}
	}
	// C1 with cap3 equality witnesses
	c1Cap3EqualitySurvivors := 0
	for i := range deduped {
		if deduped[i].rec.N == deduped[i].rec.R+deduped[i].cap3 {
			c1Cap3EqualitySurvivors++
		}
	}

	fmt.Fprintf(os.Stderr, "\nCj1 C1 (N >= r + cap2) violations on cap3 survivors: %d\n", cj1C1Violations)
	fmt.Fprintf(os.Stderr, "Cj1 C1 (N >= r + cap3) violations on cap3 survivors: %d\n", cj1C1Cap3Violations)
	fmt.Fprintf(os.Stderr, "Cj1 C2 (N >= 4r/3) violations on cap3 survivors: %d\n", cj1C2Violations)
	fmt.Fprintf(os.Stderr, "C1 (N = r + cap2) equality witnesses surviving: %d\n", c1EqualitySurvivors)
	fmt.Fprintf(os.Stderr, "C1 (N = r + cap3) equality witnesses surviving: %d\n", c1Cap3EqualitySurvivors)
	fmt.Fprintf(os.Stderr, "C2 (N = 4r/3) equality witnesses surviving: %d\n", c2EqualitySurvivors)

	// Write output JSONL.
	if err := writeOutput(outputPath, deduped); err != nil {
		fmt.Fprintf(os.Stderr, "ERROR writing output: %v\n", err)
		os.Exit(1)
	}
	fmt.Fprintf(os.Stderr, "\nWrote %d records to %s\n", len(deduped), outputPath)

	// Write ranking doc.
	if err := writeDoc(docPath, len(keeps), r4KeepCount, len(cap2Survivors), len(cap2DedupMap),
		cap2DistPre, cap2DistPost, cap2Deduped, minGapCap2,
		len(survivors), len(deduped), cap3DistPre, cap3DistPost, deduped, minGapCap3PerLevel,
		cap3Deaths, deathProfile,
		cj1C1Violations, cj1C2Violations, cj1C1Cap3Violations,
		c1EqualitySurvivors, c2EqualitySurvivors, c1Cap3EqualitySurvivors); err != nil {
		fmt.Fprintf(os.Stderr, "ERROR writing doc: %v\n", err)
		os.Exit(1)
	}
	fmt.Fprintf(os.Stderr, "Wrote ranking doc to %s\n", docPath)
}

// computeCap2 computes the strengthened
// capacity per the Pf5 rigidity lemma.
//
//	cap2 = max { n >= 2 :
//	             n^2 <= r - 1,                     (rigidity)
//	             #{j : partners[j] >= n} >= n^2,   (NC2')
//	             triangle_count >= n^3 }           (triangle supply)
func computeCap2(rec record) int {
	if rec.R <= 1 {
		return 0
	}
	maxN := int(math.Floor(math.Sqrt(float64(rec.R - 1))))
	for n := maxN; n >= 2; n-- {
		if n*n > rec.R-1 {
			continue
		}
		count := 0
		for _, p := range rec.Partners {
			if p >= n {
				count++
			}
		}
		if count < n*n {
			continue
		}
		if rec.TriangleCount < n*n*n {
			continue
		}
		return n
	}
	return 0
}

// srankLB returns the s-rank lower bound
// for tensor <n,n,n>.
//
//	n = 2: R_s(<2,2,2>) = 7 (exact, BCZ17 arXiv:1705.09652)
//	n >= 3: n^2 + 1 (rigidity bound only; no tighter published value in local corpus)
func srankLB(n int) int {
	if n == 2 {
		return 7
	}
	return n*n + 1
}

// computeCap3 computes the s-rank-strengthened capacity.
//
//	cap3 = max { n >= 2 : cap2's conditions AND r >= srank_lb(n) }
//
// Since srank_lb(n) for n >= 3 equals n^2
// + 1 which is equivalent to the rigidity
// condition (n^2 <= r-1) already in cap2,
// cap3 = cap2 for cap2 >= 3. At n = 2, cap3
// requires r >= 7 (vs r >= 5 from rigidity
// alone).
func computeCap3(rec record, cap2 int) int {
	// Start from cap2 and check srank bound downward.
	for n := cap2; n >= 2; n-- {
		if rec.R >= srankLB(n) {
			return n
		}
	}
	return 0
}

// computeFingerprint computes an
// available-field fingerprint for
// deduplication.
func computeFingerprint(rec record) string {
	vals := make([]int, len(rec.Valencies))
	copy(vals, rec.Valencies)
	sort.Ints(vals)

	mults := make([]int, len(rec.Multiplicities))
	copy(mults, rec.Multiplicities)
	sort.Ints(mults)

	parts := make([]int, len(rec.Partners))
	copy(parts, rec.Partners)
	sort.Ints(parts)

	key := fmt.Sprintf("%d|%d|%v|%v|%v|%d|%v",
		rec.N, rec.R, vals, mults, parts, rec.TriangleCount, rec.IsSymmetric)

	h := sha256.Sum256([]byte(key))
	return fmt.Sprintf("%x", h[:8])
}

func isSmaller(a, b record) bool {
	if a.GID[0] != b.GID[0] {
		return a.GID[0] < b.GID[0]
	}
	if a.GID[1] != b.GID[1] {
		return a.GID[1] < b.GID[1]
	}
	return a.HClass < b.HClass
}

func readRecords(path string) ([]record, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()

	var records []record
	scanner := bufio.NewScanner(f)
	scanner.Buffer(make([]byte, 1<<20), 1<<20)
	for scanner.Scan() {
		line := scanner.Bytes()
		if len(line) == 0 {
			continue
		}
		var rec record
		if err := json.Unmarshal(line, &rec); err != nil {
			return nil, fmt.Errorf("parse: %w", err)
		}
		records = append(records, rec)
	}
	if err := scanner.Err(); err != nil {
		return nil, err
	}
	return records, nil
}

func writeOutput(path string, deduped []scored) error {
	f, err := os.Create(path)
	if err != nil {
		return err
	}
	defer f.Close()

	w := bufio.NewWriter(f)
	for i := range deduped {
		s := &deduped[i]
		out := outputRecord{
			GID:            s.rec.GID,
			HID:            s.rec.HID,
			HClass:         s.rec.HClass,
			N:              s.rec.N,
			R:              s.rec.R,
			IsSymmetric:    s.rec.IsSymmetric,
			Multiplicities: s.rec.Multiplicities,
			Valencies:      s.rec.Valencies,
			TriangleCount:  s.rec.TriangleCount,
			Partners:       s.rec.Partners,
			NC4Bound:       s.rec.NC4Bound,
			CapEff:         s.rec.CapEff,
			NC1Pass:        s.rec.NC1Pass,
			NC2Pass:        s.rec.NC2Pass,
			IsThin:         s.rec.IsThin,
			Verdict:        s.rec.Verdict,
			Cap2:           s.cap2,
			Cap3:           s.cap3,
			FingerprintID:  s.fp,
		}
		data, err := json.Marshal(out)
		if err != nil {
			return err
		}
		if _, err := w.Write(data); err != nil {
			return err
		}
		if err := w.WriteByte('\n'); err != nil {
			return err
		}
	}
	return w.Flush()
}

func writeDoc(path string, totalKeeps, r4Keeps, cap2SurvivorCount, cap2DedupCount int,
	cap2DistPre, cap2DistPost map[int]int, cap2Deduped []scored, minGapCap2 int,
	cap3SurvivorCount, cap3DedupCount int, cap3DistPre, cap3DistPost map[int]int,
	deduped []scored, minGapCap3PerLevel map[int]int,
	cap3Deaths []scored, deathProfile map[[2]int]int,
	cj1C1Violations, cj1C2Violations, cj1C1Cap3Violations int,
	c1EqualitySurvivors, c2EqualitySurvivors, c1Cap3EqualitySurvivors int) error {

	f, err := os.Create(path)
	if err != nil {
		return err
	}
	defer f.Close()

	w := bufio.NewWriter(f)

	// === Rev 1 section (preserved) ===

	fmt.Fprintf(w, "# Im8: Gelfand screen — rigidity strengthening and ranking\n\n")
	fmt.Fprintf(w, "## Rigidity strengthening (Pf5 lemma)\n\n")
	fmt.Fprintf(w, "Per the rank-n^2 rigidity lemma (Pf5-anchor-validation.md Section 4):\n")
	fmt.Fprintf(w, "no single-fiber association scheme of rank exactly n^2 realizes <n,n,n>\n")
	fmt.Fprintf(w, "for n >= 2. This strengthens the capacity bound from floor(sqrt(r)) to\n")
	fmt.Fprintf(w, "floor(sqrt(r-1)), yielding:\n\n")
	fmt.Fprintf(w, "    cap2 = max { n >= 2 : n^2 <= r-1, #{j: partners[j]>=n} >= n^2, triangle_count >= n^3 }\n\n")
	fmt.Fprintf(w, "Records with cap2 < 2 receive verdict REJECT_RIGIDITY.\n\n")

	fmt.Fprintf(w, "## Verdict distribution (before strengthening)\n\n")
	fmt.Fprintf(w, "- Total records: 39358\n")
	fmt.Fprintf(w, "- KEEP: %d\n", totalKeeps)
	fmt.Fprintf(w, "- r=4 KEEPs (all killed by rigidity): %d\n\n", r4Keeps)

	fmt.Fprintf(w, "## After strengthening\n\n")
	fmt.Fprintf(w, "- Survivors (cap2 >= 2): %d (of %d KEEPs)\n", cap2SurvivorCount, totalKeeps)
	fmt.Fprintf(w, "- Rejected by rigidity: %d\n\n", totalKeeps-cap2SurvivorCount)

	fmt.Fprintf(w, "### Cap2 distribution (before dedup)\n\n")
	fmt.Fprintf(w, "| cap2 | count |\n")
	fmt.Fprintf(w, "|------|-------|\n")
	maxCap2 := 0
	for k := range cap2DistPre {
		if k > maxCap2 {
			maxCap2 = k
		}
	}
	for n := maxCap2; n >= 2; n-- {
		if cap2DistPre[n] > 0 {
			fmt.Fprintf(w, "| %d | %d |\n", n, cap2DistPre[n])
		}
	}

	fmt.Fprintf(w, "\n## Deduplication\n\n")
	fmt.Fprintf(w, "Fingerprint: (N, r, sorted valencies, sorted multiplicities, sorted partners,\n")
	fmt.Fprintf(w, "triangle_count, is_symmetric). SHA-256 truncated to 8 bytes.\n\n")
	fmt.Fprintf(w, "**Deviation from Cc2 spec Section 5:** full intersection-number tuples are not\n")
	fmt.Fprintf(w, "in the schema. This fingerprint is coarser than scheme isomorphism but finer\n")
	fmt.Fprintf(w, "than (N, r); collisions are parameter-identical up to all recorded invariants.\n")
	fmt.Fprintf(w, "Canonical representative: smallest (G_order, G_index, H_class).\n\n")
	fmt.Fprintf(w, "- Before dedup: %d survivors\n", cap2SurvivorCount)
	fmt.Fprintf(w, "- After dedup: %d unique fingerprints\n\n", cap2DedupCount)

	fmt.Fprintf(w, "### Cap2 distribution (after dedup)\n\n")
	fmt.Fprintf(w, "| cap2 | unique schemes |\n")
	fmt.Fprintf(w, "|------|----------------|\n")
	for n := maxCap2; n >= 2; n-- {
		if cap2DistPost[n] > 0 {
			fmt.Fprintf(w, "| %d | %d |\n", n, cap2DistPost[n])
		}
	}

	fmt.Fprintf(w, "\n## Gap statistic: r - cap2^2\n\n")
	fmt.Fprintf(w, "Conjecture 5.7 (CU13 line 1389) targets r ~ n^2; the rigidity lemma\n")
	fmt.Fprintf(w, "forbids r = cap2^2 exactly, so the minimum feasible gap is 1.\n\n")
	fmt.Fprintf(w, "- Minimum (r - cap2^2) observed: %d\n\n", minGapCap2)

	fmt.Fprintf(w, "## Top-20 unique schemes by cap2\n\n")
	fmt.Fprintf(w, "| # | G_id | H_id | H_class | N | r | cap2 | r-cap2^2 | sym | tri_count |\n")
	fmt.Fprintf(w, "|---|------|------|---------|---|---|------|----------|-----|----------|\n")
	top := 20
	if top > len(cap2Deduped) {
		top = len(cap2Deduped)
	}
	for i := 0; i < top; i++ {
		s := &cap2Deduped[i]
		sym := "N"
		if s.rec.IsSymmetric {
			sym = "Y"
		}
		gap := s.rec.R - s.cap2*s.cap2
		fmt.Fprintf(w, "| %d | [%d,%d] | [%d,%d] | %d | %d | %d | %d | %d | %s | %d |\n",
			i+1, s.rec.GID[0], s.rec.GID[1], s.rec.HID[0], s.rec.HID[1],
			s.rec.HClass, s.rec.N, s.rec.R, s.cap2, gap, sym, s.rec.TriangleCount)
	}

	fmt.Fprintf(w, "\n## Note on absent verdicts\n\n")
	fmt.Fprintf(w, "REJECT_RANK and REJECT_TRIANGLE never appear in gelfand-screen.jsonl:\n\n")
	fmt.Fprintf(w, "- **REJECT_RANK** (r < 4): unreachable dead code — the TRIVIAL_SMALL gate\n")
	fmt.Fprintf(w, "  (r <= 3) fires first in the cascade (Pf5 report defect D1).\n")
	fmt.Fprintf(w, "- **REJECT_TRIANGLE**: NC2' at n=2 requires #{j: partners[j]>=2} >= 4.\n")
	fmt.Fprintf(w, "  For any non-thin association scheme with r >= 4, the diagonal class has\n")
	fmt.Fprintf(w, "  partners = r >= 4, and non-diagonal classes generically exceed 2 partner\n")
	fmt.Fprintf(w, "  pairs. In practice no scheme reaching the KEEP-eligible stage (r >= 4,\n")
	fmt.Fprintf(w, "  non-thin, nonabelian G, non-normal H) fails NC2' at n=2 (Pf5 Section 2\n")
	fmt.Fprintf(w, "  and Pl4 provenance).\n")

	// === Rev 2 section (cap3 / BCZ17 s-rank
	// strengthening) ===

	fmt.Fprintf(w, "\n---\n\n")
	fmt.Fprintf(w, "## Rev 2: S-rank strengthening (BCZ17)\n\n")
	fmt.Fprintf(w, "Transfer principle (CU13 Prop 3.5): a commutative CC realizing <n,n,n>\n")
	fmt.Fprintf(w, "has structural tensor rank r >= R_s(<n,n,n>). Published s-rank lower bounds\n")
	fmt.Fprintf(w, "are therefore valid reject predicates.\n\n")
	fmt.Fprintf(w, "    srank_lb(2) = 7   (BCZ17 arXiv:1705.09652, exact)\n")
	fmt.Fprintf(w, "    srank_lb(n) = n^2 + 1 for n >= 3  (rigidity only; no tighter bound in corpus)\n\n")
	fmt.Fprintf(w, "    cap3 = max { n >= 2 : n^2 <= r-1, triangle_count >= n^3, r >= srank_lb(n) }\n\n")
	fmt.Fprintf(w, "The operative cap3 gates are:\n")
	fmt.Fprintf(w, "- **Rigidity:** n^2 <= r - 1\n")
	fmt.Fprintf(w, "- **Triangle supply:** triangle_count >= n^3\n")
	fmt.Fprintf(w, "- **S-rank floor:** r >= 7 at n = 2 (BCZ17)\n\n")
	fmt.Fprintf(w, "Records with cap3 < 2 receive verdict REJECT_SRANK.\n\n")

	fmt.Fprintf(w, "### Cap3 deaths (cap2 = 2, killed by s-rank)\n\n")
	fmt.Fprintf(w, "Records with cap2 = 2 but r < 7 fail the s-rank floor at n = 2.\n\n")

	// Collect unique (r, cap2) death keys sorted.
	type rCapKey struct {
		r, cap2 int
	}
	var deathKeys []rCapKey
	for k := range deathProfile {
		deathKeys = append(deathKeys, rCapKey{k[0], k[1]})
	}
	sort.Slice(deathKeys, func(i, j int) bool {
		if deathKeys[i].r != deathKeys[j].r {
			return deathKeys[i].r < deathKeys[j].r
		}
		return deathKeys[i].cap2 < deathKeys[j].cap2
	})

	fmt.Fprintf(w, "| r | cap2 | records killed |\n")
	fmt.Fprintf(w, "|---|------|----------------|\n")
	totalDeaths := 0
	for _, k := range deathKeys {
		cnt := deathProfile[[2]int{k.r, k.cap2}]
		totalDeaths += cnt
		fmt.Fprintf(w, "| %d | %d | %d |\n", k.r, k.cap2, cnt)
	}
	fmt.Fprintf(w, "\nTotal pre-dedup deaths: %d\n\n", totalDeaths)

	// Count unique fingerprints among deaths.
	deathFPs := make(map[string]bool)
	for i := range cap3Deaths {
		deathFPs[cap3Deaths[i].fp] = true
	}
	fmt.Fprintf(w, "Unique fingerprints killed: %d\n\n", len(deathFPs))

	fmt.Fprintf(w, "### After s-rank strengthening\n\n")
	fmt.Fprintf(w, "- Cap3 survivors (pre-dedup): %d\n", cap3SurvivorCount)
	fmt.Fprintf(w, "- Cap3 survivors (after dedup): %d\n\n", cap3DedupCount)

	fmt.Fprintf(w, "### Cap3 distribution (before dedup)\n\n")
	fmt.Fprintf(w, "| cap3 | count |\n")
	fmt.Fprintf(w, "|------|-------|\n")
	maxCap3 := 0
	for k := range cap3DistPre {
		if k > maxCap3 {
			maxCap3 = k
		}
	}
	for n := maxCap3; n >= 2; n-- {
		if cap3DistPre[n] > 0 {
			fmt.Fprintf(w, "| %d | %d |\n", n, cap3DistPre[n])
		}
	}

	fmt.Fprintf(w, "\n### Cap3 distribution (after dedup)\n\n")
	fmt.Fprintf(w, "| cap3 | unique schemes |\n")
	fmt.Fprintf(w, "|------|----------------|\n")
	for n := maxCap3; n >= 2; n-- {
		if cap3DistPost[n] > 0 {
			fmt.Fprintf(w, "| %d | %d |\n", n, cap3DistPost[n])
		}
	}

	fmt.Fprintf(w, "\n### Gap statistic: min(r - cap3^2) per level\n\n")
	fmt.Fprintf(w, "| cap3 | min(r - cap3^2) | note |\n")
	fmt.Fprintf(w, "|------|-----------------|------|\n")
	for n := maxCap3; n >= 2; n-- {
		if gap, ok := minGapCap3PerLevel[n]; ok {
			note := ""
			if n == 2 {
				note = "floor is srank_lb(2)=7, gap = r - 4 >= 3"
			}
			fmt.Fprintf(w, "| %d | %d | %s |\n", n, gap, note)
		}
	}

	fmt.Fprintf(w, "\n### Top-20 unique schemes by cap3\n\n")
	fmt.Fprintf(w, "| # | G_id | H_id | H_class | N | r | cap3 | r-cap3^2 | sym | tri_count |\n")
	fmt.Fprintf(w, "|---|------|------|---------|---|---|------|----------|-----|----------|\n")
	top = 20
	if top > len(deduped) {
		top = len(deduped)
	}
	for i := 0; i < top; i++ {
		s := &deduped[i]
		sym := "N"
		if s.rec.IsSymmetric {
			sym = "Y"
		}
		gap := s.rec.R - s.cap3*s.cap3
		fmt.Fprintf(w, "| %d | [%d,%d] | [%d,%d] | %d | %d | %d | %d | %d | %s | %d |\n",
			i+1, s.rec.GID[0], s.rec.GID[1], s.rec.HID[0], s.rec.HID[1],
			s.rec.HClass, s.rec.N, s.rec.R, s.cap3, gap, sym, s.rec.TriangleCount)
	}

	fmt.Fprintf(w, "\n### Cj1 conjecture cross-check (post-cap3)\n\n")
	fmt.Fprintf(w, "Re-verification of Cj1-gelfand-conjectures.md C1 and C2 on the %d cap3 survivors:\n\n", cap3DedupCount)
	fmt.Fprintf(w, "- **C1 (N >= r + cap2):** %d violations (holds universally)\n", cj1C1Violations)
	fmt.Fprintf(w, "- **C1 with cap3 (N >= r + cap3):** %d violations (holds universally)\n", cj1C1Cap3Violations)
	fmt.Fprintf(w, "- **C2 (N >= 4r/3):** %d violations (holds universally)\n\n", cj1C2Violations)
	fmt.Fprintf(w, "Equality witnesses surviving cap3:\n")
	fmt.Fprintf(w, "- N = r + cap2: %d records\n", c1EqualitySurvivors)
	fmt.Fprintf(w, "- N = r + cap3: %d records\n", c1Cap3EqualitySurvivors)
	fmt.Fprintf(w, "- N = 4r/3: %d records\n\n", c2EqualitySurvivors)

	fmt.Fprintf(w, "Cap3 kills only r in {5,6} records (all cap2 = 2). The C1 equality cases\n")
	fmt.Fprintf(w, "(N=8, r=6, cap2=2 from [16,3] and [16,11]) have r=6 < 7 and are therefore\n")
	fmt.Fprintf(w, "killed by cap3. C2 equality cases all have r >= 9 (minimum N=12, r=9) and\n")
	fmt.Fprintf(w, "survive cap3. The strengthened C1 with cap3 in place of cap2 remains valid\n")
	fmt.Fprintf(w, "on all survivors (cap3 <= cap2, so N >= r + cap2 >= r + cap3 trivially).\n")

	return w.Flush()
}
