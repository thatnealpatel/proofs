// Command rho0 computes exact rho_0(G)
// = beta_0(G)/|G| for finite groups
// using bitset-based TPP (triple product
// property) search.
//
// Two modes:
//
//   - Toy (--toy): regression anchors and controls of order <= 32.
//     Asserts every computed rho_0 equals expected_rho0 exactly.
//     Cross-validates set-based and brute-force TPP checkers.
//     Completes in seconds.
//
//   - Full (default): entire manifest exported by forge/export_tpp.sage.
//     Per-target budget (--target-budget, default 2h) and global budget
//     (--global-budget). Timed-out targets emit lower bounds.
//
// Input: JSON files under --data-dir
// (default forge/out/tpp-data/), produced
// by the Sage exporter.
//
// Output: JSONL records
// to --output (default
// forge/out/rho0/rho0-results.jsonl).
// Resume skips IDs already present in the
// output file.
//
// Projected candidate spaces (from prototype log):
//
//	Order  24 (C2 wr C3):          ~150 candidates, < 1s
//	Order  64 (D8:D8):         ~673K candidates, ~0.2s
//	Order 160 (C2 wr C5):      ~163K candidates, ~1s (Go)
//	Order 384 (C2 wr C6):    ~123.7M candidates, ~minutes (Go, parallel)
//
// Mathematical reference: Murthy,
// arXiv:2602.15796, eqs 2.5-2.6.
package main

import (
	"bufio"
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"math/big"
	"os"
	"path/filepath"
	"runtime"
	"strings"
	"time"

	"patel.codes/proofs/cmd/sieve/internal/tpp"
)

func main() {
	var (
		toyMode      = flag.Bool("toy", false, "toy mode: order <= 32 targets only, cross-validate TPP")
		dataDir      = flag.String("data-dir", "", "path to exported JSON data (default: forge/out/tpp-data/)")
		output       = flag.String("output", "", "output JSONL path (default: forge/out/rho0/rho0-results.jsonl)")
		targetBudget = flag.Duration("target-budget", 2*time.Hour, "per-target time budget")
		globalBudget = flag.Duration("global-budget", 0, "global time budget (0 = unlimited)")
		workers      = flag.Int("workers", 0, "workers per target (0 = NumCPU)")
		targetID     = flag.String("target-id", "", "run only this target ID")
		dryRun       = flag.Bool("dry-run", false, "print manifest and projections, then exit")
		pilot        = flag.String("pilot", "", "run one target and project total runtime")
	)
	flag.Parse()

	// Resolve default paths relative to the
	// script's expected location.
	repoRoot := findRepoRoot()

	if *dataDir == "" {
		*dataDir = filepath.Join(repoRoot, "Scratch", "GroupSieve", "forge", "out", "tpp-data")
	}
	if *output == "" {
		*output = filepath.Join(repoRoot, "Scratch", "GroupSieve", "forge", "out", "rho0", "rho0-results.jsonl")
	}
	if *workers == 0 {
		*workers = runtime.NumCPU()
	}

	// Load manifest.
	manifest, err := tpp.LoadManifest(*dataDir)
	if err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}

	// Filter for toy mode.
	if *toyMode {
		var filtered []tpp.ManifestEntry
		for _, m := range manifest {
			if isToyTarget(m) {
				filtered = append(filtered, m)
			}
		}
		manifest = filtered
	}

	// Filter for specific target.
	if *targetID != "" {
		var filtered []tpp.ManifestEntry
		for _, m := range manifest {
			if m.ID == *targetID {
				filtered = append(filtered, m)
			}
		}
		if len(filtered) == 0 {
			fmt.Fprintf(os.Stderr, "error: target %q not found in manifest\n", *targetID)
			os.Exit(1)
		}
		manifest = filtered
	}

	// Pilot mode.
	if *pilot != "" {
		var found *tpp.ManifestEntry
		for _, m := range manifest {
			if m.ID == *pilot {
				m := m
				found = &m
				break
			}
		}
		if found == nil {
			fmt.Fprintf(os.Stderr, "error: pilot target %q not found\n", *pilot)
			os.Exit(1)
		}
		runPilot(*dataDir, *found, *workers)
		return
	}

	// Dry-run: print manifest info.
	if *dryRun {
		fmt.Println("=== rho0 dry-run ===")
		fmt.Printf("Data dir:       %s\n", *dataDir)
		fmt.Printf("Output:         %s\n", *output)
		fmt.Printf("Target budget:  %v\n", *targetBudget)
		fmt.Printf("Global budget:  %v\n", *globalBudget)
		fmt.Printf("Workers/target: %d\n", *workers)
		fmt.Printf("Targets:        %d\n", len(manifest))
		fmt.Println()
		for i, m := range manifest {
			exp := m.ExpRho0
			if exp == "" {
				exp = "?"
			}
			fmt.Printf("  [%d] %-40s cat=%-20s expected=%s\n",
				i+1, m.Description, m.Category, exp)
		}
		return
	}

	// Load completed IDs for resume.
	completed, err := loadCompletedIDs(*output)
	if err != nil {
		fmt.Fprintf(os.Stderr, "warning: reading existing results: %v\n", err)
	}

	// Open output file for appending.
	if err := os.MkdirAll(filepath.Dir(*output), 0o755); err != nil {
		fmt.Fprintf(os.Stderr, "error: create output dir: %v\n", err)
		os.Exit(1)
	}
	outFile, err := os.OpenFile(*output, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0o644)
	if err != nil {
		fmt.Fprintf(os.Stderr, "error: open output: %v\n", err)
		os.Exit(1)
	}
	defer outFile.Close()

	// Global context with optional budget.
	ctx := context.Background()
	if *globalBudget > 0 {
		var cancel context.CancelFunc
		ctx, cancel = context.WithTimeout(ctx, *globalBudget)
		defer cancel()
	}

	nTotal := len(manifest)
	nSkipped := 0
	nFailed := 0

	fmt.Println(strings.Repeat("=", 70))
	fmt.Println("rho0 -- Exact subgroup TPP ratio engine (Go)")
	fmt.Printf("Targets: %d total, %d already done\n", nTotal, len(completed))
	fmt.Printf("Per-target budget: %v, Workers: %d\n", *targetBudget, *workers)
	fmt.Printf("Toy mode: %v, Cross-validate: %v\n", *toyMode, *toyMode)
	fmt.Println(strings.Repeat("=", 70))
	fmt.Println()

	for i, m := range manifest {
		select {
		case <-ctx.Done():
			fmt.Printf("\nGlobal budget exceeded. Stopping.\n")
			goto done
		default:
		}

		if _, ok := completed[m.ID]; ok {
			nSkipped++
			continue
		}

		fmt.Printf("[%d/%d] %s\n", i+1, nTotal, m.Description)

		result := runTarget(ctx, *dataDir, m, *targetBudget, *workers, *toyMode)

		// Write JSONL record.
		rec, err := json.Marshal(result)
		if err != nil {
			fmt.Fprintf(os.Stderr, "  ERROR marshaling result: %v\n", err)
			nFailed++
			continue
		}
		if _, err := fmt.Fprintf(outFile, "%s\n", rec); err != nil {
			fmt.Fprintf(os.Stderr, "  ERROR writing result: %v\n", err)
			nFailed++
			continue
		}
		if err := outFile.Sync(); err != nil {
			fmt.Fprintf(os.Stderr, "  WARNING: fsync failed: %v\n", err)
		}

		// Report.
		status := "DONE"
		if result.TimedOut {
			status = "TIMEOUT (lower bound)"
		}
		if result.Error != "" {
			status = "ERROR: " + result.Error
			nFailed++
		}

		matchStr := ""
		if *toyMode && result.ExpectedRho0 != "" && result.Error == "" {
			if rationalEqual(result.Rho0Exact, result.ExpectedRho0) {
				matchStr = " [MATCH]"
			} else {
				matchStr = fmt.Sprintf(" [MISMATCH expected=%s]", result.ExpectedRho0)
				nFailed++
			}
		}

		fmt.Printf("  %s: rho_0 = %s (%.6f), triple type %v, %.1fs%s\n",
			status, result.Rho0Exact, result.Rho0Float,
			result.AchievingTriple, result.RuntimeSeconds, matchStr)
		fmt.Println()
	}

done:
	fmt.Println(strings.Repeat("=", 70))
	fmt.Printf("Done. %d skipped (resume), %d failed.\n", nSkipped, nFailed)
	fmt.Printf("Results: %s\n", *output)
	fmt.Println(strings.Repeat("=", 70))

	if nFailed > 0 {
		os.Exit(1)
	}
}

func runTarget(ctx context.Context, dataDir string, m tpp.ManifestEntry, budget time.Duration, workers int, crossValidate bool) tpp.Result {
	path := tpp.GroupPath(dataDir, m.ID)
	g, err := tpp.LoadGroup(path)
	if err != nil {
		return tpp.Result{
			ID:           m.ID,
			Description:  m.Description,
			Category:     m.Category,
			ExpectedRho0: m.ExpRho0,
			Error:        err.Error(),
			Semantics:    "error",
		}
	}

	fmt.Printf("  Order: %d, %d classes, %d subgroups\n",
		g.N, len(g.Classes), len(g.Subgroups))

	tctx, cancel := context.WithTimeout(ctx, budget)
	defer cancel()

	cfg := tpp.SearchConfig{
		CrossValidate:    crossValidate,
		Workers:          workers,
		ProgressInterval: 30 * time.Second,
		Progress: func(msg string) {
			fmt.Println(msg)
		},
	}

	return tpp.Search(tctx, g, cfg)
}

func runPilot(dataDir string, m tpp.ManifestEntry, workers int) {
	fmt.Printf("=== Pilot: %s ===\n", m.Description)

	path := tpp.GroupPath(dataDir, m.ID)
	g, err := tpp.LoadGroup(path)
	if err != nil {
		fmt.Fprintf(os.Stderr, "error loading %s: %v\n", m.ID, err)
		os.Exit(1)
	}

	fmt.Printf("Order: %d, %d classes, %d subgroups\n",
		g.N, len(g.Classes), len(g.Subgroups))

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Minute)
	defer cancel()

	cfg := tpp.SearchConfig{
		Workers:          workers,
		ProgressInterval: 10 * time.Second,
		Progress: func(msg string) {
			fmt.Println(msg)
		},
	}

	result := tpp.Search(ctx, g, cfg)
	fmt.Printf("\nPilot result: rho_0 = %s, %.1fs, %d TPP checks, timed_out=%v\n",
		result.Rho0Exact, result.RuntimeSeconds, result.Stats.NTPPChecks, result.TimedOut)

	if result.Stats.NCandidates > 0 && result.RuntimeSeconds > 0 {
		rate := float64(result.Stats.NTPPChecks) / result.RuntimeSeconds
		fmt.Printf("Rate: %.0f TPP checks/sec\n", rate)
		fmt.Printf("Projected full time for this target: %.1f min\n",
			float64(result.Stats.NCandidates)/rate/60)
	}
}

func isToyTarget(m tpp.ManifestEntry) bool {
	// Toy mode: regression anchors and
	// controls of order <= 32. We parse the
	// description to check order. A more
	// robust approach would be to load the
	// JSON, but we want to avoid that for
	// dry-run.
	switch m.Category {
	case "regression_anchor":
		// Include anchors of order <= 32.
		return isOrderAtMost(m.ID, 32)
	case "kill_test_control":
		return isOrderAtMost(m.ID, 32)
	}
	return false
}

func isOrderAtMost(id string, maxOrder int) bool {
	// Parse order from ID format: "N_M" or "ctrl_N_M".
	parts := strings.Split(id, "_")
	for _, p := range parts {
		if n := parseInt(p); n > 0 && n <= maxOrder {
			return true
		}
	}
	// For IDs like "24_10", the first part is the order.
	if len(parts) >= 2 {
		if n := parseInt(parts[0]); n > 0 {
			return n <= maxOrder
		}
	}
	if len(parts) >= 3 && parts[0] == "ctrl" {
		if n := parseInt(parts[1]); n > 0 {
			return n <= maxOrder
		}
	}
	return false
}

func parseInt(s string) int {
	n := 0
	for _, c := range s {
		if c < '0' || c > '9' {
			return 0
		}
		n = n*10 + int(c-'0')
	}
	if len(s) == 0 {
		return 0
	}
	return n
}

func loadCompletedIDs(path string) (map[string]struct{}, error) {
	m := map[string]struct{}{}
	f, err := os.Open(path)
	if err != nil {
		if os.IsNotExist(err) {
			return m, nil
		}
		return m, err
	}
	defer f.Close()

	scanner := bufio.NewScanner(f)
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line == "" {
			continue
		}
		var rec struct {
			ID string `json:"id"`
		}
		if err := json.Unmarshal([]byte(line), &rec); err != nil {
			continue
		}
		if rec.ID != "" {
			m[rec.ID] = struct{}{}
		}
	}
	return m, scanner.Err()
}

func rationalEqual(a, b string) bool {
	ra, ok1 := parseRational(a)
	rb, ok2 := parseRational(b)
	if !ok1 || !ok2 {
		return a == b
	}
	// a.P/a.Q == b.P/b.Q <=> a.P*b.Q == b.P*a.Q
	lhs := new(big.Int).Mul(big.NewInt(ra.P), big.NewInt(rb.Q))
	rhs := new(big.Int).Mul(big.NewInt(rb.P), big.NewInt(ra.Q))
	return lhs.Cmp(rhs) == 0
}

func parseRational(s string) (tpp.Rational, bool) {
	parts := strings.SplitN(s, "/", 2)
	if len(parts) == 1 {
		n := parseInt(parts[0])
		if n == 0 && parts[0] != "0" {
			return tpp.Rational{}, false
		}
		return tpp.Rational{P: int64(n), Q: 1}, true
	}
	p := parseInt(parts[0])
	q := parseInt(parts[1])
	if q == 0 {
		return tpp.Rational{}, false
	}
	return tpp.Rational{P: int64(p), Q: int64(q)}, true
}

func findRepoRoot() string {
	// Walk up from cwd or executable looking for go.mod.
	dir, err := os.Getwd()
	if err != nil {
		return "."
	}
	for {
		if _, err := os.Stat(filepath.Join(dir, "go.mod")); err == nil {
			return dir
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			return "."
		}
		dir = parent
	}
}
