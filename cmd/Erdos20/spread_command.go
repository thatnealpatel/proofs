package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"math/rand"
	"os"
	"sort"
	"time"
)

type row struct {
	ID         string  `json:"id"`
	Desc       string  `json:"desc"`
	K          int     `json:"k"`
	N          int     `json:"n"`
	Fcard      int     `json:"f_card"`
	RStar      float64 `json:"r_star"`
	WitnessZ   []int   `json:"witness_z"`
	WitnessFZ  int     `json:"witness_fz"`
	WitnessF   int     `json:"witness_total"`
	TauF       int     `json:"tau_f"`
	TauSF      int     `json:"tau_sf"`
	TauExact   bool    `json:"tau_exact"`
	TauFExact  bool    `json:"tau_f_exact"`
	TauSFExact bool    `json:"tau_sf_exact"`
	Ratio      float64 `json:"ratio"`
	Seed       int64   `json:"seed,omitempty"`
	GenParams  string  `json:"gen_params,omitempty"`
	Members    [][]int `json:"members,omitempty"`
	ShiftedMem [][]int `json:"shifted_members,omitempty"`
}

type output struct {
	GeneratedAt string `json:"generated_at"`
	Calibration struct {
		TauFamilyB     int  `json:"tau_familyB"`
		TauShifted     int  `json:"tau_shifted_familyB"`
		EndpointIsStar bool `json:"endpoint_is_full_star_012"`
		Passed         bool `json:"passed"`
	} `json:"calibration"`
	Verdict string `json:"verdict"`
	Killed  *row   `json:"killing_witness,omitempty"`
	Rows    []row  `json:"rows"`
}

const (
	killRStar = 4.0
	killRatio = 8.0
	memberCap = 30
)

func spreadCommand(args []string) error {
	fs := flag.NewFlagSet("spread", flag.ContinueOnError)
	fs.SetOutput(os.Stderr)
	fs.Usage = func() {
		fmt.Fprintln(fs.Output(), "Usage: Erdos20 spread [flags]")
		fs.PrintDefaults()
	}
	timeout := fs.Duration("timeout", 5*time.Minute, "computation timeout")
	seed := fs.Int64("seed", 1, "base RNG seed for the random portions of the zoo")
	out := fs.String("out", "data/erdos20/trackB/spread_defect.json", "output JSON path")
	if err := fs.Parse(args); err != nil {
		return err
	}
	if fs.NArg() != 0 {
		return fmt.Errorf("spread: unexpected arguments: %v", fs.Args())
	}
	if *timeout <= 0 {
		return fmt.Errorf("spread: timeout must be positive")
	}
	if *out == "" {
		return fmt.Errorf("spread: out must not be empty")
	}
	ctx, cancel := context.WithTimeout(context.Background(), *timeout)
	defer cancel()
	return runSpread(ctx, *seed, *out)
}

func runSpread(ctx context.Context, baseSeed int64, outPath string) error {
	var result output
	result.GeneratedAt = time.Now().UTC().Format(time.RFC3339)
	familyB := buildFamilyB()
	result.Calibration.TauFamilyB, _ = maxSunflowerBudgeted(familyB)
	shiftedB := shiftOneSweep(familyB, 20)
	result.Calibration.TauShifted, _ = maxSunflowerBudgeted(shiftedB)
	result.Calibration.EndpointIsStar = isFullStar(shiftedB, []int{0, 1, 2}, 17)
	result.Calibration.Passed = result.Calibration.TauFamilyB == 2 && result.Calibration.TauShifted == 17 && result.Calibration.EndpointIsStar
	fmt.Printf("calibration: tau(familyB)=%d tau(S(familyB))=%d endpointStar=%v passed=%v\n", result.Calibration.TauFamilyB, result.Calibration.TauShifted, result.Calibration.EndpointIsStar, result.Calibration.Passed)
	if !result.Calibration.Passed {
		return fmt.Errorf("calibration FAILED; refusing to proceed")
	}
	result.Rows = append(result.Rows, makeRow("familyB", "calibration witness (Counterexample.lean): 4-uniform Fin20, |F|=17", 4, 20, familyB))

	var killed *row
	addRow := func(candidate row) bool {
		result.Rows = append(result.Rows, candidate)
		if candidate.RStar >= killRStar && candidate.TauF > 0 && candidate.Ratio > killRatio && candidate.TauExact {
			copy := candidate
			killed = &copy
			return true
		}
		return false
	}

	for _, kn := range [][2]int{{3, 8}, {3, 12}, {4, 10}, {4, 14}, {5, 12}} {
		if ctx.Err() != nil {
			return finishSpread(ctx, &result, killed, outPath)
		}
		k, n := kn[0], kn[1]
		family := buildStar(k, n)
		if addRow(makeRow(fmt.Sprintf("star_k%d_n%d", k, n), fmt.Sprintf("full star: all %d-sets through element 0 on n=%d", k, n), k, n, family)) {
			goto done
		}
	}
	for _, kn := range [][2]int{{3, 8}, {4, 9}, {4, 11}} {
		if ctx.Err() != nil {
			return finishSpread(ctx, &result, killed, outPath)
		}
		k, n := kn[0], kn[1]
		family := buildCoSingleton(k, n)
		if addRow(makeRow(fmt.Sprintf("cosingleton_k%d_n%d", k, n), fmt.Sprintf("co-singleton: all %d-sets on n=%d avoiding element %d", k, n, n-1), k, n, family)) {
			goto done
		}
	}
	{
		rng := rand.New(rand.NewSource(baseSeed))
		index := 0
		for k := 3; k <= 5; k++ {
			for n := 10; n <= 20; n += 5 {
				maxSets := min(nChooseK(n, k), 400)
				for _, fraction := range []float64{0.1, 0.25, 0.5} {
					count := max(2, int(fraction*float64(maxSets)))
					for repetition := 0; repetition < 2; repetition++ {
						if ctx.Err() != nil {
							return finishSpread(ctx, &result, killed, outPath)
						}
						seed := baseSeed*1000 + int64(index)
						index++
						family := buildRandom(k, n, count, rng)
						candidate := makeRowSeeded(fmt.Sprintf("rand_k%d_n%d_m%d_r%d", k, n, len(family), repetition), fmt.Sprintf("random %d-uniform, n=%d, target |F|=%d", k, n, count), k, n, family, seed, fmt.Sprintf("k=%d n=%d target_m=%d frac=%.2f rep=%d", k, n, count, fraction, repetition))
						if addRow(candidate) {
							goto done
						}
					}
				}
			}
		}
	}
	for _, kn := range [][2]int{{3, 6}, {3, 7}, {4, 7}, {4, 8}} {
		if ctx.Err() != nil {
			return finishSpread(ctx, &result, killed, outPath)
		}
		k, n := kn[0], kn[1]
		for index, family := range searchHighRatioLowTau(ctx, k, n) {
			candidate := makeRow(fmt.Sprintf("extremal_k%d_n%d_%d", k, n, index), fmt.Sprintf("search-found tau<=2 high-inflation %d-uniform on n=%d", k, n), k, n, family)
			if addRow(candidate) {
				goto done
			}
		}
	}
	{
		for _, knm := range [][3]int{{3, 14, 5}, {3, 18, 6}, {4, 16, 6}, {4, 20, 7}, {5, 18, 7}, {5, 20, 8}} {
			if ctx.Err() != nil {
				return finishSpread(ctx, &result, killed, outPath)
			}
			k, n, count := knm[0], knm[1], knm[2]
			for repetition := 0; repetition < 3; repetition++ {
				if ctx.Err() != nil {
					return finishSpread(ctx, &result, killed, outPath)
				}
				seed := baseSeed*7000 + int64(k*100+n*10+repetition)
				rng := rand.New(rand.NewSource(seed))
				family, rstar := buildHighSpread(k, n, count, rng, killRStar)
				if family == nil {
					continue
				}
				candidate := makeRowSeeded(fmt.Sprintf("highspread_k%d_n%d_m%d_r%d", k, n, count, repetition), fmt.Sprintf("ALWZ-style high-spread (reject-until r*>=%.0f) %d-uniform n=%d target r*=%.3f", killRStar, k, n, rstar), k, n, family, seed, fmt.Sprintf("k=%d n=%d m=%d rep=%d reject_threshold=%.1f", k, n, count, repetition, killRStar))
				if addRow(candidate) {
					goto done
				}
			}
		}
	}
	{
		probes := [][3]int{{3, 22, 200}, {3, 24, 300}, {4, 20, 400}, {4, 22, 600}, {4, 24, 900}, {5, 22, 1300}, {5, 24, 1600}, {5, 25, 2000}}
		for _, probe := range probes {
			k, n, count := probe[0], probe[1], probe[2]
			for repetition := 0; repetition < 2; repetition++ {
				if ctx.Err() != nil {
					return finishSpread(ctx, &result, killed, outPath)
				}
				seed := baseSeed*9000 + int64(k*1000+n*10+repetition)
				rng := rand.New(rand.NewSource(seed))
				family := buildRandom(k, n, count, rng)
				candidate := makeRowSeeded(fmt.Sprintf("killprobe_k%d_n%d_m%d_r%d", k, n, count, repetition), fmt.Sprintf("kill-probe random %d-uniform n=%d |F|=%d (scaled past 4^k for r*>=4)", k, n, len(family)), k, n, family, seed, fmt.Sprintf("k=%d n=%d target_m=%d rep=%d", k, n, count, repetition))
				if addRow(candidate) {
					goto done
				}
			}
		}
	}

done:
	return finishSpread(ctx, &result, killed, outPath)
}

func finishSpread(ctx context.Context, result *output, killed *row, outPath string) error {
	if killed != nil {
		result.Verdict = "H DEAD"
		result.Killed = killed
	} else {
		maxR := 0.0
		for _, candidate := range result.Rows {
			if candidate.RStar < 1e9 && candidate.RStar > maxR {
				maxR = candidate.RStar
			}
		}
		if maxR < killRStar {
			result.Verdict = "INCONCLUSIVE"
		} else {
			result.Verdict = "H SUPPORTED"
		}
	}
	if ctx.Err() != nil {
		fmt.Fprintf(os.Stderr, "note: deadline reached; emitting partial results (%d rows)\n", len(result.Rows))
	}
	data, err := json.MarshalIndent(result, "", "  ")
	if err != nil {
		return fmt.Errorf("marshal output: %w", err)
	}
	if err := os.MkdirAll("data/erdos20/trackB", 0o755); err != nil {
		return fmt.Errorf("mkdir: %w", err)
	}
	if err := os.WriteFile(outPath, data, 0o644); err != nil {
		return fmt.Errorf("write %s: %w", outPath, err)
	}
	fmt.Printf("verdict: %s\nrows: %d\nwrote: %s\n", result.Verdict, len(result.Rows), outPath)
	reportExtremes(result)
	return nil
}

func reportExtremes(result *output) {
	if len(result.Rows) == 0 {
		return
	}
	byRatio := append([]row(nil), result.Rows...)
	sort.Slice(byRatio, func(i, j int) bool { return byRatio[i].Ratio > byRatio[j].Ratio })
	byR := append([]row(nil), result.Rows...)
	sort.Slice(byR, func(i, j int) bool {
		left, right := byR[i].RStar, byR[j].RStar
		if left >= 1e9 {
			left = 0
		}
		if right >= 1e9 {
			right = 0
		}
		return left > right
	})
	fmt.Printf("top ratio: %s ratio=%.3f r*=%.3f k=%d tau %d->%d\n", byRatio[0].ID, byRatio[0].Ratio, byRatio[0].RStar, byRatio[0].K, byRatio[0].TauF, byRatio[0].TauSF)
	fmt.Printf("top r*:    %s r*=%.3f ratio=%.3f k=%d tau %d->%d\n", byR[0].ID, byR[0].RStar, byR[0].Ratio, byR[0].K, byR[0].TauF, byR[0].TauSF)
}

func makeRow(id, description string, k, n int, family []uint) row {
	return makeRowSeeded(id, description, k, n, family, 0, "")
}

func makeRowSeeded(id, description string, k, n int, family []uint, seed int64, parameters string) row {
	family = sortFamily(family)
	spread := computeSpread(family)
	tauF, exactF := maxSunflowerBudgeted(family)
	shifted := shiftOneSweep(family, n)
	tauShifted, exactShifted := maxSunflowerBudgeted(shifted)
	ratio := 0.0
	if tauF > 0 {
		ratio = float64(tauShifted) / float64(tauF)
	}
	result := row{ID: id, Desc: description, K: k, N: n, Fcard: len(family), RStar: spread.RStar, WitnessZ: spread.WitnessZ, WitnessFZ: spread.FZcard, WitnessF: spread.Fcard, TauF: tauF, TauSF: tauShifted, TauExact: exactF && exactShifted, TauFExact: exactF, TauSFExact: exactShifted, Ratio: ratio, Seed: seed, GenParams: parameters}
	if len(family) <= memberCap || (spread.RStar >= killRStar && ratio > killRatio) {
		result.Members = familyToSets(family)
	}
	if (spread.RStar >= killRStar && ratio > killRatio) || ratio >= 4 {
		result.ShiftedMem = familyToSets(shifted)
	}
	return result
}

func isFullStar(family []uint, core []int, want int) bool {
	if len(family) != want {
		return false
	}
	coreMask := setToMask(core)
	for _, member := range family {
		if member&coreMask != coreMask {
			return false
		}
	}
	return true
}
