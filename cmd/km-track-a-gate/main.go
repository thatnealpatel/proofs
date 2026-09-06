package main

import (
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"os"
	"runtime"
	"slices"
	"time"

	"patel.codes/proofs/internal/ring"
	"patel.codes/proofs/internal/tensor"
)

const (
	c659Path = "cmd/c659-plusflip-cert/testdata/4x4x4_m47_c659_iteration5551_Z2.txt"
	c680Path = "cmd/c659-plusflip-cert/testdata/4x4x4_m47_c680_iteration4356_Z2.txt"
)

type triple [3]uint16

type stateSpec struct {
	ID       string
	Role     string
	Expected string
	Scheme   tensor.Scheme
}

type phaseTiming struct {
	Phase   string `json:"phase"`
	Elapsed string `json:"elapsed"`
}

type checks struct {
	Brent    bool `json:"brent"`
	Nonzero  bool `json:"nonzero"`
	Distinct bool `json:"distinct"`
}

type fixtureBinding struct {
	ID                   string `json:"id"`
	RawBytes             int    `json:"raw_bytes,omitempty"`
	RawSHA256            string `json:"raw_sha256,omitempty"`
	OrderedPayloadBytes  int    `json:"ordered_factor_major_payload_bytes"`
	OrderedPayloadSHA256 string `json:"ordered_factor_major_payload_sha256"`
	CanonicalSHA256      string `json:"canonical_sha256"`
	Authenticated        bool   `json:"authenticated"`
	Construction         string `json:"construction"`
}

type classRecord struct {
	SharedMode             int      `json:"shared_mode"`
	Slots                  []int    `json:"slots"`
	ComplementaryRank      int      `json:"complementary_rank"`
	Defect                 int      `json:"defect"`
	ReductionEndpoint      string   `json:"reduction_endpoint_sha256,omitempty"`
	ReductionInsertedTerms []triple `json:"reduction_inserted_terms,omitempty"`
}

type candidateRecord struct {
	Orientation        kmOrientation `json:"orientation"`
	PivotSlot          int           `json:"pivot_slot"`
	SourceSlots        []int         `json:"source_slots"`
	Arity              int           `json:"arity"`
	ChangedIndices     []int         `json:"changed_indices"`
	ChangedCount       int           `json:"changed_count"`
	PredictedLengthMin int           `json:"predicted_compiled_length_min"`
	PredictedLengthMax int           `json:"predicted_compiled_length_max"`
	Pivot              triple        `json:"pivot"`
	Sources            []triple      `json:"sources"`
	Targets            []triple      `json:"targets"`
}

type stateReport struct {
	ID         string               `json:"id"`
	Role       string               `json:"role"`
	TermCount  int                  `json:"term_count"`
	Canonical  string               `json:"canonical_sha256"`
	Checks     checks               `json:"checks"`
	Indexes    []kmOrientationIndex `json:"orientation_indexes"`
	Scans      []kmArityScan        `json:"arity_scans"`
	Candidates []candidateRecord    `json:"accepted_candidates"`
	Classes    []classRecord        `json:"shared_factor_analysis"`
}

type regressionRecord struct {
	StateID                 string          `json:"state_id"`
	Candidate               candidateRecord `json:"candidate"`
	Primitive               string          `json:"primitive"`
	ChangedNativeMode       int             `json:"changed_native_mode"`
	CommonNativeModes       []int           `json:"common_native_modes"`
	ReplayConstructorMode   int             `json:"replay_constructor_shared_mode"`
	ReplaySlots             []int           `json:"replay_slots"`
	ReplayEndpointSHA256    string          `json:"replay_endpoint_sha256"`
	ExpectedRootSHA256      string          `json:"expected_root_sha256"`
	IndependentReplayPassed bool            `json:"independent_replay_passed"`
}

type gateReport struct {
	Schema        string `json:"schema"`
	Configuration struct {
		MaximumArity     int    `json:"maximum_arity"`
		K                int    `json:"k"`
		Altitude         int    `json:"altitude"`
		Deadline         string `json:"deadline"`
		MemoryCapBytes   uint64 `json:"memory_cap_bytes"`
		OrientationOrder string `json:"orientation_order"`
		SubsetOrder      string `json:"subset_order"`
	} `json:"configuration"`
	Fixtures   []fixtureBinding `json:"fixtures"`
	States     []stateReport    `json:"states"`
	Regression regressionRecord `json:"c567_regression"`
	Gate       struct {
		Criterion                       string `json:"criterion"`
		BroadCandidates                 int    `json:"broad_candidates"`
		CandidatesNotSubsumedByAnalyzer int    `json:"candidates_not_subsumed_by_analyzer"`
		Decision                        string `json:"decision"`
		CompilerOrSearchImplemented     bool   `json:"compiler_or_search_implemented"`
		Conclusion                      string `json:"conclusion"`
		Scope                           string `json:"scope"`
	} `json:"gate"`
	Timings        []phaseTiming `json:"timings"`
	PeakAllocBytes uint64        `json:"observed_peak_alloc_bytes"`
	PeakSysBytes   uint64        `json:"observed_peak_sys_bytes"`
	Status         struct {
		Complete          bool `json:"complete"`
		DeadlineExceeded  bool `json:"deadline_exceeded"`
		MemoryCapExceeded bool `json:"memory_cap_exceeded"`
	} `json:"status"`
}

func main() {
	if err := run(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}

func run() error {
	ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
	defer cancel()
	started := time.Now()
	report := gateReport{Schema: "patel.codes/proofs/km-track-a-gate/v1"}
	report.Configuration.MaximumArity = 5
	report.Configuration.K = 1
	report.Configuration.Altitude = 48
	report.Configuration.Deadline = "60s"
	report.Configuration.MemoryCapBytes = 4 << 30
	report.Configuration.OrientationOrder = "all six lexicographically ordered native role assignments (b,c,a): (0,1,2),(0,2,1),(1,0,2),(1,2,0),(2,0,1),(2,1,0)"
	report.Configuration.SubsetOrder = "orientation, arity 1..5, common-factor class first-slot order, pivot slot, lexicographic source-slot combination"
	peakAlloc, peakSys := uint64(0), uint64(0)
	observe := func() error {
		var memory runtime.MemStats
		runtime.ReadMemStats(&memory)
		peakAlloc = max(peakAlloc, memory.Alloc)
		peakSys = max(peakSys, memory.Sys)
		if memory.Alloc > report.Configuration.MemoryCapBytes {
			return fmt.Errorf("memory cap exceeded: allocated %d bytes", memory.Alloc)
		}
		select {
		case <-ctx.Done():
			return ctx.Err()
		default:
			return nil
		}
	}

	phase := time.Now()
	c659, c659Binding, err := loadRoot(c659Path, "c659-root", 4524, "25f47b5f37d2b7351dd5a2c5da65ff8ef5ba80ce53239d46cdfdef37e6eef403", "f61518b4864995fe5ba43f1b52819cc563c4c74326442ae12bbc338a491027cb", "f2edf6735401e203b532cc85e0783fb47684815a3207b3ec601f8503c48956d1")
	if err != nil {
		return err
	}
	c680, c680Binding, err := loadRoot(c680Path, "c680-root", 4524, "7e65a2fa888fcd9f32d9d68fd21ab8cdafeb4a39300cc77882def8e0115483e8", "f6e3264df6e1a8c39c0af212c0ee0b490c7d96b0169c21b131b4c496fe04889b", "021266950ca5db9dd40593da2ec85d043469c1a15c66a04a06c2dbe23813c598")
	if err != nil {
		return err
	}
	report.Fixtures = append(report.Fixtures, c659Binding, c680Binding)
	report.Timings = append(report.Timings, phaseTiming{Phase: "authenticate_roots", Elapsed: time.Since(phase).String()})
	if err := observe(); err != nil {
		return err
	}

	phase = time.Now()
	plus, err := constructPlus(c659)
	if err != nil {
		return err
	}
	plusBinding, err := bindConstructed("c659-plus-child", plus, "oriented Plus on root slots (7,13), orientation (0,2,1)", "0001430818e501c6964f6bf666e52a72cd0514605b3c69460e0d09cf80ec48e9")
	if err != nil {
		return err
	}
	report.Fixtures = append(report.Fixtures, plusBinding)
	descriptors := []struct {
		first, second, mode int
		hash                string
	}{
		{45, 47, 0, "640392811b97cf64b2ccf0c382666ba1ea2b91b859f815d0c957574378da8c90"},
		{46, 47, 2, "c567254223d480d8eaecde19d24f0aa96792208c41e2101a1270937bf1fe2934"},
		{47, 45, 0, "ee02607028804b19dbb6c075d2d290386dcb309cf740b826569b64550ebdddf0"},
		{47, 46, 2, "cbf85f130f4bf6decd79785c85112135ab8e55a8aa745188383aeaa541171351"},
	}
	states := []stateSpec{
		{ID: "c659-root", Role: "zero-activation-control", Expected: c659Binding.CanonicalSHA256, Scheme: c659},
		{ID: "c680-root", Role: "zero-activation-control", Expected: c680Binding.CanonicalSHA256, Scheme: c680},
		{ID: "c659-plus-child", Role: "activation-corpus", Expected: plusBinding.CanonicalSHA256, Scheme: plus},
	}
	for index, descriptor := range descriptors {
		replacement, err := tensor.NewOrdinaryFlipReplacement(plus, tensor.SharedMode(descriptor.mode), descriptor.first, descriptor.second, 1)
		if err != nil {
			return fmt.Errorf("construct flip output %d: %w", index, err)
		}
		child, err := tensor.ApplyReplacement(plus, replacement)
		if err != nil {
			return fmt.Errorf("apply flip output %d: %w", index, err)
		}
		id := fmt.Sprintf("flip-output-%d", index+1)
		construction := fmt.Sprintf("tensor.NewOrdinaryFlipReplacement(%d,%d,shared-mode=%d,coefficient=1)", descriptor.first, descriptor.second, descriptor.mode)
		binding, err := bindConstructed(id, child, construction, descriptor.hash)
		if err != nil {
			return err
		}
		report.Fixtures = append(report.Fixtures, binding)
		states = append(states, stateSpec{ID: id, Role: "activation-corpus", Expected: descriptor.hash, Scheme: child})
	}
	report.Timings = append(report.Timings, phaseTiming{Phase: "reconstruct_corpus", Elapsed: time.Since(phase).String()})
	if err := observe(); err != nil {
		return err
	}

	phase = time.Now()
	broad := 0
	for _, state := range states {
		stateResult, err := scanState(state)
		if err != nil {
			return err
		}
		for _, candidate := range stateResult.Candidates {
			if candidate.Arity >= 2 && candidate.ChangedCount >= 2 && candidate.PredictedLengthMin >= 2 {
				broad++
			}
		}
		report.States = append(report.States, stateResult)
		if err := observe(); err != nil {
			return err
		}
	}
	report.Timings = append(report.Timings, phaseTiming{Phase: "scan_and_cross_check", Elapsed: time.Since(phase).String()})

	phase = time.Now()
	regression, err := replayC567Regression(states)
	if err != nil {
		return err
	}
	report.Regression = regression
	report.Timings = append(report.Timings, phaseTiming{Phase: "independent_c567_replay", Elapsed: time.Since(phase).String()})

	report.Gate.Criterion = "GO iff an admissible candidate has n>=2, changed count m>=2, predicted native compiled-length lower bound m>=2, and endpoint/path payoff not already supplied by AnalyzeSharedFactors/NewSharedFactorReduction"
	report.Gate.BroadCandidates = broad
	report.Gate.CandidatesNotSubsumedByAnalyzer = 0
	report.Gate.CompilerOrSearchImplemented = false
	report.Gate.Scope = "exact authenticated seven-state corpus only; finite negative scan evidence is not an impossibility theorem"
	if broad == 0 {
		report.Gate.Decision = "NO_GO_CLOSE_TRACK_A_FOR_THIS_CORPUS"
		report.Gate.Conclusion = "no accepted broad indexed-KM candidate occurs through arity 5; the accepted c567 n=1,m=1 case is exactly a native directed Reduction already replayed by the shared-factor API"
	} else {
		return fmt.Errorf("gate unexpectedly activated with %d broad candidates; payoff classification requires renewal", broad)
	}
	report.PeakAllocBytes = peakAlloc
	report.PeakSysBytes = peakSys
	report.Status.Complete = true
	report.Status.DeadlineExceeded = false
	report.Status.MemoryCapExceeded = false
	report.Timings = append(report.Timings, phaseTiming{Phase: "total", Elapsed: time.Since(started).String()})

	encoder := json.NewEncoder(os.Stdout)
	encoder.SetIndent("", "  ")
	if err := encoder.Encode(report); err != nil {
		return fmt.Errorf("encode report: %w", err)
	}
	return nil
}

func loadRoot(path, id string, expectedBytes int, expectedRaw, expectedOrdered, expectedCanonical string) (tensor.Scheme, fixtureBinding, error) {
	raw, err := os.ReadFile(path)
	if err != nil {
		return tensor.Scheme{}, fixtureBinding{}, fmt.Errorf("read %s: %w", id, err)
	}
	if len(raw) != expectedBytes || hash(raw) != expectedRaw {
		return tensor.Scheme{}, fixtureBinding{}, fmt.Errorf("authenticate %s raw bytes", id)
	}
	scheme, err := tensor.ParseNative(ring.Z2, bytes.NewReader(raw))
	if err != nil {
		return tensor.Scheme{}, fixtureBinding{}, fmt.Errorf("parse %s: %w", id, err)
	}
	ordered, err := encodeScheme(scheme, false)
	if err != nil {
		return tensor.Scheme{}, fixtureBinding{}, err
	}
	canonical, err := encodeScheme(scheme, true)
	if err != nil {
		return tensor.Scheme{}, fixtureBinding{}, err
	}
	if hash(ordered) != expectedOrdered || hash(canonical) != expectedCanonical {
		return tensor.Scheme{}, fixtureBinding{}, fmt.Errorf("authenticate %s encoded payloads", id)
	}
	return scheme, fixtureBinding{
		ID: id, RawBytes: len(raw), RawSHA256: hash(raw), OrderedPayloadBytes: len(ordered),
		OrderedPayloadSHA256: hash(ordered), CanonicalSHA256: hash(canonical), Authenticated: true,
		Construction: "tensor.ParseNative from committed c659-plusflip-cert fixture",
	}, nil
}

func bindConstructed(id string, scheme tensor.Scheme, construction, expectedCanonical string) (fixtureBinding, error) {
	ordered, err := encodeScheme(scheme, false)
	if err != nil {
		return fixtureBinding{}, err
	}
	canonical, err := encodeScheme(scheme, true)
	if err != nil {
		return fixtureBinding{}, err
	}
	if hash(canonical) != expectedCanonical {
		return fixtureBinding{}, fmt.Errorf("%s canonical SHA-256 is %s, want %s", id, hash(canonical), expectedCanonical)
	}
	binding := fixtureBinding{
		ID: id, OrderedPayloadBytes: len(ordered), OrderedPayloadSHA256: hash(ordered),
		CanonicalSHA256: hash(canonical), Authenticated: true, Construction: construction,
	}
	if id == "flip-output-2" {
		var raw bytes.Buffer
		if err := tensor.WriteNative(&raw, scheme); err != nil {
			return fixtureBinding{}, err
		}
		if raw.Len() != 4617 || hash(raw.Bytes()) != "7c58efce483b4825c7b6e4068b621355fecb48e0140331cc7884c9b2505e6839" || len(ordered) != 296 || hash(ordered) != "d92fa0e6a90c6bf609b6e0731671e4ab26d5e8d68b9478b2af5ea5c14e5be01f" {
			return fixtureBinding{}, fmt.Errorf("authenticate natural c567 serialization")
		}
		binding.RawBytes = raw.Len()
		binding.RawSHA256 = hash(raw.Bytes())
	}
	return binding, nil
}

func constructPlus(root tensor.Scheme) (tensor.Scheme, error) {
	orientation := [3]int{0, 2, 1}
	oriented := make([]tensor.RankOneTerm, 2)
	for i, slot := range []int{7, 13} {
		term := root.Term(slot)
		var err error
		oriented[i], err = tensor.NewRankOneTerm(term.Factor(orientation[0]), term.Factor(orientation[1]), term.Factor(orientation[2]))
		if err != nil {
			return tensor.Scheme{}, err
		}
	}
	temporary, err := tensor.NewScheme(oriented)
	if err != nil {
		return tensor.Scheme{}, err
	}
	plus, err := tensor.NewPlusReplacement(temporary, 0, 1)
	if err != nil {
		return tensor.Scheme{}, err
	}
	inserted := make([]tensor.RankOneTerm, 3)
	for i, term := range plus.InsertedTerms() {
		factors := [3]tensor.Matrix{}
		for orientedMode, nativeMode := range orientation {
			factors[nativeMode] = term.Factor(orientedMode)
		}
		inserted[i], err = tensor.NewRankOneTerm(factors[0], factors[1], factors[2])
		if err != nil {
			return tensor.Scheme{}, err
		}
	}
	replacement, err := tensor.NewReplacement([]int{7, 13}, inserted)
	if err != nil {
		return tensor.Scheme{}, err
	}
	if err := tensor.ValidateReplacement(root, replacement); err != nil {
		return tensor.Scheme{}, err
	}
	return tensor.ApplyReplacement(root, replacement)
}

func scanState(state stateSpec) (stateReport, error) {
	canonical, err := encodeScheme(state.Scheme, true)
	if err != nil {
		return stateReport{}, err
	}
	if hash(canonical) != state.Expected {
		return stateReport{}, fmt.Errorf("state %s hash changed", state.ID)
	}
	result := stateReport{ID: state.ID, Role: state.Role, TermCount: state.Scheme.TermCount(), Canonical: hash(canonical)}
	if err := tensor.ValidateBrent(state.Scheme); err != nil {
		return stateReport{}, fmt.Errorf("%s Brent: %w", state.ID, err)
	}
	result.Checks.Brent = true
	if err := tensor.ValidateNonzeroTerms(state.Scheme); err != nil {
		return stateReport{}, fmt.Errorf("%s nonzero: %w", state.ID, err)
	}
	result.Checks.Nonzero = true
	if err := tensor.ValidateDistinctTensors(state.Scheme); err != nil {
		return stateReport{}, fmt.Errorf("%s distinct: %w", state.ID, err)
	}
	result.Checks.Distinct = true
	scan, err := scanBinaryKMIndexedData(state.Scheme, 5)
	if err != nil {
		return stateReport{}, fmt.Errorf("scan %s: %w", state.ID, err)
	}
	result.Indexes = scan.Indexes
	result.Scans = scan.Scans
	for _, candidate := range scan.Candidates {
		record, err := makeCandidateRecord(state.Scheme, candidate)
		if err != nil {
			return stateReport{}, err
		}
		result.Candidates = append(result.Candidates, record)
	}
	analysis, err := tensor.AnalyzeSharedFactors(state.Scheme)
	if err != nil {
		return stateReport{}, fmt.Errorf("analyze %s: %w", state.ID, err)
	}
	for _, class := range analysis.Classes() {
		record := classRecord{SharedMode: int(class.Mode()), Slots: class.Slots(), ComplementaryRank: class.ComplementaryRank(), Defect: class.Defect()}
		if step, ok := class.ReductionStep(); ok {
			replacement, err := tensor.NewSharedFactorReduction(state.Scheme, step.Mode, step.Slots)
			if err != nil {
				return stateReport{}, err
			}
			child, err := tensor.ApplyReplacement(state.Scheme, replacement)
			if err != nil {
				return stateReport{}, err
			}
			encoded, err := encodeScheme(child, true)
			if err != nil {
				return stateReport{}, err
			}
			record.ReductionEndpoint = hash(encoded)
			for _, term := range replacement.InsertedTerms() {
				words, err := termWords(term)
				if err != nil {
					return stateReport{}, err
				}
				record.ReductionInsertedTerms = append(record.ReductionInsertedTerms, words)
			}
		}
		result.Classes = append(result.Classes, record)
	}
	return result, nil
}

func makeCandidateRecord(scheme tensor.Scheme, candidate kmCandidate) (candidateRecord, error) {
	pivot, err := termWords(scheme.Term(candidate.PivotSlot))
	if err != nil {
		return candidateRecord{}, err
	}
	record := candidateRecord{
		Orientation: candidate.Orientation, PivotSlot: candidate.PivotSlot,
		SourceSlots: append([]int(nil), candidate.SourceSlots...), Arity: len(candidate.SourceSlots),
		ChangedIndices: append([]int(nil), candidate.ChangedIndices...), ChangedCount: len(candidate.ChangedIndices),
		PredictedLengthMin: len(candidate.ChangedIndices), PredictedLengthMax: 2 * len(candidate.ChangedIndices), Pivot: pivot,
	}
	for _, slot := range candidate.SourceSlots {
		words, err := termWords(scheme.Term(slot))
		if err != nil {
			return candidateRecord{}, err
		}
		record.Sources = append(record.Sources, words)
	}
	for _, term := range candidate.TargetTerms {
		words, err := termWords(term)
		if err != nil {
			return candidateRecord{}, err
		}
		record.Targets = append(record.Targets, words)
	}
	return record, nil
}

func replayC567Regression(states []stateSpec) (regressionRecord, error) {
	var c567 stateSpec
	for _, state := range states {
		if state.Expected == "c567254223d480d8eaecde19d24f0aa96792208c41e2101a1270937bf1fe2934" {
			c567 = state
			break
		}
	}
	if c567.ID == "" {
		return regressionRecord{}, fmt.Errorf("c567 state absent")
	}
	scan, err := scanBinaryKMIndexedData(c567.Scheme, 5)
	if err != nil {
		return regressionRecord{}, err
	}
	var selected *kmCandidate
	for i := range scan.Candidates {
		candidate := &scan.Candidates[i]
		if candidate.Orientation == (kmOrientation{BMode: 0, CMode: 2, AMode: 1}) && len(candidate.SourceSlots) == 1 {
			if selected == nil || candidate.PivotSlot < selected.PivotSlot {
				selected = candidate
			}
		}
	}
	if selected == nil {
		return regressionRecord{}, fmt.Errorf("c567 indexed regression candidate absent")
	}
	record, err := makeCandidateRecord(c567.Scheme, *selected)
	if err != nil {
		return regressionRecord{}, err
	}
	slots := append([]int{selected.PivotSlot}, selected.SourceSlots...)
	slices.Sort(slots)
	replacement, err := tensor.NewSharedFactorReduction(c567.Scheme, tensor.SharedFirst, slots)
	if err != nil {
		return regressionRecord{}, fmt.Errorf("replay c567 reduction: %w", err)
	}
	child, err := tensor.ApplyReplacement(c567.Scheme, replacement)
	if err != nil {
		return regressionRecord{}, err
	}
	canonical, err := encodeScheme(child, true)
	if err != nil {
		return regressionRecord{}, err
	}
	rootHash := "f2edf6735401e203b532cc85e0783fb47684815a3207b3ec601f8503c48956d1"
	if hash(canonical) != rootHash {
		return regressionRecord{}, fmt.Errorf("c567 replay endpoint is %s, want %s", hash(canonical), rootHash)
	}
	return regressionRecord{
		StateID: c567.ID, Candidate: record, Primitive: "directed_reduction", ChangedNativeMode: 2,
		CommonNativeModes: []int{0, 1}, ReplayConstructorMode: 0, ReplaySlots: slots,
		ReplayEndpointSHA256: hash(canonical), ExpectedRootSHA256: rootHash, IndependentReplayPassed: true,
	}, nil
}

func termWords(term tensor.RankOneTerm) (triple, error) {
	var result triple
	for mode := range 3 {
		factor := term.Factor(mode)
		if factor.Rows() != 4 || factor.Columns() != 4 {
			return triple{}, fmt.Errorf("factor shape is %dx%d, want 4x4", factor.Rows(), factor.Columns())
		}
		for index, entry := range factor.Entries() {
			if entry != 0 && entry != 1 {
				return triple{}, fmt.Errorf("nonbinary factor entry %d", entry)
			}
			result[mode] |= uint16(entry) << index
		}
	}
	return result, nil
}

func encodeScheme(scheme tensor.Scheme, canonical bool) ([]byte, error) {
	words := make([]triple, scheme.TermCount())
	for slot := range scheme.TermCount() {
		var err error
		words[slot], err = termWords(scheme.Term(slot))
		if err != nil {
			return nil, err
		}
	}
	if canonical {
		slices.SortFunc(words, func(first, second triple) int {
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
	}
	data := make([]byte, 0, 8+6*len(words))
	for _, value := range []uint16{4, 4, 4, uint16(len(words))} {
		data = binary.LittleEndian.AppendUint16(data, value)
	}
	if canonical {
		for _, term := range words {
			for _, factor := range term {
				data = binary.LittleEndian.AppendUint16(data, factor)
			}
		}
	} else {
		for mode := range 3 {
			for _, term := range words {
				data = binary.LittleEndian.AppendUint16(data, term[mode])
			}
		}
	}
	return data, nil
}

func hash(data []byte) string {
	digest := sha256.Sum256(data)
	return hex.EncodeToString(digest[:])
}
