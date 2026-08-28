package main

import (
	"bytes"
	"encoding/json"
	"errors"
	"os"
	"path/filepath"
	"reflect"
	"slices"
	"strings"
	"syscall"
	"testing"
)

func TestAllFormulaVariantsAndOrientations(t *testing.T) {
	first := triple{0x1357, 0x2468, 0x369c}
	second := triple{0xaaaa, 0x5555, 0xf00f}
	for orientationIndex, positions := range orientations {
		constructorForward, err := exactPlusConstructor(first, second, positions)
		if err != nil {
			t.Fatalf("orientation %d Plus constructor: %v", orientationIndex, err)
		}
		if want := plus(first, second, positions, 0); constructorForward != want {
			t.Fatalf("orientation %d Plus outputs = %v, want %v", orientationIndex, constructorForward, want)
		}
		for variant := range 3 {
			outputs := plus(first, second, positions, variant)
			sources, replay, mask := inverse(outputs, positions, variant)
			if sources != [2]triple{first, second} || replay != outputs || mask != 511 {
				t.Fatalf("orientation %d variant %d recovery = %v, replay=%v mask=%d", orientationIndex, variant, sources, replay, mask)
			}
			constructorSources, err := exactInverseConstructor(outputs, positions, variant)
			if err != nil {
				t.Fatalf("orientation %d variant %d inverse constructor: %v", orientationIndex, variant, err)
			}
			if constructorSources != sources {
				t.Fatalf("orientation %d variant %d constructor sources = %v, want %v", orientationIndex, variant, constructorSources, sources)
			}
		}
	}
}

func TestOrientationOrderAndPermutations(t *testing.T) {
	want := [][3]int{{0, 1, 2}, {0, 2, 1}, {1, 0, 2}, {1, 2, 0}, {2, 0, 1}, {2, 1, 0}}
	if !reflect.DeepEqual(orientations, want) || !reflect.DeepEqual(orientationNames, []string{"ijk", "ikj", "jik", "jki", "kij", "kji"}) {
		t.Fatalf("orientation freeze changed: %v %v", orientations, orientationNames)
	}
	for _, positions := range orientations {
		seen := [3]bool{}
		for _, mode := range positions {
			if mode < 0 || mode >= 3 || seen[mode] {
				t.Fatalf("not a permutation: %v", positions)
			}
			seen[mode] = true
		}
	}
}

func TestResidualAndSourcePolicies(t *testing.T) {
	sources := [2]triple{{1, 2, 4}, {8, 16, 32}}
	outputs := plus(sources[0], sources[1], orientations[0], 0)
	outputs[2][0] ^= 1
	_, _, mask := inverse(outputs, orientations[0], 0)
	if mask == 511 {
		t.Fatal("inconsistent third output passed all equations")
	}
	if sourceLegal([2]triple{{0, 2, 4}, {8, 16, 32}}) {
		t.Fatal("zero source accepted")
	}
	if sourceLegal([2]triple{{1, 2, 4}, {1, 16, 32}}) {
		t.Fatal("equal source factor accepted")
	}
	want := []int{0, 2, 1, 3, 4, 5}
	cases := [][5]bool{{false, false, false, false, false}, {true, false, false, false, false}, {true, true, false, false, false}, {true, true, true, false, false}, {true, true, true, true, true}, {true, true, true, true, false}}
	for index, values := range cases {
		if got := classifyTerminal(values[0], values[1], values[2], values[3], values[4]); got != want[index] {
			t.Fatalf("classifier case %d = %d, want %d", index, got, want[index])
		}
	}
}

func TestOutcomeDerivationIncludesAlternate(t *testing.T) {
	partition := make(map[string]int)
	for _, name := range terminals {
		partition[name] = 0
	}
	partition["alternate_valid_parent"] = 1
	status, result, failures, alternates, err := deriveOutcome(partition, 1)
	if err != nil || status != "complete" || result != "complete_counterexample_found" || failures != 0 || alternates != 1 {
		t.Fatalf("alternate outcome = %q %q %d %d %v", status, result, failures, alternates, err)
	}
	partition["alternate_valid_parent"] = 0
	partition["invalid_parent"] = 1
	status, result, _, _, err = deriveOutcome(partition, 1)
	if err != nil || status != "incomplete" || result != "incomplete" {
		t.Fatalf("incomplete outcome = %q %q %v", status, result, err)
	}
}

func TestSemanticOutcomePropagation(t *testing.T) {
	sections := make(map[string][]byte, len(sectionContracts))
	for _, contract := range sectionContracts {
		sections[contract.name] = nil
	}
	called := 0
	semantic, err := buildSemantic(sections, nil, nil, nil, nil, nil, nil, nil, nil, nil, nil, nil, func(partition map[string]int, total int) (string, string, int, int, error) {
		called++
		if total != 0 || len(partition) != len(terminals) {
			t.Fatalf("outcome inputs = %v total=%d", partition, total)
		}
		return "status-sentinel", "result-sentinel", 731, 947, nil
	})
	if err != nil {
		t.Fatal(err)
	}
	outcome := semantic["outcome"].(map[string]any)
	if called != 1 || semantic["status"] != "status-sentinel" || semantic["result"] != "result-sentinel" || outcome["integrity_or_replay_failure_count"] != 731 || outcome["alternate_valid_parent_witnesses"] != 947 || outcome["alternate_orbit_status"] != "unknown" {
		t.Fatalf("propagated semantic outcome = %v %v calls=%d", semantic, outcome, called)
	}
	outcomeError := errors.New("outcome sentinel error")
	_, err = buildSemantic(sections, nil, nil, nil, nil, nil, nil, nil, nil, nil, nil, nil, func(map[string]int, int) (string, string, int, int, error) {
		return "", "", 0, 0, outcomeError
	})
	if !errors.Is(err, outcomeError) {
		t.Fatalf("outcome error = %v", err)
	}
}

func TestSemanticDigestPropagation(t *testing.T) {
	semantic := map[string]any{"status": "status", "result": "result", "marker": "semantic-input"}
	summary, err := expectedSummaryDocument(semantic, func(value map[string]any) (string, error) {
		if value["marker"] != "semantic-input" {
			t.Fatalf("summary digest input = %v", value)
		}
		return "summary-digest-sentinel", nil
	})
	if err != nil {
		t.Fatal(err)
	}
	if got := summary["integrity"].(map[string]any)["semantic_sha256"]; got != "summary-digest-sentinel" {
		t.Fatalf("summary semantic digest = %v", got)
	}
	report, err := buildReport(semantic, validationCounts{}, nil, func(value map[string]any) (string, error) {
		if value["marker"] != "semantic-input" {
			t.Fatalf("report digest input = %v", value)
		}
		return "report-digest-sentinel", nil
	})
	if err != nil {
		t.Fatal(err)
	}
	if report["semantic_sha256"] != "report-digest-sentinel" {
		t.Fatalf("report semantic digest = %v", report["semantic_sha256"])
	}
	if report["status"] != "status" || report["result"] != "result" {
		t.Fatalf("report semantic status/result = %v/%v", report["status"], report["result"])
	}
	summaryError := errors.New("summary digest sentinel error")
	if _, err := expectedSummaryDocument(semantic, func(map[string]any) (string, error) { return "discarded", summaryError }); !errors.Is(err, summaryError) {
		t.Fatalf("summary digest error = %v", err)
	}
	reportError := errors.New("report digest sentinel error")
	if _, err := buildReport(semantic, validationCounts{}, nil, func(map[string]any) (string, error) { return "discarded", reportError }); !errors.Is(err, reportError) {
		t.Fatalf("report digest error = %v", err)
	}
}

func TestValidationReportMapsEveryCount(t *testing.T) {
	counts := validationCounts{
		rootBrent: 101, parentClassBrent: 103,
		plusConstructor: 107, inverseConstructor: 109,
		forwardExact: 113, equationHits: 127, localReplay: 131, scatterReplay: 137, parentExact: 139,
		bucketOccurrences: 149, inverseConstructorResidualFailure: 151,
	}
	want := map[string]any{
		"root_brent_replays": 101, "unique_parent_class_brent_replays": 103,
		"new_plus_replacement_calls": 107, "new_inverse_plus_replacement_calls": 109,
		"forward_exact_output_tensor_nonzero_distinct_checks": 113, "inverse_equation_hits": 127,
		"accepted_local_tensor_replays": 131, "accepted_scatter_replays": 137,
		"accepted_parent_tensor_nonzero_distinct_checks": 139, "mode_typed_factor_bucket_occurrences": 149,
		"inverse_constructor_called_on_residual_failures": 151,
	}
	if got := validationReport(counts); !reflect.DeepEqual(got, want) {
		t.Fatalf("validation report = %v, want %v", got, want)
	}
}

func TestRegeneratedSectionMetadataUsesGeneratedBytes(t *testing.T) {
	base := []byte{1, 2, 3, 4, 5, 6}
	mutated := append([]byte(nil), base...)
	mutated[2] ^= 0xff
	boundary := append([]byte(nil), base[:5]...)
	baseMetadata := regeneratedSectionMetadata("synthetic", base, 3)
	mutatedMetadata := regeneratedSectionMetadata("synthetic", mutated, 3)
	boundaryMetadata := regeneratedSectionMetadata("synthetic", boundary, 3)
	if baseMetadata["size"] != 6 || baseMetadata["count"] != 2 || baseMetadata["payload_sha256"] != digest(base) || baseMetadata["domain_separated_sha256"] != sectionDigest("synthetic", base) {
		t.Fatalf("base generated metadata = %v", baseMetadata)
	}
	if mutatedMetadata["size"] != 6 || mutatedMetadata["count"] != 2 || mutatedMetadata["payload_sha256"] != digest(mutated) || mutatedMetadata["domain_separated_sha256"] != sectionDigest("synthetic", mutated) || mutatedMetadata["payload_sha256"] == baseMetadata["payload_sha256"] || mutatedMetadata["domain_separated_sha256"] == baseMetadata["domain_separated_sha256"] {
		t.Fatalf("one-byte mutation metadata = %v, base %v", mutatedMetadata, baseMetadata)
	}
	if boundaryMetadata["size"] != 5 || boundaryMetadata["count"] != 1 || boundaryMetadata["payload_sha256"] != digest(boundary) || boundaryMetadata["domain_separated_sha256"] != sectionDigest("synthetic", boundary) {
		t.Fatalf("boundary generated metadata = %v", boundaryMetadata)
	}
}

func TestExactClassesSortMultiplicityAndCollision(t *testing.T) {
	classes, lookup, err := exactClasses([][]byte{[]byte("b"), []byte("a"), []byte("b")}, "test")
	if err != nil {
		t.Fatal(err)
	}
	if len(classes) != 2 || string(classes[0].value) != "a" || string(classes[1].value) != "b" {
		t.Fatalf("classes = %#v", classes)
	}
	if got := classes[lookup["b"]].members; !reflect.DeepEqual(got, []int{0, 2}) {
		t.Fatalf("b members = %v", got)
	}
	for _, role := range []string{"child", "source class", "parent class"} {
		_, _, err := exactClassesWithHash([][]byte{[]byte("different-a"), []byte("different-b")}, role, func([]byte) string { return "same-bucket" })
		if err == nil {
			t.Fatalf("%s differing bytes in one hash bucket were accepted", role)
		}
		if !strings.Contains(err.Error(), role+" SHA-256 collision on differing exact bytes") {
			t.Fatalf("%s collision error = %v", role, err)
		}
	}
}

func TestStrictJSONRejectsDuplicateMalformedAndTruncated(t *testing.T) {
	cases := [][]byte{
		[]byte("{\"schema\":\"x\",\"schema\":\"y\"}\n"),
		[]byte("{\"schema\":}\n"),
		[]byte("{\"schema\":\"x\"\n"),
	}
	for index, value := range cases {
		if _, err := parseSummary(value); err == nil {
			t.Fatalf("malformed summary case %d accepted", index)
		}
	}
	if _, err := parseSummary([]byte("{}")); err == nil {
		t.Fatal("summary without final LF accepted")
	}
}

func repositoryArguments() []string {
	repository := filepath.Clean(filepath.Join("..", ".."))
	return []string{
		filepath.Join(repository, rootID),
		filepath.Join(repository, sourceID),
		filepath.Join(repository, summaryID),
		filepath.Join(repository, corpusID),
		filepath.Join(repository, validatorID),
	}
}

func TestRunAuthenticatedCorpus(t *testing.T) {
	args := repositoryArguments()
	for _, path := range args {
		if _, err := os.Stat(path); err != nil {
			t.Fatalf("fixture %s: %v", path, err)
		}
	}
	var output bytes.Buffer
	dependencies := productionRunDependencies()
	calls := map[string]int{}
	nextOffset := 0
	read := dependencies.read
	dependencies.read = func(path string, spec inputSpec) ([]byte, error) {
		calls["read"]++
		return read(path, spec)
	}
	regenerate := dependencies.regenerate
	dependencies.regenerate = func(root []triple, raw []byte, validation regenerationDependencies, outcome outcomeDeriver) (*regeneration, error) {
		calls["regenerate"]++
		return regenerate(root, raw, validation, outcome)
	}
	productionValidation := productionRegenerationDependencies()
	rootExact := productionValidation.rootExact
	productionValidation.rootExact = func(root []triple, target tensorBits) error {
		calls["root_validation"]++
		if len(root) != 47 || target != targetTensor() {
			t.Fatalf("root productionValidation arguments = rank %d target_match=%v", len(root), target == targetTensor())
		}
		return rootExact(root, target)
	}
	plusConstructor := productionValidation.plusConstructor
	productionValidation.plusConstructor = func(first, second triple, positions [3]int) ([3]triple, error) {
		calls["plus_validation"]++
		if first == second || first[0] == 0 || first[1] == 0 || first[2] == 0 || second[0] == 0 || second[1] == 0 || second[2] == 0 || !slices.Contains(orientations, positions) {
			t.Fatalf("plus productionValidation arguments = %v %v %v", first, second, positions)
		}
		return plusConstructor(first, second, positions)
	}
	forwardExact := productionValidation.forwardExact
	productionValidation.forwardExact = func(outputs [3]triple, sources [2]triple, terms []triple) error {
		calls["forward_validation"]++
		if len(terms) != 48 || terms[45] != outputs[0] || terms[46] != outputs[1] || terms[47] != outputs[2] || sources[0] == sources[1] {
			t.Fatalf("forward productionValidation arguments = outputs %v sources %v terms %d", outputs, sources, len(terms))
		}
		return forwardExact(outputs, sources, terms)
	}
	bucketOccurrence := productionValidation.bucketOccurrence
	productionValidation.bucketOccurrence = func(child, mode, color int, term triple) error {
		calls["bucket_validation"]++
		if child < 0 || child >= 6486 || mode < 0 || mode >= 3 || color < 0 || color >= 48 || term[0] == 0 || term[1] == 0 || term[2] == 0 {
			t.Fatalf("bucket productionValidation arguments = child %d mode %d color %d term %v", child, mode, color, term)
		}
		return bucketOccurrence(child, mode, color, term)
	}
	inverseEquations := productionValidation.inverseEquations
	productionValidation.inverseEquations = func(outputs [3]triple, sources [2]triple, replay [3]triple, mask uint16) bool {
		calls["equation_validation"]++
		if replay != outputs || mask != 511 {
			t.Fatalf("equation productionValidation arguments = outputs %v sources %v replay %v mask %d", outputs, sources, replay, mask)
		}
		return inverseEquations(outputs, sources, replay, mask)
	}
	inverseConstructor := productionValidation.inverseConstructor
	productionValidation.inverseConstructor = func(outputs [3]triple, positions [3]int, variant int) ([2]triple, error) {
		calls["inverse_validation"]++
		if !slices.Contains(orientations, positions) || variant < 0 || variant >= 3 {
			t.Fatalf("inverse productionValidation arguments = outputs %v positions %v variant %d", outputs, positions, variant)
		}
		return inverseConstructor(outputs, positions, variant)
	}
	localReplay := productionValidation.localReplay
	productionValidation.localReplay = func(sources [2]triple, replay, outputs [3]triple) error {
		calls["local_validation"]++
		if !sourceLegal(sources) || replay != outputs {
			t.Fatalf("local productionValidation arguments = sources %v replay %v outputs %v", sources, replay, outputs)
		}
		return localReplay(sources, replay, outputs)
	}
	scatterReplay := productionValidation.scatterReplay
	productionValidation.scatterReplay = func(survivors []triple, replay [3]triple, child []byte) error {
		calls["scatter_validation"]++
		if len(survivors) != 45 || len(child) != 296 {
			t.Fatalf("scatter productionValidation arguments = survivors %d replay %v child %d", len(survivors), replay, len(child))
		}
		return scatterReplay(survivors, replay, child)
	}
	parentExact := productionValidation.parentExact
	productionValidation.parentExact = func(parent []triple, target tensorBits) error {
		calls["parent_validation"]++
		if len(parent) != 47 || target != targetTensor() {
			t.Fatalf("parent productionValidation arguments = rank %d target_match=%v", len(parent), target == targetTensor())
		}
		return parentExact(parent, target)
	}
	parentClassBrent := productionValidation.parentClassBrent
	productionValidation.parentClassBrent = func(parent []triple) error {
		calls["parent_class_validation"]++
		if len(parent) != 47 {
			t.Fatalf("parent class productionValidation rank = %d", len(parent))
		}
		return parentClassBrent(parent)
	}
	dependencies.regenerationDependencies = productionValidation
	compareSection := dependencies.compareSection
	dependencies.compareSection = func(corpus []byte, offset, size int, name string, generated []byte) error {
		calls["compare_section"]++
		if offset != nextOffset || size != len(generated) {
			t.Fatalf("section %s regenerated range = %d+%d, next=%d bytes=%d", name, offset, size, nextOffset, len(generated))
		}
		nextOffset += len(generated)
		return compareSection(corpus, offset, size, name, generated)
	}
	compareJSON := dependencies.compareJSON
	dependencies.compareJSON = func(expected, generated any) error {
		calls["compare_json"]++
		return compareJSON(expected, generated)
	}
	outcome := dependencies.deriveOutcome
	dependencies.deriveOutcome = func(partition map[string]int, total int) (string, string, int, int, error) {
		calls["derive_outcome"]++
		return outcome(partition, total)
	}
	semanticDigest := dependencies.deriveSemanticDigest
	dependencies.deriveSemanticDigest = func(semantic map[string]any) (string, error) {
		calls["derive_semantic_digest"]++
		return semanticDigest(semantic)
	}
	if err := runWithDependencies(args, &output, dependencies); err != nil {
		t.Fatal(err)
	}
	if calls["read"] != 5 || calls["regenerate"] != 1 || calls["compare_section"] != len(sectionOrder) || calls["compare_json"] != len(sectionOrder)+1 || calls["derive_outcome"] != 1 || calls["derive_semantic_digest"] != 2 || nextOffset != corpusSize {
		t.Fatalf("run dependency calls = %v, covered=%d", calls, nextOffset)
	}
	validationCalls := map[string]int{
		"root_validation": 1, "plus_validation": 12972, "forward_validation": 12972,
		"bucket_validation": 6486 * 48 * 3, "equation_validation": 38916, "inverse_validation": 38916,
		"local_validation": 38916, "scatter_validation": 38916, "parent_validation": 38916, "parent_class_validation": 1,
	}
	for name, want := range validationCalls {
		if calls[name] != want {
			t.Fatalf("production validation call %s = %d, want %d", name, calls[name], want)
		}
	}
	if got := digest(output.Bytes()); got != "83e72bed74c3f65f0230dadbe80dc0ded576dd0cfa82e29ab84e340ca65fb250" {
		t.Fatalf("complete output SHA-256 = %s", got)
	}
	var report map[string]any
	if err := json.Unmarshal(output.Bytes(), &report); err != nil {
		t.Fatal(err)
	}
	if report["status"] != "complete" || report["result"] != "complete_no_counterexample_found" || report["semantic_sha256"] != "ddb62e128b9d310e6cd5954d9bf638fe2c97a813a82be8a86d25b3e8c3aeacec" {
		t.Fatalf("top-level derivation = %v/%v/%v", report["status"], report["result"], report["semantic_sha256"])
	}
	bindings := report["authenticated_inputs"].([]any)
	wantRoles := []string{"root", "producer source", "summary", "corpus", "validator"}
	for index, value := range bindings {
		binding := value.(map[string]any)
		if binding["role"] != wantRoles[index] || binding["authenticated"] != true {
			t.Fatalf("binding %d = %v", index, binding)
		}
	}
	regeneration := report["independent_regeneration"].(map[string]any)
	sections := regeneration["sections"].([]any)
	if regeneration["all_ten_sections_exact"] != true || len(sections) != 10 {
		t.Fatalf("section report = %v", regeneration)
	}
	for _, value := range sections {
		section := value.(map[string]any)
		for _, field := range []string{"exact_section_bytes", "size_exact", "count_exact", "payload_sha256_exact", "domain_separated_sha256_exact"} {
			if section[field] != true {
				t.Fatalf("section %s field %s = %v", section["id"], field, section[field])
			}
		}
		if section["expected"] == nil || section["regenerated"] == nil {
			t.Fatalf("section metadata missing: %v", section)
		}
	}
	validation := regeneration["validation_counts"].(map[string]any)
	wantCounts := map[string]float64{
		"root_brent_replays": 1, "unique_parent_class_brent_replays": 1,
		"new_plus_replacement_calls": 12972, "new_inverse_plus_replacement_calls": 38916,
		"forward_exact_output_tensor_nonzero_distinct_checks": 12972, "inverse_equation_hits": 38916,
		"accepted_local_tensor_replays": 38916, "accepted_scatter_replays": 38916,
		"accepted_parent_tensor_nonzero_distinct_checks": 38916, "mode_typed_factor_bucket_occurrences": 6486 * 48 * 3,
		"inverse_constructor_called_on_residual_failures": 0,
	}
	for key, want := range wantCounts {
		if validation[key] != want {
			t.Fatalf("validation count %s = %v, want %v", key, validation[key], want)
		}
	}
	derived := report["derived"].(map[string]any)
	counts := derived["counts"].(map[string]any)
	if counts["residual_failures"] != float64(7632) || counts["forward_aliases_covered"] != float64(12972) || counts["raw_wedges"] != float64(7758) {
		t.Fatalf("residual/alias/wedge counts = %v", counts)
	}
	aliasProfile := counts["forward_alias_multiplicity_profile"].(map[string]any)
	coverageProfile := counts["inverse_witnesses_per_forward_alias_profile"].(map[string]any)
	wedgeProfile := counts["child_raw_wedge_profile"].(map[string]any)
	if aliasProfile["2"] != float64(6486) || coverageProfile["3"] != float64(12972) || wedgeProfile["1"] != float64(5652) || wedgeProfile["2"] != float64(476) || wedgeProfile["3"] != float64(278) || wedgeProfile["4"] != float64(80) {
		t.Fatalf("alias/coverage/typed-wedge profiles = %v %v %v", aliasProfile, coverageProfile, wedgeProfile)
	}
	execution := report["authenticated_program_execution"].(map[string]any)
	if execution["sage_producer_executed"] != false || execution["python_validator_executed"] != false || execution["equivalence_solver_executed"] != false {
		t.Fatalf("execution disclosure = %v", execution)
	}
	if !strings.Contains(execution["alternate_parent_orbit_policy"].(string), "unknown orbit status") || !strings.Contains(execution["alternate_parent_orbit_policy"].(string), "fail before certificate publication") {
		t.Fatalf("alternate orbit disclosure = %v", execution)
	}
	scope := report["scope"].(map[string]any)
	if !strings.Contains(scope["forward_children"].(string), "variant 0 only") || !strings.Contains(scope["inverse_candidates"].(string), "complete mode-typed wedges only") {
		t.Fatalf("scope is not honest: %v", scope)
	}
	qualification := scope["nine_equation_qualification"].(string)
	if !strings.Contains(qualification, "nine output-factor coordinate equalities") || !strings.Contains(qualification, "does not claim algebraic independence") {
		t.Fatalf("nine-equation qualification = %q", qualification)
	}
	negative := scope["negative_scope"].(map[string]any)
	if len(negative["excluded"].([]any)) != 7 {
		t.Fatalf("scope exclusions = %v", negative)
	}
}

func TestExactCorpusSectionRejectsTamperedAndTruncated(t *testing.T) {
	generated := []byte{2, 3, 4}
	if err := exactCorpusSection([]byte{1, 2, 3, 4, 5}, 1, 3, "synthetic", generated); err != nil {
		t.Fatal(err)
	}
	if err := exactCorpusSection([]byte{1, 2, 9, 4, 5}, 1, 3, "synthetic", generated); err == nil {
		t.Fatal("tampered section accepted")
	}
	if err := exactCorpusSection([]byte{1, 2, 3}, 1, 3, "synthetic", generated); err == nil {
		t.Fatal("truncated section accepted")
	}
}

func TestReadAuthenticatedRejectsSymlinkTamperingAndTruncation(t *testing.T) {
	directory := t.TempDir()
	regular := filepath.Join(directory, "regular")
	if err := os.WriteFile(regular, []byte("authenticated"), 0o600); err != nil {
		t.Fatal(err)
	}
	spec := inputSpec{Role: "test", Size: len("authenticated"), SHA256: digest([]byte("authenticated"))}
	if _, err := readAuthenticated(regular, spec); err != nil {
		t.Fatalf("regular authenticated input: %v", err)
	}
	wrong := spec
	wrong.SHA256 = digest([]byte("wrong"))
	if _, err := readAuthenticated(regular, wrong); err == nil {
		t.Fatal("accepted wrong hash")
	}
	truncated := spec
	truncated.Size++
	if _, err := readAuthenticated(regular, truncated); err == nil {
		t.Fatal("accepted truncated input")
	}
	link := filepath.Join(directory, "link")
	if err := os.Symlink(regular, link); err != nil {
		t.Fatal(err)
	}
	if _, err := readAuthenticated(link, spec); err == nil {
		t.Fatal("accepted symbolic link")
	}
}

func TestReadAuthenticatedRejectsFIFOWithoutBlocking(t *testing.T) {
	path := filepath.Join(t.TempDir(), "fifo")
	if err := syscall.Mkfifo(path, 0o600); err != nil {
		t.Fatal(err)
	}
	if _, err := readAuthenticated(path, inputSpec{Role: "fifo", SHA256: digest(nil)}); err == nil {
		t.Fatal("accepted FIFO")
	}
}

func TestTypedWedgesUseAllModeTypedOccurrences(t *testing.T) {
	terms := []triple{{1, 2, 4}, {1, 8, 1}, {16, 2, 5}, {1, 2, 9}, {1, 32, 7}}
	observed := 0
	wedges, err := enumerateTypedWedges(terms, func(mode, color int, term triple) error {
		if term != terms[color] || mode < 0 || mode >= 3 {
			t.Fatalf("bad occurrence mode=%d color=%d term=%v", mode, color, term)
		}
		observed++
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}
	if observed != len(terms)*3 {
		t.Fatalf("observed %d factor occurrences, want %d", observed, len(terms)*3)
	}
	found := false
	for _, wedge := range wedges {
		if wedge.center == 0 && wedge.a == (colorLeg{1, 0}) && wedge.b == (colorLeg{2, 1}) {
			found = true
			if wedge.residual != 2 || !wedge.pass {
				t.Fatalf("discriminating wedge = %+v", wedge)
			}
		}
		if wedge.center == 0 && (wedge.a.color == 3 || wedge.b.color == 3) {
			t.Fatalf("color sharing two typed legs entered wedge: %+v", wedge)
		}
	}
	if !found {
		t.Fatalf("missing complete typed wedge in %+v", wedges)
	}
	terms[2][2] ^= 1
	wedges, err = enumerateTypedWedges(terms, func(int, int, triple) error { return nil })
	if err != nil {
		t.Fatal(err)
	}
	for _, wedge := range wedges {
		if wedge.center == 0 && wedge.a.color == 1 && wedge.b.color == 2 && wedge.pass {
			t.Fatal("residual mutation did not change wedge pass")
		}
	}
}

func TestReciprocalAliasLookupRejectsCollisionAndBadSlot(t *testing.T) {
	root := []triple{{1, 2, 3}, {4, 5, 6}}
	forward := []forwardRow{{first: 0, second: 1, child: 7}, {first: 0, second: 1, child: 7}}
	if _, err := reciprocalAliasLookup(forward, root); err == nil {
		t.Fatal("duplicate reciprocal alias key was silently overwritten")
	}
	forward = []forwardRow{{first: 0, second: 2, child: 7}}
	if _, err := reciprocalAliasLookup(forward, root); err == nil {
		t.Fatal("out-of-range reciprocal alias source was accepted")
	}
}

func TestAcceptedWitnessRejectsMissingReciprocalAliasKey(t *testing.T) {
	sources := [2]triple{{1, 2, 3}, {4, 5, 6}}
	accepted := []acceptedRow{{descriptor: 0, sources: sources}}
	descriptors := []descriptorRow{{child: 7}}
	err := assignReciprocalAliases(accepted, descriptors, map[aliasKey]uint32{})
	if err == nil || !strings.Contains(err.Error(), "accepted witness has no reciprocal alias") {
		t.Fatalf("missing reciprocal alias error = %v", err)
	}
}

func TestParentClassificationDistinguishesAlternateExactBytes(t *testing.T) {
	root := []byte{1, 2, 3}
	classification, orbit := parentClassification(append([]byte(nil), root...), root)
	if classification != 0 || orbit != 0 {
		t.Fatalf("exact root classification = %d/%d", classification, orbit)
	}
	alternate := append([]byte(nil), root...)
	alternate[2] ^= 1
	classification, orbit = parentClassification(alternate, root)
	if classification != 1 || orbit != 1 {
		t.Fatalf("alternate classification = %d/%d", classification, orbit)
	}
}

func TestRegenerationGateDependenciesAndCounters(t *testing.T) {
	calls := make(map[string]int)
	dependencies := regenerationDependencies{
		rootExact:          func([]triple, tensorBits) error { calls["root"]++; return nil },
		plusConstructor:    func(triple, triple, [3]int) ([3]triple, error) { calls["plus"]++; return [3]triple{}, nil },
		forwardExact:       func([3]triple, [2]triple, []triple) error { calls["forward"]++; return nil },
		bucketOccurrence:   func(int, int, int, triple) error { calls["bucket"]++; return nil },
		inverseEquations:   func([3]triple, [2]triple, [3]triple, uint16) bool { calls["equations"]++; return true },
		inverseConstructor: func([3]triple, [3]int, int) ([2]triple, error) { calls["inverse"]++; return [2]triple{}, nil },
		localReplay:        func([2]triple, [3]triple, [3]triple) error { calls["local"]++; return nil },
		scatterReplay:      func([]triple, [3]triple, []byte) error { calls["scatter"]++; return nil },
		parentExact:        func([]triple, tensorBits) error { calls["parent"]++; return nil },
		parentClassBrent:   func([]triple) error { calls["class"]++; return nil },
	}
	gates := regenerationGates{dependencies: dependencies}
	if err := gates.validateRoot(nil, tensorBits{}); err != nil {
		t.Fatal(err)
	}
	if _, err := gates.constructPlus(triple{}, triple{}, [3]int{}); err != nil {
		t.Fatal(err)
	}
	if err := gates.validateForward([3]triple{}, [2]triple{}, nil); err != nil {
		t.Fatal(err)
	}
	if err := gates.observeBucket(0, 0, 0, triple{}); err != nil {
		t.Fatal(err)
	}
	if !gates.validateEquations([3]triple{}, [2]triple{}, [3]triple{}, 511) {
		t.Fatal("equation spy rejected")
	}
	if _, err := gates.constructInverse([3]triple{}, [3]int{}, 0, false); err != nil {
		t.Fatal(err)
	}
	if err := gates.validateLocal([2]triple{}, [3]triple{}, [3]triple{}); err != nil {
		t.Fatal(err)
	}
	if err := gates.validateScatter(nil, [3]triple{}, nil); err != nil {
		t.Fatal(err)
	}
	if err := gates.validateParent(nil, tensorBits{}); err != nil {
		t.Fatal(err)
	}
	if err := gates.validateParentClass(nil); err != nil {
		t.Fatal(err)
	}
	for _, name := range []string{"root", "plus", "forward", "bucket", "equations", "inverse", "local", "scatter", "parent", "class"} {
		if calls[name] != 1 {
			t.Fatalf("dependency %s calls = %d", name, calls[name])
		}
	}
	counts := gates.counts
	if counts.rootBrent != 1 || counts.plusConstructor != 1 || counts.forwardExact != 1 || counts.bucketOccurrences != 1 || counts.equationHits != 1 || counts.inverseConstructor != 1 || counts.inverseConstructorResidualFailure != 1 || counts.localReplay != 1 || counts.scatterReplay != 1 || counts.parentExact != 1 || counts.parentClassBrent != 1 {
		t.Fatalf("actual-call counters = %+v", counts)
	}
}

func TestProductionValidationDependenciesAreMutationSensitive(t *testing.T) {
	dependencies := productionRegenerationDependencies()
	sources := [2]triple{{1, 2, 4}, {8, 16, 32}}
	outputs := plus(sources[0], sources[1], orientations[0], 0)
	terms := append([]triple(nil), outputs[:]...)
	if err := dependencies.forwardExact(outputs, sources, terms); err != nil {
		t.Fatal(err)
	}
	mutatedTerms := append([]triple(nil), terms...)
	mutatedTerms = append(mutatedTerms, terms[0])
	if err := dependencies.forwardExact(outputs, sources, mutatedTerms); err == nil {
		t.Fatal("duplicate forward output mutation passed")
	}
	recovered, replay, mask := inverse(outputs, orientations[0], 0)
	if !dependencies.inverseEquations(outputs, recovered, replay, mask) {
		t.Fatal("exact inverse replay rejected")
	}
	replay[2][0] ^= 1
	if dependencies.inverseEquations(outputs, recovered, replay, mask) {
		t.Fatal("replay coordinate mutation passed nine equality checks")
	}
	replay = outputs
	child := canonicalPayload(replay[:])
	if err := dependencies.scatterReplay(nil, replay, child); err != nil {
		t.Fatal(err)
	}
	child[len(child)-1] ^= 1
	if err := dependencies.scatterReplay(nil, replay, child); err == nil {
		t.Fatal("scatter byte mutation passed")
	}
	parent := make([]triple, 47)
	for index := range parent {
		value := uint16(index + 1)
		parent[index] = triple{value, value + 100, value + 200}
	}
	target := tensorSum(parent)
	if err := dependencies.parentExact(parent, target); err != nil {
		t.Fatal(err)
	}
	parent[46] = parent[0]
	if err := dependencies.parentExact(parent, target); err == nil {
		t.Fatal("duplicate parent term mutation passed")
	}
}

func TestRunRejectsArgumentCount(t *testing.T) {
	var output bytes.Buffer
	if err := run(nil, &output); err == nil {
		t.Fatal("run accepted no paths")
	}
	if output.String() != usage {
		t.Fatalf("usage = %q", output.String())
	}
}
