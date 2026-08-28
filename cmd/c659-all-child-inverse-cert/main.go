package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"strconv"

	"patel.codes/proofs/internal/ring"
	"patel.codes/proofs/internal/tensor"
)

const usage = "Usage: c659-all-child-inverse-cert ROOT SAGE_PRODUCER SUMMARY CORPUS PYTHON_VALIDATOR\n"

func main() {
	if err := run(os.Args[1:], os.Stdout); err != nil {
		fmt.Fprintf(os.Stderr, "%s: %v\n", commandName, err)
		os.Exit(1)
	}
}

type runDependencies struct {
	read                     func(string, inputSpec) ([]byte, error)
	regenerate               func([]triple, []byte, regenerationDependencies, outcomeDeriver) (*regeneration, error)
	regenerationDependencies regenerationDependencies
	compareSection           func([]byte, int, int, string, []byte) error
	compareJSON              func(any, any) error
	deriveOutcome            outcomeDeriver
	deriveSemanticDigest     semanticDigestDeriver
}

func productionRunDependencies() runDependencies {
	return runDependencies{
		read:                     readAuthenticated,
		regenerate:               regenerateWithDependencies,
		regenerationDependencies: productionRegenerationDependencies(),
		compareSection:           exactCorpusSection,
		compareJSON:              compareCanonicalJSON,
		deriveOutcome:            deriveOutcome,
		deriveSemanticDigest:     deriveSemanticDigest,
	}
}

func run(args []string, output io.Writer) error {
	return runWithDependencies(args, output, productionRunDependencies())
}

func runWithDependencies(args []string, output io.Writer, dependencies runDependencies) error {
	if len(args) == 1 && (args[0] == "-h" || args[0] == "--help") {
		_, err := io.WriteString(output, usage)
		return err
	}
	if len(args) != len(inputSpecs) {
		if _, err := io.WriteString(output, usage); err != nil {
			return err
		}
		return fmt.Errorf("require exactly five authenticated file paths, got %d", len(args))
	}
	inputs := make([][]byte, len(args))
	for index, path := range args {
		value, err := dependencies.read(path, inputSpecs[index])
		if err != nil {
			return err
		}
		inputs[index] = value
	}
	document, err := parseSummary(inputs[2])
	if err != nil {
		return err
	}
	rootScheme, err := tensor.ParseNative(ring.Z2, bytes.NewReader(inputs[0]))
	if err != nil {
		return fmt.Errorf("parse root with tensor.ParseNative: %w", err)
	}
	if rootScheme.Dimensions() != [3]int{4, 4, 4} || rootScheme.TermCount() != 47 {
		return fmt.Errorf("root dimensions/rank mismatch")
	}
	root, err := schemeWords(rootScheme)
	if err != nil {
		return err
	}
	regenerated, err := dependencies.regenerate(root, inputs[0], dependencies.regenerationDependencies, dependencies.deriveOutcome)
	if err != nil {
		return err
	}
	expectedManifest, err := verifiedSummaryManifest(document)
	if err != nil {
		return err
	}
	generatedManifestRaw, generatedCorpus, err := buildManifest(regenerated.sections)
	if err != nil {
		return err
	}
	if len(generatedCorpus) != len(inputs[3]) {
		return fmt.Errorf("regenerated corpus size is %d, authenticated corpus size is %d", len(generatedCorpus), len(inputs[3]))
	}
	sectionReports := make([]map[string]any, 0, len(sectionOrder))
	for index, name := range sectionOrder {
		expected := expectedManifest[index]
		generated, ok := generatedManifestRaw[index].(map[string]any)
		if !ok {
			return fmt.Errorf("regenerated manifest section %d is not an object", index)
		}
		if generated["id"] != name {
			return fmt.Errorf("regenerated manifest section %d ID mismatch", index)
		}
		if err := dependencies.compareJSON(expected, generated); err != nil {
			return fmt.Errorf("summary manifest section %s metadata differs from regeneration: %w", name, err)
		}
		offset, err := jsonInteger(generated["offset"])
		if err != nil {
			return fmt.Errorf("regenerated manifest section %s offset is invalid", name)
		}
		size, err := jsonInteger(generated["size"])
		if err != nil {
			return fmt.Errorf("regenerated manifest section %s size is invalid", name)
		}
		generatedBytes := regenerated.sections[name]
		if err := dependencies.compareSection(inputs[3], offset, size, name, generatedBytes); err != nil {
			return err
		}
		contract := sectionContracts[index]
		regeneratedMetadata := regeneratedSectionMetadata(name, generatedBytes, contract.recordSize)
		expectedMetadata := map[string]any{"size": expected["size"], "count": expected["count"], "payload_sha256": expected["payload_sha256"], "domain_separated_sha256": expected["domain_separated_sha256"]}
		sectionReports = append(sectionReports, map[string]any{
			"id": name, "expected": expectedMetadata, "regenerated": regeneratedMetadata,
			"exact_section_bytes":           true,
			"size_exact":                    equalJSONNumber(expected["size"], len(generatedBytes)),
			"count_exact":                   equalJSONNumber(expected["count"], len(generatedBytes)/contract.recordSize),
			"payload_sha256_exact":          expected["payload_sha256"] == regeneratedMetadata["payload_sha256"],
			"domain_separated_sha256_exact": expected["domain_separated_sha256"] == regeneratedMetadata["domain_separated_sha256"],
		})
	}
	expectedDocument, err := expectedSummaryDocument(regenerated.semantic, dependencies.deriveSemanticDigest)
	if err != nil {
		return err
	}
	expectedJSON, err := canonicalJSON(expectedDocument)
	if err != nil {
		return err
	}
	if !bytes.Equal(append(expectedJSON, '\n'), inputs[2]) {
		return fmt.Errorf("authenticated summary differs from independently regenerated semantic document")
	}
	if err := dependencies.compareJSON(document, expectedDocument); err != nil {
		return fmt.Errorf("parsed summary semantic contract mismatch: %w", err)
	}
	report, err := buildReport(regenerated.semantic, regenerated.validation, sectionReports, dependencies.deriveSemanticDigest)
	if err != nil {
		return err
	}
	encoded, err := json.MarshalIndent(report, "", "  ")
	if err != nil {
		return err
	}
	encoded = append(encoded, '\n')
	written, err := output.Write(encoded)
	if err != nil {
		return err
	}
	if written != len(encoded) {
		return io.ErrShortWrite
	}
	return nil
}

func regeneratedSectionMetadata(name string, generated []byte, recordSize int) map[string]any {
	return map[string]any{
		"size":                    len(generated),
		"count":                   len(generated) / recordSize,
		"payload_sha256":          digest(generated),
		"domain_separated_sha256": sectionDigest(name, generated),
	}
}

func validationReport(counts validationCounts) map[string]any {
	return map[string]any{
		"root_brent_replays":                                  counts.rootBrent,
		"unique_parent_class_brent_replays":                   counts.parentClassBrent,
		"new_plus_replacement_calls":                          counts.plusConstructor,
		"new_inverse_plus_replacement_calls":                  counts.inverseConstructor,
		"forward_exact_output_tensor_nonzero_distinct_checks": counts.forwardExact,
		"inverse_equation_hits":                               counts.equationHits,
		"accepted_local_tensor_replays":                       counts.localReplay,
		"accepted_scatter_replays":                            counts.scatterReplay,
		"accepted_parent_tensor_nonzero_distinct_checks":      counts.parentExact,
		"mode_typed_factor_bucket_occurrences":                counts.bucketOccurrences,
		"inverse_constructor_called_on_residual_failures":     counts.inverseConstructorResidualFailure,
	}
}

func buildReport(semantic map[string]any, counts validationCounts, sectionReports []map[string]any, semanticDigest semanticDigestDeriver) (map[string]any, error) {
	status, statusOK := semantic["status"].(string)
	result, resultOK := semantic["result"].(string)
	if !statusOK || !resultOK {
		return nil, fmt.Errorf("derived status/result are not strings")
	}
	semanticSHA256, err := semanticDigest(semantic)
	if err != nil {
		return nil, err
	}
	bindings := make([]map[string]any, len(inputSpecs))
	for index, spec := range inputSpecs {
		bindings[index] = map[string]any{"argument_position": index + 1, "role": spec.Role, "repository_relative_id": spec.ID, "bytes": spec.Size, "sha256": spec.SHA256, "authenticated": true}
	}
	return map[string]any{
		"schema": outputSchema, "status": status, "result": result, "semantic_sha256": semanticSHA256, "oracle_schema": schema,
		"authenticated_inputs": bindings,
		"authenticated_program_execution": map[string]any{
			"sage_producer_executed": false, "python_validator_executed": false, "equivalence_solver_executed": false,
			"alternate_parent_orbit_policy": "Any unexpected exact alternate parent would have unknown orbit status; this command runs no equivalence solver, and exact comparison with the frozen corpus would fail before certificate publication.",
			"statement":                     "The Sage producer and Python validator are authenticated as exact input bytes but are not executed; this Go command independently regenerates and validates the artifact semantics and corpus.",
		},
		"independent_regeneration": map[string]any{
			"all_ten_sections_exact": true, "section_order": sectionOrder, "sections": sectionReports,
			"summary_semantics_exact": true, "manifest_exact": true, "stable_ids_exact": true,
			"validation_counts": validationReport(counts),
		},
		"scope": map[string]any{
			"forward_children":            "all 47x46 ordered root source pairs and six orientations, Plus variant 0 only",
			"inverse_candidates":          "complete mode-typed wedges only, built from all canonical factor-bucket occurrences; no untyped or first-occurrence-only bucket reduction",
			"nine_equation_qualification": "Each mask bit records one of nine output-factor coordinate equalities in an exact formula replay; 'nine equations' does not claim algebraic independence.",
			"negative_scope":              semantic["negative_scope"],
		},
		"derived": map[string]any{"counts": semantic["counts"], "outcome": semantic["outcome"]},
	}, nil
}

func compareCanonicalJSON(expected, generated any) error {
	expectedBytes, err := canonicalJSON(expected)
	if err != nil {
		return err
	}
	generatedBytes, err := canonicalJSON(generated)
	if err != nil {
		return err
	}
	if !bytes.Equal(expectedBytes, generatedBytes) {
		return fmt.Errorf("canonical JSON differs")
	}
	return nil
}

func exactCorpusSection(corpus []byte, offset, size int, name string, generated []byte) error {
	if offset < 0 || size < 0 || offset > len(corpus) || size > len(corpus)-offset {
		return fmt.Errorf("corpus section %s exceeds authenticated corpus", name)
	}
	if !bytes.Equal(corpus[offset:offset+size], generated) {
		return fmt.Errorf("independently regenerated corpus section differs: %s", name)
	}
	return nil
}

func verifiedSummaryManifest(document map[string]any) ([]map[string]any, error) {
	semantic, ok := document["semantic"].(map[string]any)
	if !ok {
		return nil, fmt.Errorf("summary semantic object missing")
	}
	corpus, ok := semantic["corpus"].(map[string]any)
	if !ok {
		return nil, fmt.Errorf("summary corpus object missing")
	}
	raw, ok := corpus["sections"].([]any)
	if !ok || len(raw) != len(sectionOrder) {
		return nil, fmt.Errorf("summary section manifest length mismatch")
	}
	result := make([]map[string]any, len(raw))
	for index, value := range raw {
		record, ok := value.(map[string]any)
		if !ok {
			return nil, fmt.Errorf("summary section manifest record %d is not an object", index)
		}
		result[index] = record
	}
	return result, nil
}

func jsonInteger(value any) (int, error) {
	switch number := value.(type) {
	case json.Number:
		parsed, err := strconv.Atoi(number.String())
		return parsed, err
	case int:
		return number, nil
	default:
		return 0, fmt.Errorf("not an integer")
	}
}

func equalJSONNumber(value any, expected int) bool {
	actual, err := jsonInteger(value)
	return err == nil && actual == expected
}

func expectedSummaryDocument(semantic map[string]any, semanticDigest semanticDigestDeriver) (map[string]any, error) {
	semanticSHA256, err := semanticDigest(semantic)
	if err != nil {
		return nil, err
	}
	statement := "These integrity checksums report regular source-file bytes read at start and report time and require equality; they are not loaded-code attestation or authentication, and runtime/path diagnostics are outside the semantic digest."
	return map[string]any{
		"schema":         schema,
		"semantic":       semantic,
		"implementation": map[string]any{"source_repository_relative_id": sourceID, "source_at_start": map[string]any{"bytes": sourceSize, "sha256": sourceSHA256}, "source_at_report": map[string]any{"bytes": sourceSize, "sha256": sourceSHA256}, "statement": statement},
		"integrity":      map[string]any{"algorithm": "SHA-256", "classification": "integrity/checksums, not authentication", "semantic_digest_scope": "domain-separated canonical ASCII JSON encoding of the semantic object only", "semantic_sha256": semanticSHA256},
	}, nil
}
