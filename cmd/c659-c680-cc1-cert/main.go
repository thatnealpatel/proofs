package main

import (
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"os"
)

const usage = "Usage: c659-c680-cc1-cert C659_ROOT C680_ROOT C659_ALL_CHILD_CORPUS\n"

func main() {
	if err := run(os.Args[1:], os.Stdin, os.Stdout, os.Stderr); err != nil {
		if _, writeErr := fmt.Fprintf(os.Stderr, "%s: %v\n", commandName, err); writeErr != nil {
			os.Exit(2)
		}
		os.Exit(1)
	}
}

func run(args []string, stdin io.Reader, stdout, stderr io.Writer) error {
	_ = stdin
	if len(args) == 1 && (args[0] == "-h" || args[0] == "--help") {
		return writeAll(stdout, []byte(usage))
	}
	if len(args) != 3 {
		if err := writeAll(stderr, []byte(usage)); err != nil {
			return err
		}
		return fmt.Errorf("require exactly three authenticated file paths, got %d", len(args))
	}
	specs := []inputSpec{c659Spec.Input, c680Spec.Input, corpusSpec}
	inputs := make([][]byte, len(specs))
	for index, spec := range specs {
		value, err := readAuthenticated(args[index], spec)
		if err != nil {
			return err
		}
		inputs[index] = value
	}
	c659Root, err := parseRoot(inputs[0], c659Spec)
	if err != nil {
		return err
	}
	c680Root, err := parseRoot(inputs[1], c680Spec)
	if err != nil {
		return err
	}
	c659Frontier, err := enumerateFrontier(c659Root, "c659")
	if err != nil {
		return err
	}
	c680Frontier, err := enumerateFrontier(c680Root, "c680")
	if err != nil {
		return err
	}
	if err := verifyCorpusChildSection(inputs[2], c659Frontier.ClassPayloadStream); err != nil {
		return err
	}
	intersection := intersectExact(c659Frontier.Classes, c680Frontier.Classes)
	report := buildCertificate(c659Frontier, c680Frontier, intersection)
	encoded, err := json.MarshalIndent(report, "", "  ")
	if err != nil {
		return fmt.Errorf("encode certificate: %w", err)
	}
	encoded = append(encoded, '\n')
	if err := writeAll(stdout, encoded); err != nil {
		return fmt.Errorf("write certificate: %w", err)
	}
	return nil
}

func buildCertificate(c659, c680 *frontier, intersection [][]byte) certificate {
	orientationsReport := make([]orientationBinding, len(orientations))
	for index, positions := range orientations {
		orientationsReport[index] = orientationBinding{Index: index, Name: orientationNames[index], Positions: positions}
	}
	intersectionHex := make([]string, len(intersection))
	intersectionStream := make([]byte, 0, len(intersection)*childPayloadBytes)
	for index, payload := range intersection {
		intersectionHex[index] = hex.EncodeToString(payload)
		intersectionStream = append(intersectionStream, payload...)
	}
	result := "complete_no_common_exact_variant_0_one_plus_child_payload"
	if len(intersection) != 0 {
		result = "complete_common_exact_variant_0_one_plus_child_payload_found"
	}
	bindings := []inputBinding{
		binding(1, c659Spec.Input),
		binding(2, c680Spec.Input),
		binding(3, corpusSpec),
	}
	return certificate{
		Schema:              outputSchema,
		ExperimentID:        "CC-1a-c659-c680-variant0-one-plus-v1",
		Status:              "complete",
		Result:              result,
		AuthenticatedInputs: bindings,
		MoveContract: moveContractReport{
			Move:                     "one Plus replacement over GF(2)",
			Variant:                  0,
			RootTerms:                rootTerms,
			OrderedDistinctPairs:     rootTerms * (rootTerms - 1),
			Orientations:             orientationsReport,
			DescriptorOrder:          "first root slot increasing, then second root slot increasing excluding equality, then frozen orientation index increasing",
			DescriptorEncoding:       "little-endian <HHBB: first root slot, second root slot, orientation index, variant>",
			DescriptorsPerRoot:       orderedDescriptors,
			Constructor:              "each oriented source pair is replayed by internal/tensor.NewPlusReplacement on an exact two-term GF(2) scheme",
			IndependentReplay:        "constructor outputs must equal an independent uint16 XOR implementation of the frozen variant-0 formula after unorientation",
			ChildRequirement:         "every one of the 12,972 descriptor children per root is independently required to have 48 nonzero distinct terms and satisfy every Brent equation",
			Canonicalization:         "sort all 48 complete native-factor-position uint16 triples numerically; this removes term order only",
			CanonicalPayloadEncoding: "little-endian <4H header (4,4,4,48), then 48 sorted <HHH complete terms>",
			CanonicalPayloadBytes:    childPayloadBytes,
			EqualityRule:             "class formation and intersection ultimately require equality of all 296 canonical payload bytes; payload hashes are metadata only",
			HashCollisionDefense:     "a SHA-256 bucket containing differing complete payload bytes aborts certification",
		},
		Roots: []rootReport{
			makeRootReport("c659", c659Spec, c659),
			makeRootReport("c680", c680Spec, c680),
		},
		CorpusReplay: corpusReplayReport{
			InputRole:                  corpusSpec.Role,
			SectionID:                  "child_payloads",
			Offset:                     corpusChildOffset,
			Size:                       corpusChildSectionSize,
			AuthenticatedSectionSHA256: c659ChildStreamSHA256,
			RegeneratedStream:          makeStreamReport("c659.sorted_class_payloads", "6,486 lexicographically byte-sorted 296-byte canonical payloads", canonicalClasses, c659.ClassPayloadStream),
			ExactBytesEqual:            true,
		},
		ExactComparison: comparisonReport{
			Method:                        "two-pointer merge of the complete strictly sorted canonical class payloads using bytes.Compare and bytes.Equal",
			HashesUsedAsEqualityEvidence:  false,
			C659Classes:                   len(c659.Classes),
			C680Classes:                   len(c680.Classes),
			ExactIntersectionCount:        len(intersection),
			ExactUnionCount:               len(c659.Classes) + len(c680.Classes) - len(intersection),
			SortedIntersectionPayloadsHex: intersectionHex,
			IntersectionPayloadStream:     makeStreamReport("intersection.sorted_payloads", "concatenated sorted complete 296-byte common payloads", len(intersection), intersectionStream),
		},
		Scope: scopeReport{
			Established: "the exact term-permutation-canonical payload intersection of the two complete authenticated variant-0 one-Plus child frontiers in fixed native factor positions",
			Excluded: []string{
				"no sandwich, gauge, or orientation equivalence comparison",
				"no inverse claim",
				"no moat, rank, or minimality claim",
				"no Plus variants 1 or 2",
				"no roots other than the two authenticated frozen inputs",
				"no ordinary flips, paths longer than one Plus move, or global connectivity claim",
			},
		},
	}
}

func binding(position int, spec inputSpec) inputBinding {
	return inputBinding{
		ArgumentPosition:     position,
		Role:                 spec.Role,
		RepositoryRelativeID: spec.ID,
		Bytes:                spec.Size,
		SHA256:               spec.SHA256,
		Authenticated:        true,
	}
}

func makeRootReport(role string, spec rootSpec, value *frontier) rootReport {
	return rootReport{
		Role:                      role,
		Terms:                     rootTerms,
		OrderedFactorMajorPayload: rootPayloadBinding{Bytes: 290, SHA256: spec.OrderedSHA256},
		CanonicalRootPayload:      rootPayloadBinding{Bytes: 290, SHA256: spec.CanonicalSHA256},
		Nonzero:                   true,
		Distinct:                  true,
		BrentValid:                true,
		Frontier: frontierReport{
			OrderedDescriptors:                orderedDescriptors,
			ConstructorReplays:                value.ConstructorReplays,
			IndependentFormulaReplays:         value.FormulaReplays,
			NonzeroDistinctBrentValidChildren: value.ChildValidations,
			ExactCanonicalClasses:             len(value.Classes),
			AliasesPerClass:                   2,
			DescriptorStream: makeStreamReport(
				role+".descriptors",
				"enumeration-order little-endian <HHBB records",
				orderedDescriptors,
				value.DescriptorStream,
			),
			DescriptorCanonicalPayloadStream: makeStreamReport(
				role+".descriptor_payloads",
				"enumeration-order concatenated complete 296-byte canonical payloads",
				orderedDescriptors,
				value.DescriptorPayloadStream,
			),
			SortedClassPayloadStream: makeStreamReport(
				role+".sorted_class_payloads",
				"lexicographically byte-sorted distinct complete 296-byte canonical payloads",
				canonicalClasses,
				value.ClassPayloadStream,
			),
			SortedClassAliasStream: makeStreamReport(
				role+".sorted_class_aliases",
				"one little-endian <II pair of enumeration-order descriptor indices per sorted class",
				canonicalClasses,
				value.AliasStream,
			),
		},
	}
}

func makeStreamReport(id, encoding string, count int, value []byte) streamReport {
	return streamReport{
		ID:                    id,
		Encoding:              encoding,
		Count:                 count,
		Bytes:                 len(value),
		SHA256:                digest(value),
		DomainSeparatedSHA256: domainDigest(id, value),
	}
}
