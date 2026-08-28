package main

import (
	"bytes"
	"fmt"
	"io"
	"os"
	"slices"
	"sort"

	"patel.codes/proofs/internal/ring"
	"patel.codes/proofs/internal/tensor"
)

type rootState struct {
	Scheme                         tensor.Scheme
	OrderedFactorMajorPayloadBytes []byte
	Certificate                    rootCandidateCertificate
}

type plusState struct {
	Scheme      tensor.Scheme
	Certificate plusCertificate
}

type uniqueOutputState struct {
	Scheme    tensor.Scheme
	Canonical []byte
	Public    uniqueOutput
}

type experimentCounts struct {
	Rejected         int
	Classes          int
	DefectZero       int
	DefectOne        int
	DefectAtLeastTwo int
	Reductions       int
	ReductionHashes  []string
}

func executeExperiment(c659Path, c680Path string) (semanticCertificate, error) {
	c659Root, err := loadRootCandidate(c659Path, declaredRootSpecs[0])
	if err != nil {
		return semanticCertificate{}, err
	}
	c680Root, err := loadRootCandidate(c680Path, declaredRootSpecs[1])
	if err != nil {
		return semanticCertificate{}, err
	}
	rootSelection, selectedRoot, err := selectDeclaredRoots([2]rootState{c659Root, c680Root}, c659RootID)
	if err != nil {
		return semanticCertificate{}, err
	}
	plus, err := constructFixedPlus(selectedRoot.Scheme)
	if err != nil {
		return semanticCertificate{}, err
	}
	attempts, records, uniqueStates, counts, err := enumerateFlips(plus.Scheme)
	if err != nil {
		return semanticCertificate{}, err
	}
	for index := range uniqueStates {
		screens, screenCounts, err := screenUniqueOutput(uniqueStates[index].Scheme, uniqueStates[index].Public.UnorderedSHA256)
		if err != nil {
			return semanticCertificate{}, fmt.Errorf("screen unique output %d: %w", index, err)
		}
		uniqueStates[index].Public.Screens = screens
		counts.Classes += screenCounts.Classes
		counts.DefectZero += screenCounts.DefectZero
		counts.DefectOne += screenCounts.DefectOne
		counts.DefectAtLeastTwo += screenCounts.DefectAtLeastTwo
		counts.Reductions += screenCounts.Reductions
		counts.ReductionHashes = append(counts.ReductionHashes, screenCounts.ReductionHashes...)
	}
	uniqueOutputs := make([]uniqueOutput, len(uniqueStates))
	for index := range uniqueStates {
		uniqueOutputs[index] = uniqueStates[index].Public
	}
	if err := enforceExperimentCounts(attempts, records, uniqueOutputs, counts); err != nil {
		return semanticCertificate{}, err
	}
	accepted := make([]descriptorHash, len(records))
	for index, record := range records {
		accepted[index] = descriptorHash{Descriptor: record.Descriptor, SHA256: record.Result.UnorderedCanonicalSHA256}
	}
	coverage := coverageCertificate{
		SlotCount:                  expectedPlusChildTerms,
		OrderedDistinctSlotPairs:   expectedPlusChildTerms * (expectedPlusChildTerms - 1),
		SharedModes:                []int{0, 1, 2},
		Coefficient:                1,
		DeclaredCandidates:         expectedCandidateCount,
		RecordedAttempts:           len(attempts),
		Accepted:                   len(records),
		Rejected:                   counts.Rejected,
		RejectionsByCode:           []countByCode{{Code: "shared_factors_not_literally_equal", Count: counts.Rejected}},
		UniqueUnorderedOutputs:     len(uniqueOutputs),
		MaximalClasses:             counts.Classes,
		DefectZeroClasses:          counts.DefectZero,
		DefectOneClasses:           counts.DefectOne,
		DefectAtLeastTwoClasses:    counts.DefectAtLeastTwo,
		ReplayedPositiveReductions: counts.Reductions,
		Complete:                   true,
		DomainStatement:            "all 48*47*3 ordered distinct-slot/shared-mode ordinary-flip candidates with coefficient 1 on the fixed Plus child",
	}
	return semanticCertificate{
		Schema:     certificateSchema,
		Experiment: "exact fixed selected-c659 variant-0 one-Plus/one-ordinary-flip maximal-class experiment after declared c659/c680 root selection",
		Encodings: encodingCertificate{
			FactorWord:          "4x4 binary matrix as uint16; row-major entry index is the bit index; uint16 bytes are little-endian",
			Header:              "little-endian <4H>: dimension_0, dimension_1, dimension_2, term_count",
			UnorderedCanonical:  "header followed by numeric-lexicographically sorted term triples, each term encoded as little-endian <3H>",
			OrderedRootPayload:  "header followed by little-endian uint16 factor words in factor-major then root-slot order",
			ClassRows:           "16 uint16 rows of the GF(2) complementary outer-product sum; complementary modes are increasing and row/column bit indices are 0 through 15",
			ClassRowHash:        "SHA-256 of exactly 16 little-endian uint16 rows with no header",
			SemanticDigestInput: "compact encoding/json serialization of the semantic object only",
		},
		RootSelection: rootSelection,
		PriorScan:     makePriorScanBinding(),
		FixedPlus:     plus.Certificate,
		Coverage:      coverage,
		Attempts:      attempts,
		Records:       records,
		UniqueOutputs: uniqueOutputs,
		Summary: summaryCertificate{
			AcceptedDescriptors:        accepted,
			ReductionResultHashes:      counts.ReductionHashes,
			ResultClassification:       "four exact defect-one reductions recover 47-term presentations with the authenticated selected c659 root unordered hash",
			ScopedNegative:             "no defect-two class exists among the ten maximal classes of the four unique accepted one-flip outputs; this says nothing beyond this fixed representative slice",
			FullClassTheoremUse:        "each defect-zero maximal literal equal-factor class excludes every positive-defect proper subset of that class",
			CanonicalMinimumProved:     false,
			TensorRankMinimumProved:    false,
			PresentationUpperBoundOnly: true,
		},
	}, nil
}

func loadRootCandidate(path string, spec rootSpec) (rootState, error) {
	file, err := os.Open(path)
	if err != nil {
		return rootState{}, fmt.Errorf("open declared %s root: %w", spec.Role, err)
	}
	defer file.Close()
	raw, rawHash, err := readAuthenticatedRoot(file, spec)
	if err != nil {
		return rootState{}, fmt.Errorf("authenticate declared %s root: %w", spec.Role, err)
	}
	scheme, err := tensor.ParseNative(ring.Z2, bytes.NewReader(raw))
	if err != nil {
		return rootState{}, fmt.Errorf("parse declared %s root: %w", spec.Role, err)
	}
	if scheme.Ring() != ring.Z2 {
		return rootState{}, fmt.Errorf("declared %s root ring is %d, want Z2", spec.Role, scheme.Ring())
	}
	if scheme.Dimensions() != expectedDimensions {
		return rootState{}, fmt.Errorf("declared %s root dimensions are %v, want %v", spec.Role, scheme.Dimensions(), expectedDimensions)
	}
	if scheme.TermCount() != expectedRootTerms {
		return rootState{}, fmt.Errorf("declared %s root has %d terms, want %d", spec.Role, scheme.TermCount(), expectedRootTerms)
	}
	ordered, err := orderedFactorMajorBytes(scheme)
	if err != nil {
		return rootState{}, fmt.Errorf("encode declared %s root ordered factor-major payload: %w", spec.Role, err)
	}
	if len(ordered) != expectedRootOrderedFactorMajorPayloadBytes {
		return rootState{}, fmt.Errorf("declared %s root ordered factor-major payload has %d bytes, want %d", spec.Role, len(ordered), expectedRootOrderedFactorMajorPayloadBytes)
	}
	orderedHash := sha256Hex(ordered)
	if orderedHash != spec.OrderedFactorMajorSHA256 {
		return rootState{}, fmt.Errorf("declared %s root ordered factor-major SHA-256 is %s, want %s", spec.Role, orderedHash, spec.OrderedFactorMajorSHA256)
	}
	canonicalHashValue, _, err := canonicalHash(scheme)
	if err != nil {
		return rootState{}, fmt.Errorf("encode declared %s root unordered canonical form: %w", spec.Role, err)
	}
	if canonicalHashValue != spec.UnorderedCanonicalSHA256 {
		return rootState{}, fmt.Errorf("declared %s root unordered canonical SHA-256 is %s, want %s", spec.Role, canonicalHashValue, spec.UnorderedCanonicalSHA256)
	}
	checks, err := validateSchemeSeparately(scheme)
	if err != nil {
		return rootState{}, fmt.Errorf("validate declared %s root: %w", spec.Role, err)
	}
	literal, err := literalFactorScreen(scheme)
	if err != nil {
		return rootState{}, fmt.Errorf("screen declared %s root literal factors: %w", spec.Role, err)
	}
	if literal.NonzeroFactors != literal.FactorOccurrences || literal.RepeatedClasses != 0 || literal.RepeatedPairs != 0 {
		return rootState{}, fmt.Errorf("declared %s root literal factor screen has %d/%d nonzero factors, %d repeated classes, and %d repeated pairs", spec.Role, literal.NonzeroFactors, literal.FactorOccurrences, literal.RepeatedClasses, literal.RepeatedPairs)
	}
	return rootState{
		Scheme:                         scheme,
		OrderedFactorMajorPayloadBytes: append([]byte(nil), ordered...),
		Certificate: rootCandidateCertificate{
			ArgumentPosition:               spec.ArgumentPosition,
			Role:                           spec.Role,
			ID:                             spec.ID,
			RootFileName:                   spec.RootFileName,
			Ring:                           "GF(2)",
			Dimensions:                     scheme.Dimensions(),
			TermCount:                      scheme.TermCount(),
			RawBytes:                       len(raw),
			RawSHA256:                      rawHash,
			OrderedFactorMajorPayloadBytes: len(ordered),
			OrderedFactorMajorSHA256:       orderedHash,
			UnorderedCanonicalSHA256:       canonicalHashValue,
			Checks:                         checks,
			LiteralFactorScreening:         literal,
		},
	}, nil
}

func readAuthenticatedRoot(reader io.Reader, spec rootSpec) ([]byte, string, error) {
	if spec.RawBytes < 0 {
		return nil, "", fmt.Errorf("%s root declares invalid raw byte count %d", spec.Role, spec.RawBytes)
	}
	raw, err := io.ReadAll(io.LimitReader(reader, int64(spec.RawBytes)+1))
	if err != nil {
		return nil, "", err
	}
	if len(raw) != spec.RawBytes {
		return nil, "", fmt.Errorf("%s root has %d raw bytes, want %d", spec.Role, len(raw), spec.RawBytes)
	}
	rawHash := sha256Hex(raw)
	if rawHash != spec.RawSHA256 {
		return nil, "", fmt.Errorf("%s root raw SHA-256 is %s, want %s", spec.Role, rawHash, spec.RawSHA256)
	}
	return raw, rawHash, nil
}

func selectDeclaredRoots(candidates [2]rootState, requiredRootID string) (rootSelectionCertificate, rootState, error) {
	for index, candidate := range candidates {
		spec := declaredRootSpecs[index]
		if candidate.Certificate.ArgumentPosition != spec.ArgumentPosition || candidate.Certificate.Role != spec.Role || candidate.Certificate.ID != spec.ID {
			return rootSelectionCertificate{}, rootState{}, fmt.Errorf("declared root candidate %d identity is position %d role %q ID %q, want position %d role %q ID %q", index, candidate.Certificate.ArgumentPosition, candidate.Certificate.Role, candidate.Certificate.ID, spec.ArgumentPosition, spec.Role, spec.ID)
		}
		if err := validateLowercaseSHA256Hex(candidate.Certificate.OrderedFactorMajorSHA256); err != nil {
			return rootSelectionCertificate{}, rootState{}, fmt.Errorf("declared %s root ordered factor-major SHA-256 binding: %w", spec.Role, err)
		}
		if len(candidate.OrderedFactorMajorPayloadBytes) != candidate.Certificate.OrderedFactorMajorPayloadBytes {
			return rootSelectionCertificate{}, rootState{}, fmt.Errorf("declared %s root authenticated ordered factor-major payload has %d bytes, certificate binds %d", spec.Role, len(candidate.OrderedFactorMajorPayloadBytes), candidate.Certificate.OrderedFactorMajorPayloadBytes)
		}
		payloadHash := sha256Hex(candidate.OrderedFactorMajorPayloadBytes)
		if payloadHash != candidate.Certificate.OrderedFactorMajorSHA256 {
			return rootSelectionCertificate{}, rootState{}, fmt.Errorf("declared %s root authenticated ordered factor-major payload SHA-256 is %s, certificate binds %s", spec.Role, payloadHash, candidate.Certificate.OrderedFactorMajorSHA256)
		}
	}
	left := candidates[0]
	right := candidates[1]
	leftDigest := left.Certificate.OrderedFactorMajorSHA256
	rightDigest := right.Certificate.OrderedFactorMajorSHA256
	commonPrefixCharacters := 0
	for commonPrefixCharacters < len(leftDigest) && leftDigest[commonPrefixCharacters] == rightDigest[commonPrefixCharacters] {
		commonPrefixCharacters++
	}
	var firstDifference *rootDigestCharacterDifference
	if commonPrefixCharacters < len(leftDigest) {
		leftCharacter := leftDigest[commonPrefixCharacters]
		rightCharacter := rightDigest[commonPrefixCharacters]
		firstDifference = &rootDigestCharacterDifference{
			ZeroBasedPosition: commonPrefixCharacters,
			LeftCharacter:     string(leftCharacter),
			RightCharacter:    string(rightCharacter),
			LeftASCII:         int(leftCharacter),
			RightASCII:        int(rightCharacter),
		}
	}
	compareResult := 0
	if leftDigest < rightDigest {
		compareResult = -1
	} else if leftDigest > rightDigest {
		compareResult = 1
	}
	result := "digests_equal"
	selectedIndex := -1
	if compareResult < 0 {
		result = "left_digest_less_than_right_digest"
		selectedIndex = 0
	} else if compareResult > 0 {
		result = "right_digest_less_than_left_digest"
		selectedIndex = 1
	}
	comparison := rootComparisonCertificate{
		Rule:           "lexicographically compare the bound 64-character lowercase SHA-256 hexadecimal digest strings bytewise in ASCII order; the lower character at the first difference wins",
		DigestEncoding: "64-character lowercase hexadecimal SHA-256 digest of the complete ordered factor-major root payload",
		Left: rootDigestBinding{
			RootID: left.Certificate.ID,
			Digest: leftDigest,
		},
		Right: rootDigestBinding{
			RootID: right.Certificate.ID,
			Digest: rightDigest,
		},
		CommonPrefixCharacters: commonPrefixCharacters,
		FirstDifference:        firstDifference,
		CompareResult:          compareResult,
		Result:                 result,
	}
	if selectedIndex < 0 {
		return rootSelectionCertificate{
			DeclaredArgumentRoles:  []string{c659RootRole, c680RootRole},
			Candidates:             []rootCandidateCertificate{left.Certificate, right.Certificate},
			Comparison:             comparison,
			RequiredSelectedRootID: requiredRootID,
		}, rootState{}, fmt.Errorf("declared c659 and c680 root ordered factor-major SHA-256 digest strings are equal; strict least root is undefined")
	}
	selected := candidates[selectedIndex]
	selection := rootSelectionCertificate{
		DeclaredArgumentRoles:     []string{c659RootRole, c680RootRole},
		Candidates:                []rootCandidateCertificate{left.Certificate, right.Certificate},
		Comparison:                comparison,
		SelectedRootID:            selected.Certificate.ID,
		RequiredSelectedRootID:    requiredRootID,
		RequiredSelectionVerified: selected.Certificate.ID == requiredRootID,
	}
	if !selection.RequiredSelectionVerified {
		return selection, rootState{}, fmt.Errorf("declared root selection chose %s, require %s before running the fixed experiment", selection.SelectedRootID, requiredRootID)
	}
	return selection, selected, nil
}

func validateLowercaseSHA256Hex(value string) error {
	if len(value) != 64 {
		return fmt.Errorf("digest has %d characters, want 64", len(value))
	}
	for position := range len(value) {
		character := value[position]
		if (character < '0' || character > '9') && (character < 'a' || character > 'f') {
			return fmt.Errorf("digest character %d is %q, want lowercase hexadecimal", position, character)
		}
	}
	return nil
}

func validateSchemeSeparately(scheme tensor.Scheme) (schemeChecks, error) {
	if err := tensor.ValidateBrent(scheme); err != nil {
		return schemeChecks{}, fmt.Errorf("Brent replay: %w", err)
	}
	if err := tensor.ValidateNonzeroTerms(scheme); err != nil {
		return schemeChecks{BrentReplay: true}, fmt.Errorf("nonzero terms: %w", err)
	}
	if err := tensor.ValidateDistinctTensors(scheme); err != nil {
		return schemeChecks{BrentReplay: true, NonzeroTerms: true}, fmt.Errorf("distinct rank-one terms: %w", err)
	}
	return schemeChecks{BrentReplay: true, NonzeroTerms: true, DistinctRankOneTerms: true}, nil
}

func literalFactorScreen(scheme tensor.Scheme) (literalFactorCheck, error) {
	words, err := schemeWords(scheme)
	if err != nil {
		return literalFactorCheck{}, err
	}
	result := literalFactorCheck{FactorOccurrences: 3 * len(words)}
	for mode := range 3 {
		counts := make(map[uint16]int)
		for _, term := range words {
			word := term[mode]
			if word != 0 {
				result.NonzeroFactors++
			}
			counts[word]++
		}
		for word, count := range counts {
			if word != 0 && count >= 2 {
				result.RepeatedClasses++
				result.RepeatedPairs += count * (count - 1) / 2
			}
		}
	}
	return result, nil
}

func makePriorScanBinding() priorScanBinding {
	return priorScanBinding{
		Status:                                  "declared c659/c680 root selection closed by this command; binding to an independently completed c659 Plus scan",
		DeclaredTwoRootSelectionClosedByCommand: true,
		C659PlusScanRecomputedByCommand:         false,
		DescriptorStreamSHA256:                  expectedPriorDescriptorSHA256,
		Domain: priorScanDomain{
			Root:                  c659RootID,
			RootSlotPairs:         1081,
			RootSlotOrders:        2,
			OuterOrientations:     6,
			PlusVariant:           0,
			OrderedDescriptors:    expectedPriorPlusDescriptors,
			UniqueOutputs:         expectedPriorUniquePlusOutputs,
			EqualFactorSubsets:    expectedPriorEqualFactorSubsets,
			PositiveDefectSubsets: expectedPriorPositiveDefectSubsets,
		},
		Selection: priorScanSelection{
			RootRule:    "least 64-character lowercase SHA-256 hexadecimal digest string of the complete ordered factor-major payload among exactly the authenticated declared c659 and c680 roots, compared bytewise in ASCII order and replayed in root_selection by this command",
			OutputRule:  priorScanOutputRule,
			RootSlots:   plusRootSlots,
			Orientation: "ikj",
			ChildSHA256: expectedPlusChildSHA256,
		},
		C659PlusOutputMinimumProvedByCommand: false,
		BindingStatement:                     "root_selection closes only the declared two-root c659/c680 choice; the prior c659 variant-0 Plus scan remains bound by its descriptor-stream SHA-256 and selected child hash and is not recomputed by this command",
	}
}

func constructFixedPlus(root tensor.Scheme) (plusState, error) {
	oriented := make([]tensor.RankOneTerm, 2)
	for index, slot := range plusRootSlots {
		term, err := orientTerm(root.Term(slot), plusOrientation)
		if err != nil {
			return plusState{}, fmt.Errorf("orient root slot %d: %w", slot, err)
		}
		oriented[index] = term
	}
	temporary, err := tensor.NewScheme(oriented)
	if err != nil {
		return plusState{}, fmt.Errorf("construct oriented temporary pair: %w", err)
	}
	temporaryReplacement, err := tensor.NewPlusReplacement(temporary, 0, 1)
	if err != nil {
		return plusState{}, fmt.Errorf("tensor.NewPlusReplacement on oriented temporary pair: %w", err)
	}
	orientedInserted := temporaryReplacement.InsertedTerms()
	inserted := make([]tensor.RankOneTerm, len(orientedInserted))
	for index, term := range orientedInserted {
		inserted[index], err = unorientTerm(term, plusOrientation)
		if err != nil {
			return plusState{}, fmt.Errorf("unorient insertion %d: %w", index, err)
		}
	}
	replacement, err := tensor.NewReplacement(plusRootSlots[:], inserted)
	if err != nil {
		return plusState{}, fmt.Errorf("construct root Plus replacement: %w", err)
	}
	if err := tensor.ValidateReplacement(root, replacement); err != nil {
		return plusState{}, fmt.Errorf("validate root Plus replacement: %w", err)
	}
	witness, err := makeReplacementWitness(root, replacement, "tensor.NewReplacement from tensor.NewPlusReplacement on oriented temporary pair")
	if err != nil {
		return plusState{}, fmt.Errorf("record root Plus replacement: %w", err)
	}
	if !slices.Equal(witness.InsertedTerms, expectedPlusInserted) {
		return plusState{}, fmt.Errorf("Plus inserted terms are %v, want %v", witness.InsertedTerms, expectedPlusInserted)
	}
	child, err := tensor.ApplyReplacement(root, replacement)
	if err != nil {
		return plusState{}, fmt.Errorf("apply root Plus replacement: %w", err)
	}
	if child.TermCount() != expectedPlusChildTerms {
		return plusState{}, fmt.Errorf("Plus child has %d terms, want %d", child.TermCount(), expectedPlusChildTerms)
	}
	order := makeOutputOrder(root.TermCount(), replacement.RemovedSlots(), len(replacement.InsertedTerms()))
	if !slices.Equal(order.InsertionResultSlots, plusInsertionSlots[:]) || len(order.SurvivorParentSlots) != 45 {
		return plusState{}, fmt.Errorf("Plus output order has survivor count %d and insertion slots %v", len(order.SurvivorParentSlots), order.InsertionResultSlots)
	}
	if err := verifyOutputOrder(root, child, replacement, order); err != nil {
		return plusState{}, fmt.Errorf("verify Plus output order: %w", err)
	}
	result, _, err := checkedSchemeResult(child)
	if err != nil {
		return plusState{}, fmt.Errorf("validate Plus child: %w", err)
	}
	if result.UnorderedCanonicalSHA256 != expectedPlusChildSHA256 {
		return plusState{}, fmt.Errorf("Plus child unordered canonical SHA-256 is %s, want %s", result.UnorderedCanonicalSHA256, expectedPlusChildSHA256)
	}
	return plusState{
		Scheme: child,
		Certificate: plusCertificate{
			Descriptor: plusDescriptor{
				Kind:                 "oriented Plus",
				Variant:              0,
				RootSlots:            plusRootSlots,
				SlotIndexing:         "zero-based",
				OrientationName:      "ikj",
				OrientationPositions: plusOrientation,
			},
			Adaptation: []string{
				"copy selected c659 root slots 7 and 13 into a two-term temporary scheme",
				"orient each temporary term by positions (0,2,1)",
				"call tensor.NewPlusReplacement on temporary slots (0,1)",
				"unorient all three insertion terms by the inverse position map",
				"call tensor.NewReplacement on selected c659 root slots (7,13), validate, and apply",
			},
			TemporaryPairSlots: [2]int{0, 1},
			Replacement:        witness,
			OutputOrder:        order,
			Child:              result,
		},
	}, nil
}

func orientTerm(term tensor.RankOneTerm, positions [3]int) (tensor.RankOneTerm, error) {
	if err := validateOrientation(positions); err != nil {
		return tensor.RankOneTerm{}, err
	}
	return tensor.NewRankOneTerm(
		term.Factor(positions[0]),
		term.Factor(positions[1]),
		term.Factor(positions[2]),
	)
}

func unorientTerm(term tensor.RankOneTerm, positions [3]int) (tensor.RankOneTerm, error) {
	if err := validateOrientation(positions); err != nil {
		return tensor.RankOneTerm{}, err
	}
	var factors [3]tensor.Matrix
	for orientedMode, sourceMode := range positions {
		factors[sourceMode] = term.Factor(orientedMode)
	}
	return tensor.NewRankOneTerm(factors[0], factors[1], factors[2])
}

func validateOrientation(positions [3]int) error {
	seen := [3]bool{}
	for index, position := range positions {
		if position < 0 || position >= 3 {
			return fmt.Errorf("orientation position %d is %d, outside 0 through 2", index, position)
		}
		if seen[position] {
			return fmt.Errorf("orientation repeats position %d", position)
		}
		seen[position] = true
	}
	return nil
}

func enumerateFlips(parent tensor.Scheme) ([]attemptCertificate, []flipRecord, []uniqueOutputState, experimentCounts, error) {
	attempts := make([]attemptCertificate, 0, expectedCandidateCount)
	records := make([]flipRecord, 0, expectedAcceptedCount)
	uniqueStates := make([]uniqueOutputState, 0, expectedUniqueOutputCount)
	uniqueByHash := make(map[string]int)
	counts := experimentCounts{}
	sequence := 0
	for firstSlot := range parent.TermCount() {
		for secondSlot := range parent.TermCount() {
			if firstSlot == secondSlot {
				continue
			}
			for sharedMode := range 3 {
				descriptor := flipDescriptor{FirstSlot: firstSlot, SecondSlot: secondSlot, SharedMode: sharedMode, Coefficient: 1}
				replacement, err := tensor.NewOrdinaryFlipReplacement(parent, tensor.SharedMode(sharedMode), firstSlot, secondSlot, 1)
				if err != nil {
					if !ordinaryFlipHasLiteralInequality(parent, descriptor) {
						return nil, nil, nil, counts, fmt.Errorf("candidate %d %v failed unexpectedly: %w", sequence, descriptor, err)
					}
					attempts = append(attempts, attemptCertificate{
						Sequence:   sequence,
						Descriptor: descriptor,
						Outcome:    "rejected",
						Rejection: &rejectionRecord{
							Code:             "shared_factors_not_literally_equal",
							ConstructorError: err.Error(),
						},
						AcceptedRecord: nil,
						OutputSHA256:   nil,
					})
					counts.Rejected++
					sequence++
					continue
				}
				if err := tensor.ValidateReplacement(parent, replacement); err != nil {
					return nil, nil, nil, counts, fmt.Errorf("validate accepted candidate %d %v: %w", sequence, descriptor, err)
				}
				witness, err := makeReplacementWitness(parent, replacement, "tensor.NewOrdinaryFlipReplacement")
				if err != nil {
					return nil, nil, nil, counts, fmt.Errorf("record accepted candidate %d %v: %w", sequence, descriptor, err)
				}
				resultScheme, err := tensor.ApplyReplacement(parent, replacement)
				if err != nil {
					return nil, nil, nil, counts, fmt.Errorf("apply accepted candidate %d %v: %w", sequence, descriptor, err)
				}
				order := makeOutputOrder(parent.TermCount(), replacement.RemovedSlots(), len(replacement.InsertedTerms()))
				if err := verifyOutputOrder(parent, resultScheme, replacement, order); err != nil {
					return nil, nil, nil, counts, fmt.Errorf("verify accepted candidate %d output order: %w", sequence, err)
				}
				result, canonical, err := checkedSchemeResult(resultScheme)
				if err != nil {
					return nil, nil, nil, counts, fmt.Errorf("validate accepted candidate %d %v: %w", sequence, descriptor, err)
				}
				expectedHash, ok := preregisteredFlipHash(descriptor)
				if !ok {
					return nil, nil, nil, counts, fmt.Errorf("candidate %d produced an unregistered accepted descriptor %v with hash %s", sequence, descriptor, result.UnorderedCanonicalSHA256)
				}
				if result.UnorderedCanonicalSHA256 != expectedHash {
					return nil, nil, nil, counts, fmt.Errorf("candidate %d %v hash is %s, want %s", sequence, descriptor, result.UnorderedCanonicalSHA256, expectedHash)
				}
				recordIndex := len(records)
				uniqueIndex, exists := uniqueByHash[result.UnorderedCanonicalSHA256]
				if exists {
					if !bytes.Equal(uniqueStates[uniqueIndex].Canonical, canonical) {
						return nil, nil, nil, counts, fmt.Errorf("unordered SHA-256 collision at candidate %d", sequence)
					}
				} else {
					uniqueIndex = len(uniqueStates)
					uniqueByHash[result.UnorderedCanonicalSHA256] = uniqueIndex
					uniqueStates = append(uniqueStates, uniqueOutputState{
						Scheme:    resultScheme,
						Canonical: append([]byte(nil), canonical...),
						Public: uniqueOutput{
							Index:                uniqueIndex,
							DedupeKey:            "SHA-256 of unordered canonical bytes",
							UnorderedSHA256:      result.UnorderedCanonicalSHA256,
							RepresentativeRecord: recordIndex,
							Lineages:             make([]lineageReference, 0, 1),
							RepresentativeTerms:  append([]wordTriple(nil), result.OrderedTerms...),
							Screens:              make([]classScreen, 0),
						},
					})
				}
				uniqueStates[uniqueIndex].Public.Lineages = append(uniqueStates[uniqueIndex].Public.Lineages, lineageReference{
					Record:          recordIndex,
					AttemptSequence: sequence,
					Descriptor:      descriptor,
				})
				records = append(records, flipRecord{
					Record:          recordIndex,
					AttemptSequence: sequence,
					Descriptor:      descriptor,
					ParentSHA256:    expectedPlusChildSHA256,
					Replacement:     witness,
					OutputOrder:     order,
					Result:          result,
					UniqueOutput:    uniqueIndex,
				})
				outputHash := result.UnorderedCanonicalSHA256
				attempts = append(attempts, attemptCertificate{
					Sequence:       sequence,
					Descriptor:     descriptor,
					Outcome:        "accepted",
					Rejection:      nil,
					AcceptedRecord: intPointer(recordIndex),
					OutputSHA256:   stringPointer(outputHash),
				})
				sequence++
			}
		}
	}
	if sequence != expectedCandidateCount {
		return nil, nil, nil, counts, fmt.Errorf("enumerated %d candidates, want %d", sequence, expectedCandidateCount)
	}
	if err := enforcePreregisteredRecords(records); err != nil {
		return nil, nil, nil, counts, err
	}
	return attempts, records, uniqueStates, counts, nil
}

func ordinaryFlipHasLiteralInequality(scheme tensor.Scheme, descriptor flipDescriptor) bool {
	if descriptor.SharedMode < 0 || descriptor.SharedMode >= 3 ||
		descriptor.FirstSlot < 0 || descriptor.FirstSlot >= scheme.TermCount() ||
		descriptor.SecondSlot < 0 || descriptor.SecondSlot >= scheme.TermCount() ||
		descriptor.FirstSlot == descriptor.SecondSlot ||
		!scheme.Ring().Valid() || scheme.Ring().Normalize(descriptor.Coefficient) == 0 ||
		!schemeStructureIsValid(scheme) {
		return false
	}
	first := scheme.Term(descriptor.FirstSlot).Factor(descriptor.SharedMode)
	second := scheme.Term(descriptor.SecondSlot).Factor(descriptor.SharedMode)
	if matrixIsStructurallyZero(first) {
		return false
	}
	return !matricesAreStructurallyEqual(first, second)
}

func schemeStructureIsValid(scheme tensor.Scheme) bool {
	dimensions := scheme.Dimensions()
	for mode := range 3 {
		rows := dimensions[mode]
		columns := dimensions[(mode+1)%3]
		if rows <= 0 || columns <= 0 || rows > int(^uint(0)>>1)/columns {
			return false
		}
		for slot := range scheme.TermCount() {
			factor := scheme.Term(slot).Factor(mode)
			if factor.Ring() != scheme.Ring() || factor.Rows() != rows || factor.Columns() != columns || len(factor.Entries()) != rows*columns {
				return false
			}
		}
	}
	return true
}

func matrixIsStructurallyZero(matrix tensor.Matrix) bool {
	for _, entry := range matrix.Entries() {
		if entry != 0 {
			return false
		}
	}
	return true
}

func matricesAreStructurallyEqual(first, second tensor.Matrix) bool {
	return first.Ring() == second.Ring() &&
		first.Rows() == second.Rows() &&
		first.Columns() == second.Columns() &&
		slices.Equal(first.Entries(), second.Entries())
}

func preregisteredFlipHash(descriptor flipDescriptor) (string, bool) {
	for _, expected := range expectedFlips {
		if expected.Descriptor == descriptor {
			return expected.Hash, true
		}
	}
	return "", false
}

func enforcePreregisteredRecords(records []flipRecord) error {
	if len(records) != len(expectedFlips) {
		return fmt.Errorf("accepted %d descriptors, want %d", len(records), len(expectedFlips))
	}
	for index, expected := range expectedFlips {
		if records[index].Descriptor != expected.Descriptor {
			return fmt.Errorf("accepted descriptor %d is %v, want %v", index, records[index].Descriptor, expected.Descriptor)
		}
		if records[index].Result.UnorderedCanonicalSHA256 != expected.Hash {
			return fmt.Errorf("accepted descriptor %d hash is %s, want %s", index, records[index].Result.UnorderedCanonicalSHA256, expected.Hash)
		}
	}
	return nil
}

func screenUniqueOutput(scheme tensor.Scheme, outputHash string) ([]classScreen, experimentCounts, error) {
	terms, err := schemeWords(scheme)
	if err != nil {
		return nil, experimentCounts{}, err
	}
	screens := make([]classScreen, 0)
	counts := experimentCounts{}
	matchedReductions := make(map[int]bool)
	for mode := range 3 {
		groups := make(map[uint16][]int)
		for slot, term := range terms {
			groups[term[mode]] = append(groups[term[mode]], slot)
		}
		factors := make([]int, 0, len(groups))
		for factor, slots := range groups {
			if factor != 0 && len(slots) >= 2 {
				factors = append(factors, int(factor))
			}
		}
		sort.Ints(factors)
		for _, factorValue := range factors {
			factor := uint16(factorValue)
			slots := append([]int(nil), groups[factor]...)
			rows, complementaryModes, err := complementaryRows(terms, slots, mode)
			if err != nil {
				return nil, counts, err
			}
			elimination := eliminateRows(rows)
			defect := len(slots) - elimination.Rank
			if defect < 0 {
				return nil, counts, fmt.Errorf("mode %d factor %d has class size %d below rank %d", mode, factor, len(slots), elimination.Rank)
			}
			classTerms := make([]wordTriple, len(slots))
			for index, slot := range slots {
				classTerms[index] = terms[slot]
			}
			screen := classScreen{
				Screen:                len(screens),
				SharedMode:            mode,
				SharedFactorWord:      factor,
				SharedFactorHex:       fmt.Sprintf("%04x", factor),
				Nonzero:               true,
				Maximal:               true,
				Slots:                 slots,
				Terms:                 classTerms,
				ComplementaryModes:    complementaryModes,
				Rows:                  rows,
				RowsSHA256:            rowsHash(rows),
				Elimination:           elimination,
				ClassSize:             len(slots),
				Rank:                  elimination.Rank,
				Defect:                defect,
				ProperSubsetsExcluded: defect == 0,
				Reduction:             nil,
			}
			counts.Classes++
			switch {
			case defect == 0:
				counts.DefectZero++
				screen.Conclusion = "zero defect; every proper subset is also nondeficient by full-maximal-class monotonicity"
			case defect == 1:
				counts.DefectOne++
				screen.Conclusion = "defect one; exact shared-factor reduction replayed"
			default:
				counts.DefectAtLeastTwo++
				screen.Conclusion = "defect at least two; exact shared-factor reduction replayed"
			}
			if defect > 0 {
				reduction, err := replayReduction(scheme, outputHash, mode, slots)
				if err != nil {
					return nil, counts, fmt.Errorf("mode %d factor %d reduction: %w", mode, factor, err)
				}
				screen.Reduction = &reduction
				counts.Reductions++
				counts.ReductionHashes = append(counts.ReductionHashes, reduction.Result.UnorderedCanonicalSHA256)
				registeredIndex, ok := preregisteredReductionIndex(outputHash, mode)
				if !ok {
					return nil, counts, fmt.Errorf("positive class at output %s mode %d is not preregistered", outputHash, mode)
				}
				if matchedReductions[registeredIndex] {
					return nil, counts, fmt.Errorf("preregistered reduction %d matched more than once", registeredIndex)
				}
				matchedReductions[registeredIndex] = true
			}
			screens = append(screens, screen)
		}
	}
	return screens, counts, nil
}

func replayReduction(parent tensor.Scheme, outputHash string, mode int, slots []int) (reductionCertificate, error) {
	replacement, err := tensor.NewSharedFactorReduction(parent, tensor.SharedMode(mode), slots)
	if err != nil {
		return reductionCertificate{}, fmt.Errorf("tensor.NewSharedFactorReduction: %w", err)
	}
	if err := tensor.ValidateReplacement(parent, replacement); err != nil {
		return reductionCertificate{}, fmt.Errorf("validate replacement: %w", err)
	}
	witness, err := makeReplacementWitness(parent, replacement, "tensor.NewSharedFactorReduction")
	if err != nil {
		return reductionCertificate{}, err
	}
	registeredIndex, registered := preregisteredReductionIndex(outputHash, mode)
	if !registered {
		return reductionCertificate{}, fmt.Errorf("output %s mode %d has no preregistered reduction", outputHash, mode)
	}
	expected := expectedReductions[registeredIndex]
	if len(witness.InsertedTerms) != 1 || witness.InsertedTerms[0] != expected.Inserted {
		return reductionCertificate{}, fmt.Errorf("inserted terms are %v, want [%v]", witness.InsertedTerms, expected.Inserted)
	}
	resultScheme, err := tensor.ApplyReplacement(parent, replacement)
	if err != nil {
		return reductionCertificate{}, fmt.Errorf("apply replacement: %w", err)
	}
	order := makeOutputOrder(parent.TermCount(), replacement.RemovedSlots(), len(replacement.InsertedTerms()))
	if err := verifyOutputOrder(parent, resultScheme, replacement, order); err != nil {
		return reductionCertificate{}, fmt.Errorf("verify output order: %w", err)
	}
	result, _, err := checkedSchemeResult(resultScheme)
	if err != nil {
		return reductionCertificate{}, fmt.Errorf("validate result: %w", err)
	}
	if result.TermCount != expectedRootTerms {
		return reductionCertificate{}, fmt.Errorf("reduction result has %d terms, want %d", result.TermCount, expectedRootTerms)
	}
	if result.UnorderedCanonicalSHA256 != expectedC659UnorderedCanonicalSHA256 {
		return reductionCertificate{}, fmt.Errorf("reduction result hash is %s, want %s", result.UnorderedCanonicalSHA256, expectedC659UnorderedCanonicalSHA256)
	}
	return reductionCertificate{
		Classification: "exact defect-one reduction to an authenticated 47-term unordered presentation",
		Replacement:    witness,
		OutputOrder:    order,
		Result:         result,
	}, nil
}

func preregisteredReductionIndex(outputHash string, mode int) (int, bool) {
	for index, expected := range expectedReductions {
		if expected.OutputHash == outputHash && expected.SharedMode == mode {
			return index, true
		}
	}
	return 0, false
}

func checkedSchemeResult(scheme tensor.Scheme) (schemeResult, []byte, error) {
	checks, err := validateSchemeSeparately(scheme)
	if err != nil {
		return schemeResult{}, nil, err
	}
	hash, canonical, err := canonicalHash(scheme)
	if err != nil {
		return schemeResult{}, nil, err
	}
	words, err := schemeWords(scheme)
	if err != nil {
		return schemeResult{}, nil, err
	}
	return schemeResult{
		TermCount:                scheme.TermCount(),
		UnorderedCanonicalSHA256: hash,
		OrderedTerms:             words,
		Checks:                   checks,
	}, canonical, nil
}

func makeReplacementWitness(parent tensor.Scheme, replacement tensor.Replacement, constructor string) (replacementWitness, error) {
	removedSlots := replacement.RemovedSlots()
	removedTerms := make([]wordTriple, len(removedSlots))
	for index, slot := range removedSlots {
		triple, err := termWords(parent.Term(slot))
		if err != nil {
			return replacementWitness{}, fmt.Errorf("removed term %d: %w", slot, err)
		}
		removedTerms[index] = triple
	}
	inserted := replacement.InsertedTerms()
	insertedTerms := make([]wordTriple, len(inserted))
	for index, term := range inserted {
		triple, err := termWords(term)
		if err != nil {
			return replacementWitness{}, fmt.Errorf("inserted term %d: %w", index, err)
		}
		insertedTerms[index] = triple
	}
	return replacementWitness{
		Constructor:            constructor,
		RemovedSlots:           removedSlots,
		RemovedTerms:           removedTerms,
		InsertedTerms:          insertedTerms,
		ValidationAPI:          "tensor.ValidateReplacement",
		TensorIdentityVerified: true,
	}, nil
}

func makeOutputOrder(parentCount int, removed []int, insertedCount int) outputOrderWitness {
	removedSet := make(map[int]bool, len(removed))
	for _, slot := range removed {
		removedSet[slot] = true
	}
	survivors := make([]int, 0, parentCount-len(removed))
	for slot := range parentCount {
		if !removedSet[slot] {
			survivors = append(survivors, slot)
		}
	}
	survivorResults := make([]int, len(survivors))
	for index := range survivorResults {
		survivorResults[index] = index
	}
	insertions := make([]int, insertedCount)
	for index := range insertions {
		insertions[index] = len(survivors) + index
	}
	return outputOrderWitness{
		Rule:                 "increasing parent-slot survivors followed by insertion-list order",
		SurvivorParentSlots:  survivors,
		SurvivorResultSlots:  survivorResults,
		InsertionResultSlots: insertions,
	}
}

func verifyOutputOrder(parent, result tensor.Scheme, replacement tensor.Replacement, order outputOrderWitness) error {
	if len(order.SurvivorParentSlots) != len(order.SurvivorResultSlots) {
		return fmt.Errorf("survivor lineage lengths differ")
	}
	for index, parentSlot := range order.SurvivorParentSlots {
		resultSlot := order.SurvivorResultSlots[index]
		parentWords, err := termWords(parent.Term(parentSlot))
		if err != nil {
			return err
		}
		resultWords, err := termWords(result.Term(resultSlot))
		if err != nil {
			return err
		}
		if parentWords != resultWords {
			return fmt.Errorf("parent survivor %d differs from result slot %d", parentSlot, resultSlot)
		}
	}
	inserted := replacement.InsertedTerms()
	if len(inserted) != len(order.InsertionResultSlots) {
		return fmt.Errorf("insertion lineage lengths differ")
	}
	for index, term := range inserted {
		insertedWords, err := termWords(term)
		if err != nil {
			return err
		}
		resultWords, err := termWords(result.Term(order.InsertionResultSlots[index]))
		if err != nil {
			return err
		}
		if insertedWords != resultWords {
			return fmt.Errorf("insertion %d differs from result slot %d", index, order.InsertionResultSlots[index])
		}
	}
	return nil
}

func enforceExperimentCounts(attempts []attemptCertificate, records []flipRecord, uniqueOutputs []uniqueOutput, counts experimentCounts) error {
	checks := []struct {
		name string
		got  int
		want int
	}{
		{name: "attempts", got: len(attempts), want: expectedCandidateCount},
		{name: "accepted records", got: len(records), want: expectedAcceptedCount},
		{name: "rejections", got: counts.Rejected, want: expectedRejectedCount},
		{name: "unique outputs", got: len(uniqueOutputs), want: expectedUniqueOutputCount},
		{name: "maximal classes", got: counts.Classes, want: expectedMaximalClassCount},
		{name: "defect-zero classes", got: counts.DefectZero, want: expectedDefectZeroCount},
		{name: "defect-one classes", got: counts.DefectOne, want: expectedDefectOneCount},
		{name: "defect-at-least-two classes", got: counts.DefectAtLeastTwo, want: expectedDefectAtLeastTwoCount},
		{name: "reductions", got: counts.Reductions, want: expectedReductionCount},
	}
	for _, check := range checks {
		if check.got != check.want {
			return fmt.Errorf("%s count is %d, want %d", check.name, check.got, check.want)
		}
	}
	return nil
}

func intPointer(value int) *int {
	return &value
}

func stringPointer(value string) *string {
	return &value
}
