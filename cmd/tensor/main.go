package main

import (
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os"
	"strconv"

	"patel.codes/proofs/internal/ring"
	"patel.codes/proofs/internal/tensor"
)

const usage = `Usage:
  tensor validate DOMAIN
  tensor explain DOMAIN
  tensor analyze-shared DOMAIN
  tensor apply DOMAIN plus P Q
  tensor apply DOMAIN ordinary-flip MODE FIRST_SLOT SECOND_SLOT COEFFICIENT
  tensor apply DOMAIN inverse-plus VARIANT OUTPUT_SLOT_0 OUTPUT_SLOT_1 OUTPUT_SLOT_2
  tensor apply DOMAIN shared-factor MODE SLOT SLOT [SLOT...]
  tensor replay DOMAIN TRANSCRIPT_PATH

DOMAIN is z2 or z3. Native source is read from stdin.
MODE is first, second, or third.
VARIANT is second-third-first, third-first-second, or first-second-third.
`

type validationOutput struct {
	Domain     string           `json:"domain"`
	Dimensions [3]int           `json:"dimensions"`
	Terms      int              `json:"terms"`
	Checks     validationChecks `json:"checks"`
}

type validationChecks struct {
	Brent                  bool `json:"brent"`
	NonzeroTerms           bool `json:"nonzero_terms"`
	DistinctRankOneTensors bool `json:"distinct_rank_one_tensors"`
}

type explanationOutput struct {
	Domain     string              `json:"domain"`
	Dimensions [3]int              `json:"dimensions"`
	Terms      int                 `json:"terms"`
	Factors    [3]factorDiagnostic `json:"factors"`
}

type factorDiagnostic struct {
	Mode           int `json:"mode"`
	Rows           int `json:"rows"`
	Columns        int `json:"columns"`
	Entries        int `json:"entries"`
	NonzeroEntries int `json:"nonzero_entries"`
	ZeroFactors    int `json:"zero_factors"`
}

type sharedAnalysisOutput struct {
	Domain     string                `json:"domain"`
	Dimensions [3]int                `json:"dimensions"`
	Terms      int                   `json:"terms"`
	Classes    []sharedClassOutput   `json:"classes"`
	Summary    sharedAnalysisSummary `json:"summary"`
}

type sharedClassOutput struct {
	Mode              tensor.SharedMode `json:"mode"`
	Slots             []int             `json:"slots"`
	Size              int               `json:"size"`
	ComplementaryRank int               `json:"complementary_rank"`
	Defect            int               `json:"defect"`
}

type sharedAnalysisSummary struct {
	ClassCount              int `json:"class_count"`
	PositiveDefectClasses   int `json:"positive_defect_classes"`
	MaximumIndividualDefect int `json:"maximum_individual_defect"`
}

func main() {
	if err := run(os.Args[1:], os.Stdin, os.Stdout, os.Stderr); err != nil {
		if _, writeErr := fmt.Fprintf(os.Stderr, "tensor: %v\n", err); writeErr != nil {
			os.Exit(2)
		}
		os.Exit(1)
	}
}

func run(args []string, stdin io.Reader, stdout, stderr io.Writer) error {
	if len(args) == 1 && (args[0] == "-h" || args[0] == "--help") {
		return writeString(stdout, usage, "help")
	}
	if len(args) < 2 {
		if err := writeString(stderr, usage, "usage"); err != nil {
			return err
		}
		return fmt.Errorf("require a command and explicit domain")
	}
	domain, err := parseDomain(args[1])
	if err != nil {
		return err
	}
	switch args[0] {
	case "validate":
		if len(args) != 2 {
			return usageError(stderr, "validate requires exactly DOMAIN")
		}
		return runValidate(domain, args[1], stdin, stdout)
	case "explain":
		if len(args) != 2 {
			return usageError(stderr, "explain requires exactly DOMAIN")
		}
		return runExplain(domain, args[1], stdin, stdout)
	case "analyze-shared":
		if len(args) != 2 {
			return usageError(stderr, "analyze-shared requires exactly DOMAIN")
		}
		if domain != ring.Z2 {
			return usageError(stderr, "analyze-shared requires domain z2")
		}
		return runAnalyzeShared(domain, args[1], stdin, stdout)
	case "apply":
		if len(args) < 3 {
			return usageError(stderr, "apply requires a named constructor")
		}
		step, err := parseApplyStep(domain, args[2:])
		if err != nil {
			return usageError(stderr, "apply: %v", err)
		}
		return runApply(domain, stdin, stdout, step)
	case "replay":
		if len(args) != 3 {
			return usageError(stderr, "replay requires exactly DOMAIN and TRANSCRIPT_PATH")
		}
		return runReplay(domain, args[2], stdin, stdout)
	default:
		return usageError(stderr, "unknown command %q", args[0])
	}
}

func runValidate(domain ring.Ring, domainName string, stdin io.Reader, stdout io.Writer) error {
	scheme, err := tensor.ParseNative(domain, stdin)
	if err != nil {
		return fmt.Errorf("validate: parse %s native source: %w", domainName, err)
	}
	if err := tensor.ValidateBrent(scheme); err != nil {
		return fmt.Errorf("validate: Brent check: %w", err)
	}
	if err := tensor.ValidateNonzeroTerms(scheme); err != nil {
		return fmt.Errorf("validate: nonzero-term check: %w", err)
	}
	if err := tensor.ValidateDistinctTensors(scheme); err != nil {
		return fmt.Errorf("validate: distinct-rank-one-tensor check: %w", err)
	}
	return writeJSON(stdout, validationOutput{
		Domain: domainName, Dimensions: scheme.Dimensions(), Terms: scheme.TermCount(),
		Checks: validationChecks{Brent: true, NonzeroTerms: true, DistinctRankOneTensors: true},
	}, "validation")
}

func runExplain(domain ring.Ring, domainName string, stdin io.Reader, stdout io.Writer) error {
	scheme, err := tensor.ParseNative(domain, stdin)
	if err != nil {
		return fmt.Errorf("explain: parse %s native source: %w", domainName, err)
	}
	dimensions := scheme.Dimensions()
	output := explanationOutput{Domain: domainName, Dimensions: dimensions, Terms: scheme.TermCount()}
	for mode := range 3 {
		diagnostic := factorDiagnostic{
			Mode: mode, Rows: dimensions[mode], Columns: dimensions[(mode+1)%3],
		}
		for termIndex := range scheme.TermCount() {
			entries := scheme.Term(termIndex).Factor(mode).Entries()
			diagnostic.Entries += len(entries)
			factorNonzero := false
			for _, entry := range entries {
				if entry != 0 {
					diagnostic.NonzeroEntries++
					factorNonzero = true
				}
			}
			if !factorNonzero {
				diagnostic.ZeroFactors++
			}
		}
		output.Factors[mode] = diagnostic
	}
	return writeJSON(stdout, output, "explanation")
}

func runAnalyzeShared(domain ring.Ring, domainName string, stdin io.Reader, stdout io.Writer) error {
	scheme, err := tensor.ParseNative(domain, stdin)
	if err != nil {
		return fmt.Errorf("analyze-shared: parse %s native source: %w", domainName, err)
	}
	analysis, err := tensor.AnalyzeSharedFactors(scheme)
	if err != nil {
		return fmt.Errorf("analyze-shared: %w", err)
	}
	classes := analysis.Classes()
	output := sharedAnalysisOutput{
		Domain: domainName, Dimensions: scheme.Dimensions(), Terms: scheme.TermCount(),
		Classes: make([]sharedClassOutput, len(classes)),
	}
	output.Summary.ClassCount = len(classes)
	for i, class := range classes {
		slots := class.Slots()
		output.Classes[i] = sharedClassOutput{
			Mode: class.Mode(), Slots: slots, Size: len(slots),
			ComplementaryRank: class.ComplementaryRank(), Defect: class.Defect(),
		}
		if class.Defect() > 0 {
			output.Summary.PositiveDefectClasses++
		}
		if class.Defect() > output.Summary.MaximumIndividualDefect {
			output.Summary.MaximumIndividualDefect = class.Defect()
		}
	}
	return writeJSON(stdout, output, "shared-factor analysis")
}

func runApply(domain ring.Ring, stdin io.Reader, stdout io.Writer, step tensor.TranscriptStep) error {
	scheme, err := tensor.ParseNative(domain, stdin)
	if err != nil {
		return fmt.Errorf("apply: parse native source: %w", err)
	}
	result, err := tensor.ApplyTranscriptStep(scheme, step)
	if err != nil {
		return fmt.Errorf("apply: %w", err)
	}
	if err := tensor.WriteNative(stdout, result); err != nil {
		return fmt.Errorf("apply: write native result: %w", err)
	}
	return nil
}

func runReplay(domain ring.Ring, transcriptPath string, stdin io.Reader, stdout io.Writer) error {
	transcript, err := readTranscript(transcriptPath)
	if err != nil {
		return fmt.Errorf("replay: %w", err)
	}
	if transcript.Ring != domain {
		return fmt.Errorf("replay: explicit domain %d differs from transcript ring %d", domain, transcript.Ring)
	}
	source, err := tensor.ParseNative(domain, stdin)
	if err != nil {
		return fmt.Errorf("replay: parse native source: %w", err)
	}
	result, err := tensor.ReplayTranscript(source, transcript)
	if err != nil {
		return fmt.Errorf("replay: %w", err)
	}
	if err := tensor.WriteNative(stdout, result); err != nil {
		return fmt.Errorf("replay: write native result: %w", err)
	}
	return nil
}

func parseApplyStep(domain ring.Ring, args []string) (tensor.TranscriptStep, error) {
	if len(args) == 0 {
		return tensor.TranscriptStep{}, fmt.Errorf("named constructor is required")
	}
	switch args[0] {
	case "plus":
		if domain != ring.Z2 {
			return tensor.TranscriptStep{}, fmt.Errorf("plus requires domain z2")
		}
		if len(args) != 3 {
			return tensor.TranscriptStep{}, fmt.Errorf("plus requires P and Q")
		}
		p, err := parseSlot(args[1], "P")
		if err != nil {
			return tensor.TranscriptStep{}, err
		}
		q, err := parseSlot(args[2], "Q")
		if err != nil {
			return tensor.TranscriptStep{}, err
		}
		if p == q {
			return tensor.TranscriptStep{}, fmt.Errorf("P and Q must be distinct")
		}
		return tensor.TranscriptStep{Plus: &tensor.PlusStep{P: p, Q: q}}, nil
	case "ordinary-flip":
		if len(args) != 5 {
			return tensor.TranscriptStep{}, fmt.Errorf("ordinary-flip requires MODE, FIRST_SLOT, SECOND_SLOT, and COEFFICIENT")
		}
		mode, err := parseMode(args[1])
		if err != nil {
			return tensor.TranscriptStep{}, err
		}
		first, err := parseSlot(args[2], "FIRST_SLOT")
		if err != nil {
			return tensor.TranscriptStep{}, err
		}
		second, err := parseSlot(args[3], "SECOND_SLOT")
		if err != nil {
			return tensor.TranscriptStep{}, err
		}
		if first == second {
			return tensor.TranscriptStep{}, fmt.Errorf("FIRST_SLOT and SECOND_SLOT must be distinct")
		}
		coefficient, err := parseInteger(args[4], "COEFFICIENT")
		if err != nil {
			return tensor.TranscriptStep{}, err
		}
		if domain.Normalize(coefficient) == 0 {
			return tensor.TranscriptStep{}, fmt.Errorf("COEFFICIENT is zero in domain z%d", domain)
		}
		return tensor.TranscriptStep{OrdinaryFlip: &tensor.OrdinaryFlipStep{
			Mode: mode, FirstSlot: first, SecondSlot: second, Coefficient: coefficient,
		}}, nil
	case "inverse-plus":
		if domain != ring.Z2 {
			return tensor.TranscriptStep{}, fmt.Errorf("inverse-plus requires domain z2")
		}
		if len(args) != 5 {
			return tensor.TranscriptStep{}, fmt.Errorf("inverse-plus requires VARIANT and three output slots")
		}
		variant, err := parseVariant(args[1])
		if err != nil {
			return tensor.TranscriptStep{}, err
		}
		var slots [3]int
		for index := range slots {
			slots[index], err = parseSlot(args[index+2], fmt.Sprintf("OUTPUT_SLOT_%d", index))
			if err != nil {
				return tensor.TranscriptStep{}, err
			}
			for earlier := range index {
				if slots[index] == slots[earlier] {
					return tensor.TranscriptStep{}, fmt.Errorf("output slots must be distinct")
				}
			}
		}
		return tensor.TranscriptStep{InversePlus: &tensor.InversePlusStep{OutputSlots: slots, Variant: variant}}, nil
	case "shared-factor":
		if domain != ring.Z2 {
			return tensor.TranscriptStep{}, fmt.Errorf("shared-factor requires domain z2")
		}
		if len(args) < 4 {
			return tensor.TranscriptStep{}, fmt.Errorf("shared-factor requires MODE and at least two slots")
		}
		mode, err := parseMode(args[1])
		if err != nil {
			return tensor.TranscriptStep{}, err
		}
		slots := make([]int, len(args)-2)
		seen := make(map[int]struct{}, len(slots))
		for index, value := range args[2:] {
			slots[index], err = parseSlot(value, fmt.Sprintf("SLOT_%d", index))
			if err != nil {
				return tensor.TranscriptStep{}, err
			}
			if _, ok := seen[slots[index]]; ok {
				return tensor.TranscriptStep{}, fmt.Errorf("slots must be distinct")
			}
			seen[slots[index]] = struct{}{}
		}
		return tensor.TranscriptStep{SharedFactorReduction: &tensor.SharedFactorReductionStep{Mode: mode, Slots: slots}}, nil
	default:
		return tensor.TranscriptStep{}, fmt.Errorf("unknown constructor %q", args[0])
	}
}

func parseDomain(value string) (ring.Ring, error) {
	switch value {
	case "z2":
		return ring.Z2, nil
	case "z3":
		return ring.Z3, nil
	default:
		return 0, fmt.Errorf("unsupported domain %q, want z2 or z3", value)
	}
}

func parseMode(value string) (tensor.SharedMode, error) {
	switch value {
	case "first":
		return tensor.SharedFirst, nil
	case "second":
		return tensor.SharedSecond, nil
	case "third":
		return tensor.SharedThird, nil
	default:
		return 0, fmt.Errorf("unsupported mode %q", value)
	}
}

func parseVariant(value string) (tensor.PlusVariant, error) {
	switch value {
	case "second-third-first":
		return tensor.PlusVariantSecondThirdFirst, nil
	case "third-first-second":
		return tensor.PlusVariantThirdFirstSecond, nil
	case "first-second-third":
		return tensor.PlusVariantFirstSecondThird, nil
	default:
		return 0, fmt.Errorf("unsupported inverse Plus variant %q", value)
	}
}

func parseSlot(value, role string) (int, error) {
	parsed, err := parseInteger(value, role)
	if err != nil {
		return 0, err
	}
	if parsed < 0 {
		return 0, fmt.Errorf("%s must be nonnegative, got %d", role, parsed)
	}
	return parsed, nil
}

func parseInteger(value, role string) (int, error) {
	parsed, err := strconv.Atoi(value)
	if err != nil {
		return 0, fmt.Errorf("%s is not an integer: %q", role, value)
	}
	return parsed, nil
}

func readTranscript(path string) (tensor.Transcript, error) {
	file, err := os.Open(path)
	if err != nil {
		return tensor.Transcript{}, fmt.Errorf("open transcript %q: %w", path, err)
	}
	value, parseErr := tensor.ParseTranscript(file)
	closeErr := file.Close()
	if parseErr != nil {
		return tensor.Transcript{}, fmt.Errorf("parse transcript %q: %w", path, errors.Join(parseErr, closeErr))
	}
	if closeErr != nil {
		return tensor.Transcript{}, fmt.Errorf("close transcript %q: %w", path, closeErr)
	}
	return value, nil
}

func writeJSON(writer io.Writer, value any, role string) error {
	encoded, err := json.MarshalIndent(value, "", "  ")
	if err != nil {
		return fmt.Errorf("encode %s: %w", role, err)
	}
	encoded = append(encoded, '\n')
	written, err := writer.Write(encoded)
	if err != nil {
		return fmt.Errorf("write %s: %w", role, err)
	}
	if written != len(encoded) {
		return fmt.Errorf("write %s: %w", role, io.ErrShortWrite)
	}
	return nil
}

func usageError(stderr io.Writer, format string, arguments ...any) error {
	if err := writeString(stderr, usage, "usage"); err != nil {
		return err
	}
	return fmt.Errorf(format, arguments...)
}

func writeString(writer io.Writer, value, role string) error {
	written, err := io.WriteString(writer, value)
	if err != nil {
		return fmt.Errorf("write %s: %w", role, err)
	}
	if written != len(value) {
		return fmt.Errorf("write %s: %w", role, io.ErrShortWrite)
	}
	return nil
}
