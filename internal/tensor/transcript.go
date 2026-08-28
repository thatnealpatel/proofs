package tensor

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"sort"

	"patel.codes/proofs/internal/ring"
)

const TranscriptVersion = 1
const MaxTranscriptBytes = 16 << 20

type Transcript struct {
	Version    int              `json:"version"`
	Ring       ring.Ring        `json:"ring"`
	Dimensions [3]int           `json:"dimensions"`
	Steps      []TranscriptStep `json:"steps"`
}

type TranscriptStep struct {
	Plus                  *PlusStep                  `json:"plus,omitempty"`
	OrdinaryFlip          *OrdinaryFlipStep          `json:"ordinary_flip,omitempty"`
	InversePlus           *InversePlusStep           `json:"inverse_plus,omitempty"`
	SharedFactorReduction *SharedFactorReductionStep `json:"shared_factor_reduction,omitempty"`
}

type PlusStep struct {
	P int `json:"p"`
	Q int `json:"q"`
}

type OrdinaryFlipStep struct {
	Mode        SharedMode `json:"mode"`
	FirstSlot   int        `json:"first_slot"`
	SecondSlot  int        `json:"second_slot"`
	Coefficient int        `json:"coefficient"`
}

type InversePlusStep struct {
	OutputSlots [3]int      `json:"output_slots"`
	Variant     PlusVariant `json:"variant"`
}

type SharedFactorReductionStep struct {
	Mode  SharedMode `json:"mode"`
	Slots []int      `json:"slots"`
}

func NewTranscript(source Scheme, steps []TranscriptStep) (Transcript, error) {
	if err := source.validateStructure(); err != nil {
		return Transcript{}, fmt.Errorf("transcript source: %w", err)
	}
	transcript := Transcript{
		Version:    TranscriptVersion,
		Ring:       source.ring,
		Dimensions: source.dimensions,
		Steps:      cloneTranscriptSteps(steps),
	}
	if _, err := ReplayTranscript(source, transcript); err != nil {
		return Transcript{}, err
	}
	return transcript, nil
}

func ValidateTranscript(transcript Transcript) error {
	if transcript.Version != TranscriptVersion {
		return fmt.Errorf("unsupported transcript version %d, want %d", transcript.Version, TranscriptVersion)
	}
	if !transcript.Ring.Valid() {
		return fmt.Errorf("unsupported transcript ring %d", transcript.Ring)
	}
	for mode := range 3 {
		if _, err := matrixSize(transcript.Dimensions[mode], transcript.Dimensions[(mode+1)%3]); err != nil {
			return fmt.Errorf("transcript dimensions at mode %d: %w", mode, err)
		}
	}
	if transcript.Steps == nil {
		return fmt.Errorf("transcript steps must be an array")
	}
	for index, step := range transcript.Steps {
		if err := validateTranscriptStep(step, transcript.Ring); err != nil {
			return fmt.Errorf("transcript step %d: %w", index, err)
		}
	}
	return nil
}

func ApplyTranscriptStep(source Scheme, step TranscriptStep) (Scheme, error) {
	if err := source.validateStructure(); err != nil {
		return Scheme{}, fmt.Errorf("constructor source: %w", err)
	}
	if err := validateTranscriptStep(step, source.ring); err != nil {
		return Scheme{}, err
	}
	name := transcriptStepName(step)
	var replacement Replacement
	var err error
	switch {
	case step.Plus != nil:
		replacement, err = NewPlusReplacement(source, step.Plus.P, step.Plus.Q)
	case step.OrdinaryFlip != nil:
		operation := step.OrdinaryFlip
		replacement, err = NewOrdinaryFlipReplacement(source, operation.Mode, operation.FirstSlot, operation.SecondSlot, operation.Coefficient)
	case step.InversePlus != nil:
		operation := step.InversePlus
		replacement, err = NewInversePlusReplacement(source, operation.OutputSlots, operation.Variant)
	case step.SharedFactorReduction != nil:
		operation := step.SharedFactorReduction
		replacement, err = NewSharedFactorReduction(source, operation.Mode, operation.Slots)
	}
	if err != nil {
		return Scheme{}, fmt.Errorf("construct %s replacement: %w", name, err)
	}
	result, err := ApplyReplacement(source, replacement)
	if err != nil {
		return Scheme{}, fmt.Errorf("apply %s replacement: %w", name, err)
	}
	return result, nil
}

func ReplayTranscript(source Scheme, transcript Transcript) (Scheme, error) {
	if err := ValidateTranscript(transcript); err != nil {
		return Scheme{}, err
	}
	if err := source.validateStructure(); err != nil {
		return Scheme{}, fmt.Errorf("replay source: %w", err)
	}
	if source.ring != transcript.Ring {
		return Scheme{}, fmt.Errorf("replay source ring is %d, transcript ring is %d", source.ring, transcript.Ring)
	}
	if source.dimensions != transcript.Dimensions {
		return Scheme{}, fmt.Errorf("replay source dimensions are %v, transcript dimensions are %v", source.dimensions, transcript.Dimensions)
	}
	current := source
	for index, step := range transcript.Steps {
		result, err := ApplyTranscriptStep(current, step)
		if err != nil {
			return Scheme{}, fmt.Errorf("transcript step %d (%s): %w", index, transcriptStepName(step), err)
		}
		current = result
	}
	return current, nil
}

func ParseTranscript(reader io.Reader) (Transcript, error) {
	data, err := io.ReadAll(io.LimitReader(reader, MaxTranscriptBytes+1))
	if err != nil {
		return Transcript{}, fmt.Errorf("read transcript: %w", err)
	}
	if len(data) > MaxTranscriptBytes {
		return Transcript{}, fmt.Errorf("transcript exceeds %d-byte limit", MaxTranscriptBytes)
	}
	if err := rejectDuplicateJSONKeys(data); err != nil {
		return Transcript{}, fmt.Errorf("parse transcript JSON: %w", err)
	}
	var document transcriptDocument
	if err := decodeStrictJSONObject(data, &document, "version", "ring", "dimensions", "steps"); err != nil {
		return Transcript{}, fmt.Errorf("parse transcript JSON: %w", err)
	}
	transcript, err := document.transcript()
	if err != nil {
		return Transcript{}, err
	}
	if err := ValidateTranscript(transcript); err != nil {
		return Transcript{}, err
	}
	return transcript, nil
}

func WriteTranscript(writer io.Writer, transcript Transcript) error {
	if err := ValidateTranscript(transcript); err != nil {
		return err
	}
	encoded, err := json.MarshalIndent(transcript, "", "  ")
	if err != nil {
		return fmt.Errorf("encode transcript: %w", err)
	}
	encoded = append(encoded, '\n')
	written, err := writer.Write(encoded)
	if err != nil {
		return fmt.Errorf("write transcript: %w", err)
	}
	if written != len(encoded) {
		return fmt.Errorf("write transcript: %w", io.ErrShortWrite)
	}
	return nil
}

func validateTranscriptStep(step TranscriptStep, r ring.Ring) error {
	count := 0
	if step.Plus != nil {
		count++
	}
	if step.OrdinaryFlip != nil {
		count++
	}
	if step.InversePlus != nil {
		count++
	}
	if step.SharedFactorReduction != nil {
		count++
	}
	if count != 1 {
		return fmt.Errorf("must contain exactly one constructor, got %d", count)
	}
	switch {
	case step.Plus != nil:
		if r != ring.Z2 {
			return fmt.Errorf("Plus requires ring Z2, got %d", r)
		}
		if step.Plus.P < 0 || step.Plus.Q < 0 {
			return fmt.Errorf("Plus slots must be nonnegative, got %d and %d", step.Plus.P, step.Plus.Q)
		}
		if step.Plus.P == step.Plus.Q {
			return fmt.Errorf("Plus slots must be distinct, got %d twice", step.Plus.P)
		}
	case step.OrdinaryFlip != nil:
		operation := step.OrdinaryFlip
		if operation.Mode < SharedFirst || operation.Mode > SharedThird {
			return fmt.Errorf("ordinary flip mode is unsupported: %d", operation.Mode)
		}
		if operation.FirstSlot < 0 || operation.SecondSlot < 0 {
			return fmt.Errorf("ordinary flip slots must be nonnegative, got %d and %d", operation.FirstSlot, operation.SecondSlot)
		}
		if operation.FirstSlot == operation.SecondSlot {
			return fmt.Errorf("ordinary flip slots must be distinct, got %d twice", operation.FirstSlot)
		}
		if r.Valid() && r.Normalize(operation.Coefficient) == 0 {
			return fmt.Errorf("ordinary flip coefficient is zero in ring %d", r)
		}
	case step.InversePlus != nil:
		if r != ring.Z2 {
			return fmt.Errorf("inverse Plus requires ring Z2, got %d", r)
		}
		operation := step.InversePlus
		if operation.Variant < PlusVariantSecondThirdFirst || operation.Variant > PlusVariantFirstSecondThird {
			return fmt.Errorf("inverse Plus variant is unsupported: %d", operation.Variant)
		}
		for output, slot := range operation.OutputSlots {
			if slot < 0 {
				return fmt.Errorf("inverse Plus output slot %d is negative: %d", output, slot)
			}
			for earlier := range output {
				if slot == operation.OutputSlots[earlier] {
					return fmt.Errorf("inverse Plus output slots must be distinct, got %d at positions %d and %d", slot, earlier, output)
				}
			}
		}
	case step.SharedFactorReduction != nil:
		if r != ring.Z2 {
			return fmt.Errorf("shared-factor reduction requires ring Z2, got %d", r)
		}
		operation := step.SharedFactorReduction
		if operation.Mode < SharedFirst || operation.Mode > SharedThird {
			return fmt.Errorf("shared-factor mode is unsupported: %d", operation.Mode)
		}
		if len(operation.Slots) < 2 {
			return fmt.Errorf("shared-factor reduction requires at least two slots, got %d", len(operation.Slots))
		}
		seen := make(map[int]int, len(operation.Slots))
		for index, slot := range operation.Slots {
			if slot < 0 {
				return fmt.Errorf("shared-factor slot %d is negative: %d", index, slot)
			}
			if earlier, ok := seen[slot]; ok {
				return fmt.Errorf("shared-factor slots contain duplicate %d at positions %d and %d", slot, earlier, index)
			}
			seen[slot] = index
		}
	}
	return nil
}

func transcriptStepName(step TranscriptStep) string {
	switch {
	case step.Plus != nil:
		return "plus"
	case step.OrdinaryFlip != nil:
		return "ordinary_flip"
	case step.InversePlus != nil:
		return "inverse_plus"
	case step.SharedFactorReduction != nil:
		return "shared_factor_reduction"
	default:
		return "invalid"
	}
}

func cloneTranscriptSteps(steps []TranscriptStep) []TranscriptStep {
	cloned := make([]TranscriptStep, len(steps))
	for index, step := range steps {
		if step.Plus != nil {
			value := *step.Plus
			cloned[index].Plus = &value
		}
		if step.OrdinaryFlip != nil {
			value := *step.OrdinaryFlip
			cloned[index].OrdinaryFlip = &value
		}
		if step.InversePlus != nil {
			value := *step.InversePlus
			cloned[index].InversePlus = &value
		}
		if step.SharedFactorReduction != nil {
			value := *step.SharedFactorReduction
			value.Slots = append([]int(nil), value.Slots...)
			cloned[index].SharedFactorReduction = &value
		}
	}
	return cloned
}

type transcriptDocument struct {
	Version    *int               `json:"version"`
	Ring       *ring.Ring         `json:"ring"`
	Dimensions *[]int             `json:"dimensions"`
	Steps      *[]json.RawMessage `json:"steps"`
}

func (document transcriptDocument) transcript() (Transcript, error) {
	if document.Version == nil {
		return Transcript{}, fmt.Errorf("transcript version is required")
	}
	if document.Ring == nil {
		return Transcript{}, fmt.Errorf("transcript ring is required")
	}
	if document.Dimensions == nil {
		return Transcript{}, fmt.Errorf("transcript dimensions are required")
	}
	if len(*document.Dimensions) != 3 {
		return Transcript{}, fmt.Errorf("transcript dimensions have length %d, want 3", len(*document.Dimensions))
	}
	if document.Steps == nil {
		return Transcript{}, fmt.Errorf("transcript steps must be an array")
	}
	transcript := Transcript{
		Version: *document.Version,
		Ring:    *document.Ring,
		Dimensions: [3]int{
			(*document.Dimensions)[0],
			(*document.Dimensions)[1],
			(*document.Dimensions)[2],
		},
		Steps: make([]TranscriptStep, len(*document.Steps)),
	}
	for index, raw := range *document.Steps {
		step, err := parseTranscriptStep(raw)
		if err != nil {
			return Transcript{}, fmt.Errorf("transcript step %d: %w", index, err)
		}
		transcript.Steps[index] = step
	}
	return transcript, nil
}

type transcriptStepDocument struct {
	Plus                  json.RawMessage `json:"plus"`
	OrdinaryFlip          json.RawMessage `json:"ordinary_flip"`
	InversePlus           json.RawMessage `json:"inverse_plus"`
	SharedFactorReduction json.RawMessage `json:"shared_factor_reduction"`
}

func parseTranscriptStep(data []byte) (TranscriptStep, error) {
	var document transcriptStepDocument
	if err := decodeStrictJSONObject(data, &document, "plus", "ordinary_flip", "inverse_plus", "shared_factor_reduction"); err != nil {
		return TranscriptStep{}, err
	}
	count := 0
	for _, raw := range []json.RawMessage{document.Plus, document.OrdinaryFlip, document.InversePlus, document.SharedFactorReduction} {
		if len(raw) != 0 {
			count++
		}
	}
	if count != 1 {
		return TranscriptStep{}, fmt.Errorf("must contain exactly one constructor, got %d", count)
	}
	var step TranscriptStep
	var err error
	switch {
	case len(document.Plus) != 0:
		step.Plus, err = parsePlusStep(document.Plus)
	case len(document.OrdinaryFlip) != 0:
		step.OrdinaryFlip, err = parseOrdinaryFlipStep(document.OrdinaryFlip)
	case len(document.InversePlus) != 0:
		step.InversePlus, err = parseInversePlusStep(document.InversePlus)
	case len(document.SharedFactorReduction) != 0:
		step.SharedFactorReduction, err = parseSharedFactorReductionStep(document.SharedFactorReduction)
	}
	return step, err
}

func parsePlusStep(data []byte) (*PlusStep, error) {
	var value struct {
		P *int `json:"p"`
		Q *int `json:"q"`
	}
	if err := decodeStrictJSONObject(data, &value, "p", "q"); err != nil {
		return nil, err
	}
	if value.P == nil || value.Q == nil {
		return nil, fmt.Errorf("Plus requires p and q")
	}
	return &PlusStep{P: *value.P, Q: *value.Q}, nil
}

func parseOrdinaryFlipStep(data []byte) (*OrdinaryFlipStep, error) {
	var value struct {
		Mode        *SharedMode `json:"mode"`
		FirstSlot   *int        `json:"first_slot"`
		SecondSlot  *int        `json:"second_slot"`
		Coefficient *int        `json:"coefficient"`
	}
	if err := decodeStrictJSONObject(data, &value, "mode", "first_slot", "second_slot", "coefficient"); err != nil {
		return nil, err
	}
	if value.Mode == nil || value.FirstSlot == nil || value.SecondSlot == nil || value.Coefficient == nil {
		return nil, fmt.Errorf("ordinary flip requires mode, first_slot, second_slot, and coefficient")
	}
	return &OrdinaryFlipStep{Mode: *value.Mode, FirstSlot: *value.FirstSlot, SecondSlot: *value.SecondSlot, Coefficient: *value.Coefficient}, nil
}

func parseInversePlusStep(data []byte) (*InversePlusStep, error) {
	var value struct {
		OutputSlots *[]int       `json:"output_slots"`
		Variant     *PlusVariant `json:"variant"`
	}
	if err := decodeStrictJSONObject(data, &value, "output_slots", "variant"); err != nil {
		return nil, err
	}
	if value.OutputSlots == nil || value.Variant == nil {
		return nil, fmt.Errorf("inverse Plus requires output_slots and variant")
	}
	if len(*value.OutputSlots) != 3 {
		return nil, fmt.Errorf("inverse Plus output_slots has length %d, want 3", len(*value.OutputSlots))
	}
	return &InversePlusStep{OutputSlots: [3]int{(*value.OutputSlots)[0], (*value.OutputSlots)[1], (*value.OutputSlots)[2]}, Variant: *value.Variant}, nil
}

func parseSharedFactorReductionStep(data []byte) (*SharedFactorReductionStep, error) {
	var value struct {
		Mode  *SharedMode `json:"mode"`
		Slots *[]int      `json:"slots"`
	}
	if err := decodeStrictJSONObject(data, &value, "mode", "slots"); err != nil {
		return nil, err
	}
	if value.Mode == nil || value.Slots == nil {
		return nil, fmt.Errorf("shared-factor reduction requires mode and slots")
	}
	return &SharedFactorReductionStep{Mode: *value.Mode, Slots: append([]int(nil), (*value.Slots)...)}, nil
}

func decodeStrictJSONObject(data []byte, target any, allowed ...string) error {
	var fields map[string]json.RawMessage
	if err := json.Unmarshal(data, &fields); err != nil {
		return err
	}
	allowedSet := make(map[string]struct{}, len(allowed))
	for _, field := range allowed {
		allowedSet[field] = struct{}{}
	}
	unknown := make([]string, 0)
	for field := range fields {
		if _, ok := allowedSet[field]; !ok {
			unknown = append(unknown, field)
		}
	}
	if len(unknown) != 0 {
		sort.Strings(unknown)
		return fmt.Errorf("unknown field %q", unknown[0])
	}
	return decodeStrictJSON(data, target)
}

func decodeStrictJSON(data []byte, target any) error {
	decoder := json.NewDecoder(bytes.NewReader(data))
	decoder.DisallowUnknownFields()
	if err := decoder.Decode(target); err != nil {
		return err
	}
	var trailing any
	if err := decoder.Decode(&trailing); err != io.EOF {
		if err == nil {
			return fmt.Errorf("trailing JSON value")
		}
		return fmt.Errorf("trailing data: %w", err)
	}
	return nil
}

func rejectDuplicateJSONKeys(data []byte) error {
	decoder := json.NewDecoder(bytes.NewReader(data))
	var walk func() error
	walk = func() error {
		token, err := decoder.Token()
		if err != nil {
			return err
		}
		delimiter, ok := token.(json.Delim)
		if !ok {
			return nil
		}
		switch delimiter {
		case '{':
			seen := make(map[string]struct{})
			for decoder.More() {
				keyToken, err := decoder.Token()
				if err != nil {
					return err
				}
				key, ok := keyToken.(string)
				if !ok {
					return fmt.Errorf("object key is not a string")
				}
				if _, duplicate := seen[key]; duplicate {
					return fmt.Errorf("duplicate object key %q", key)
				}
				seen[key] = struct{}{}
				if err := walk(); err != nil {
					return err
				}
			}
			closing, err := decoder.Token()
			if err != nil {
				return err
			}
			if closing != json.Delim('}') {
				return fmt.Errorf("object has invalid closing delimiter")
			}
		case '[':
			for decoder.More() {
				if err := walk(); err != nil {
					return err
				}
			}
			closing, err := decoder.Token()
			if err != nil {
				return err
			}
			if closing != json.Delim(']') {
				return fmt.Errorf("array has invalid closing delimiter")
			}
		default:
			return fmt.Errorf("unexpected delimiter %q", delimiter)
		}
		return nil
	}
	if err := walk(); err != nil {
		return err
	}
	if _, err := decoder.Token(); err != io.EOF {
		if err == nil {
			return fmt.Errorf("trailing JSON value")
		}
		return fmt.Errorf("trailing data: %w", err)
	}
	return nil
}
