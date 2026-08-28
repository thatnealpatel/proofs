package main

import (
	"bytes"
	"fmt"
	"slices"
	"sync"

	"patel.codes/proofs/internal/ring"
	"patel.codes/proofs/internal/tensor"
)

func parseRoot(raw []byte, spec rootSpec) ([]triple, error) {
	scheme, err := tensor.ParseNative(ring.Z2, bytes.NewReader(raw))
	if err != nil {
		return nil, fmt.Errorf("%s parse: %w", spec.Input.Role, err)
	}
	if scheme.Ring() != ring.Z2 || scheme.Dimensions() != [3]int{4, 4, 4} || scheme.TermCount() != rootTerms {
		return nil, fmt.Errorf("%s ring, dimensions, or term count mismatch", spec.Input.Role)
	}
	if err := tensor.ValidateNonzeroTerms(scheme); err != nil {
		return nil, fmt.Errorf("%s nonzero validation: %w", spec.Input.Role, err)
	}
	if err := tensor.ValidateDistinctTensors(scheme); err != nil {
		return nil, fmt.Errorf("%s distinct validation: %w", spec.Input.Role, err)
	}
	if err := tensor.ValidateBrent(scheme); err != nil {
		return nil, fmt.Errorf("%s Brent validation: %w", spec.Input.Role, err)
	}
	words, err := schemeWords(scheme)
	if err != nil {
		return nil, fmt.Errorf("%s words: %w", spec.Input.Role, err)
	}
	if got := digest(orderedPayload(words)); got != spec.OrderedSHA256 {
		return nil, fmt.Errorf("%s ordered payload SHA-256 is %s, want %s", spec.Input.Role, got, spec.OrderedSHA256)
	}
	if got := digest(canonicalPayload(words)); got != spec.CanonicalSHA256 {
		return nil, fmt.Errorf("%s canonical payload SHA-256 is %s, want %s", spec.Input.Role, got, spec.CanonicalSHA256)
	}
	if tensorSum(words) != targetTensor() {
		return nil, fmt.Errorf("%s exact root tensor encoding mismatch", spec.Input.Role)
	}
	return words, nil
}

func formulaPlus(first, second triple, positions [3]int) [3]triple {
	a1, b1, c1 := first[positions[0]], first[positions[1]], first[positions[2]]
	a2, b2, c2 := second[positions[0]], second[positions[1]], second[positions[2]]
	oriented := [3]triple{{a1, b1 ^ b2, c1}, {a1 ^ a2, b2, c2}, {a1, b2, c1 ^ c2}}
	var outputs [3]triple
	for output := range outputs {
		outputs[output] = unorient(oriented[output], positions)
	}
	return outputs
}

func constructorPlus(first, second triple, positions [3]int) ([3]triple, error) {
	scheme, err := schemeFromWords([]triple{orient(first, positions), orient(second, positions)})
	if err != nil {
		return [3]triple{}, err
	}
	replacement, err := tensor.NewPlusReplacement(scheme, 0, 1)
	if err != nil {
		return [3]triple{}, err
	}
	inserted := replacement.InsertedTerms()
	if len(inserted) != 3 {
		return [3]triple{}, fmt.Errorf("Plus constructor returned %d terms, want 3", len(inserted))
	}
	var outputs [3]triple
	for index, term := range inserted {
		words, err := termWords(term)
		if err != nil {
			return [3]triple{}, fmt.Errorf("inserted term %d: %w", index, err)
		}
		outputs[index] = unorient(words, positions)
	}
	return outputs, nil
}

type tensorBits [64]uint64

var outerCache sync.Map

func outer(words triple) tensorBits {
	if cached, found := outerCache.Load(words); found {
		return cached.(tensorBits)
	}
	var value tensorBits
	for first := range 16 {
		if words[0]&(uint16(1)<<first) == 0 {
			continue
		}
		for second := range 16 {
			if words[1]&(uint16(1)<<second) == 0 {
				continue
			}
			for third := range 16 {
				if words[2]&(uint16(1)<<third) == 0 {
					continue
				}
				bit := (first*16+second)*16 + third
				value[bit/64] |= uint64(1) << (bit % 64)
			}
		}
	}
	outerCache.Store(words, value)
	return value
}

func tensorSum(words []triple) tensorBits {
	var sum tensorBits
	for _, term := range words {
		value := outer(term)
		for index := range sum {
			sum[index] ^= value[index]
		}
	}
	return sum
}

func targetTensor() tensorBits {
	var target tensorBits
	for i := range 4 {
		for j := range 4 {
			for k := range 4 {
				bit := (((4*i+j)*16)+(4*j+k))*16 + (4*k + i)
				target[bit/64] |= uint64(1) << (bit % 64)
			}
		}
	}
	return target
}

func validateChild(words []triple) error {
	if len(words) != 48 {
		return fmt.Errorf("child has %d terms, want 48", len(words))
	}
	seen := make(map[tensorBits]int, len(words))
	for index, term := range words {
		if term[0] == 0 || term[1] == 0 || term[2] == 0 {
			return fmt.Errorf("nonzero: term %d has a zero factor", index)
		}
		value := outer(term)
		if previous, found := seen[value]; found {
			return fmt.Errorf("distinct: terms %d and %d define the same rank-one tensor", previous, index)
		}
		seen[value] = index
	}
	if tensorSum(words) != targetTensor() {
		return fmt.Errorf("Brent: exact 4096-bit tensor sum differs from the matrix multiplication tensor")
	}
	return nil
}

func enumerateFrontier(root []triple, role string) (*frontier, error) {
	if len(root) != rootTerms {
		return nil, fmt.Errorf("%s root has %d terms, want %d", role, len(root), rootTerms)
	}
	result := &frontier{
		DescriptorStream:        make([]byte, 0, orderedDescriptors*6),
		DescriptorPayloadStream: make([]byte, 0, orderedDescriptors*childPayloadBytes),
	}
	payloads := make([][]byte, 0, orderedDescriptors)
	for first := range rootTerms {
		for second := range rootTerms {
			if first == second {
				continue
			}
			survivors := make([]triple, 0, 45)
			for slot, term := range root {
				if slot != first && slot != second {
					survivors = append(survivors, term)
				}
			}
			for orientationIndex, positions := range orientations {
				descriptorIndex := len(payloads)
				outputs, err := constructorPlus(root[first], root[second], positions)
				if err != nil {
					return nil, fmt.Errorf("%s descriptor %d constructor: %w", role, descriptorIndex, err)
				}
				result.ConstructorReplays++
				formula := formulaPlus(root[first], root[second], positions)
				if outputs != formula {
					return nil, fmt.Errorf("%s descriptor %d constructor/formula mismatch", role, descriptorIndex)
				}
				result.FormulaReplays++
				child := append(append([]triple(nil), survivors...), outputs[:]...)
				if err := validateChild(child); err != nil {
					return nil, fmt.Errorf("%s descriptor %d child validation: %w", role, descriptorIndex, err)
				}
				result.ChildValidations++
				payload := canonicalPayload(child)
				if len(payload) != childPayloadBytes {
					return nil, fmt.Errorf("%s descriptor %d payload has %d bytes", role, descriptorIndex, len(payload))
				}
				result.DescriptorStream = appendU16(result.DescriptorStream, uint16(first), uint16(second))
				result.DescriptorStream = append(result.DescriptorStream, byte(orientationIndex), 0)
				result.DescriptorPayloadStream = append(result.DescriptorPayloadStream, payload...)
				payloads = append(payloads, payload)
			}
		}
	}
	if len(payloads) != orderedDescriptors {
		return nil, fmt.Errorf("%s descriptor count is %d, want %d", role, len(payloads), orderedDescriptors)
	}
	classes, err := exactClasses(payloads, role+" child", digest)
	if err != nil {
		return nil, err
	}
	if len(classes) != canonicalClasses {
		return nil, fmt.Errorf("%s class count is %d, want %d", role, len(classes), canonicalClasses)
	}
	for index, class := range classes {
		if len(class.Members) != 2 {
			return nil, fmt.Errorf("%s class %d has %d aliases, want 2", role, index, len(class.Members))
		}
		result.ClassPayloadStream = append(result.ClassPayloadStream, class.Value...)
		result.AliasStream = appendU32(result.AliasStream, uint32(class.Members[0]), uint32(class.Members[1]))
	}
	result.Classes = classes
	return result, nil
}

func exactClasses(values [][]byte, role string, hash func([]byte) string) ([]exactClass, error) {
	byHash := make(map[string]int, len(values))
	classes := make([]exactClass, 0, len(values))
	for index, value := range values {
		key := hash(value)
		if classIndex, found := byHash[key]; found {
			if !bytes.Equal(classes[classIndex].Value, value) {
				return nil, fmt.Errorf("%s SHA-256 collision on differing exact bytes", role)
			}
			classes[classIndex].Members = append(classes[classIndex].Members, index)
			continue
		}
		byHash[key] = len(classes)
		classes = append(classes, exactClass{Value: append([]byte(nil), value...), Members: []int{index}})
	}
	slices.SortFunc(classes, func(first, second exactClass) int {
		return bytes.Compare(first.Value, second.Value)
	})
	return classes, nil
}

func intersectExact(first, second []exactClass) [][]byte {
	intersection := make([][]byte, 0)
	for left, right := 0, 0; left < len(first) && right < len(second); {
		comparison := bytes.Compare(first[left].Value, second[right].Value)
		switch {
		case comparison < 0:
			left++
		case comparison > 0:
			right++
		default:
			if bytes.Equal(first[left].Value, second[right].Value) {
				intersection = append(intersection, append([]byte(nil), first[left].Value...))
			}
			left++
			right++
		}
	}
	return intersection
}

func verifyCorpusChildSection(corpus, regenerated []byte) error {
	if corpusChildOffset < 0 || corpusChildSectionSize < 0 || corpusChildOffset > len(corpus) || corpusChildSectionSize > len(corpus)-corpusChildOffset {
		return fmt.Errorf("authenticated corpus child section exceeds corpus boundary")
	}
	section := corpus[corpusChildOffset : corpusChildOffset+corpusChildSectionSize]
	if digest(section) != c659ChildStreamSHA256 {
		return fmt.Errorf("authenticated corpus child section SHA-256 mismatch")
	}
	if !bytes.Equal(section, regenerated) {
		return fmt.Errorf("regenerated c659 class payload stream differs from authenticated corpus child section")
	}
	return nil
}
