package main

import (
	"bytes"
	"fmt"
	"slices"
	"strconv"
)

type validationCounts struct {
	rootBrent, parentClassBrent                                         int
	plusConstructor, inverseConstructor                                 int
	forwardExact, equationHits, localReplay, scatterReplay, parentExact int
	bucketOccurrences, inverseConstructorResidualFailure                int
}

type regeneration struct {
	sections   map[string][]byte
	semantic   map[string]any
	validation validationCounts
}

func regenerate(root []triple, raw []byte) (*regeneration, error) {
	return regenerateWithOutcome(root, raw, deriveOutcome)
}

func regenerateWithOutcome(root []triple, raw []byte, outcome outcomeDeriver) (*regeneration, error) {
	return regenerateWithDependencies(root, raw, productionRegenerationDependencies(), outcome)
}

func regenerateWithDependencies(root []triple, raw []byte, dependencies regenerationDependencies, outcome outcomeDeriver) (*regeneration, error) {
	target := targetTensor()
	gates := regenerationGates{dependencies: dependencies}
	if digest(tensorBytes(target)) != tensorSHA256 {
		return nil, fmt.Errorf("target tensor encoding mismatch")
	}
	if err := gates.validateRoot(root, target); err != nil {
		return nil, fmt.Errorf("root exact tensor/nonzero/distinct/Brent replay failed: %w", err)
	}
	rootOrdered, rootCanonical := orderedPayload(root), canonicalPayload(root)
	if digest(rootOrdered) != rootOrderedSHA256 || digest(rootCanonical) != rootCanonicalSHA256 {
		return nil, fmt.Errorf("root payload checksum mismatch")
	}

	forward := make([]forwardRow, 0, 12972)
	childValues := make([][]byte, 0, 12972)
	orderedValues := make([][]triple, 0, 12972)
	provenances := make([][]byte, 0, 12972)
	for first := range 47 {
		for second := range 47 {
			if first == second {
				continue
			}
			survivors := make([]triple, 0, 45)
			provenance := make([]byte, 0, 48)
			for slot, term := range root {
				if slot != first && slot != second {
					survivors = append(survivors, term)
					provenance = append(provenance, byte(slot))
				}
			}
			for orientationIndex, positions := range orientations {
				outputs := plus(root[first], root[second], positions, 0)
				constructorOutputs, err := gates.constructPlus(root[first], root[second], positions)
				if err != nil {
					return nil, fmt.Errorf("forward descriptor %d Plus constructor: %w", len(forward), err)
				}
				if constructorOutputs != outputs {
					return nil, fmt.Errorf("forward descriptor %d Plus constructor ordered outputs differ", len(forward))
				}
				terms := append(append([]triple(nil), survivors...), outputs[:]...)
				if err := gates.validateForward(outputs, [2]triple{root[first], root[second]}, terms); err != nil {
					return nil, fmt.Errorf("forward descriptor %d exact output validation: %w", len(forward), err)
				}
				childValues = append(childValues, canonicalPayload(terms))
				orderedValues = append(orderedValues, terms)
				provenances = append(provenances, append(append([]byte(nil), provenance...), 128, 129, 130))
				forward = append(forward, forwardRow{uint16(first), uint16(second), uint8(orientationIndex), 0, 0})
			}
		}
	}
	children, childLookup, err := exactClasses(childValues, "child")
	if err != nil {
		return nil, err
	}
	for index, value := range childValues {
		child := childLookup[string(value)]
		forward[index].child = uint16(child)
	}
	if len(children) != 6486 {
		return nil, fmt.Errorf("unique child count is %d, want 6486", len(children))
	}
	for index := range children {
		if len(children[index].members) != 2 {
			return nil, fmt.Errorf("child %d has %d aliases", index, len(children[index].members))
		}
	}

	sections := make(map[string][]byte, len(sectionOrder))
	var data []byte
	for _, row := range forward {
		data = appendU16(data, row.first, row.second)
		data = append(data, row.orientation, row.variant)
		data = appendU16(data, row.child)
	}
	sections["forward_descriptors"] = data
	data = nil
	for _, class := range children {
		data = append(data, class.value...)
	}
	sections["child_payloads"] = data
	data = nil
	for _, class := range children {
		data = appendU32(data, uint32(class.members[0]), uint32(class.members[1]))
	}
	sections["child_aliases"] = data

	childTerms := make([][]triple, len(children))
	data = nil
	for childIndex, class := range children {
		least := class.members[0]
		terms := orderedValues[least]
		canonical := append([]triple(nil), terms...)
		slices.SortFunc(canonical, compareTriple)
		orderedToCanonical := make([]byte, 48)
		canonicalToOrdered := make([]byte, 48)
		for orderedIndex, term := range terms {
			canonicalIndex := slices.Index(canonical, term)
			orderedToCanonical[orderedIndex] = byte(canonicalIndex)
		}
		for canonicalIndex, term := range canonical {
			orderedIndex := slices.Index(terms, term)
			canonicalToOrdered[canonicalIndex] = byte(orderedIndex)
		}
		for index := range 48 {
			if canonicalToOrdered[orderedToCanonical[index]] != byte(index) {
				return nil, fmt.Errorf("child %d ordered maps are not inverse", childIndex)
			}
		}
		data = appendU32(data, uint32(least))
		data = append(data, orderedPayload(terms)...)
		data = append(data, orderedToCanonical...)
		data = append(data, canonicalToOrdered...)
		data = append(data, provenances[least]...)
		childTerms[childIndex] = canonical
	}
	sections["ordered_realizations"] = data

	wedges := make([]wedgeRow, 0, 7758)
	descriptors := make([]descriptorRow, 0, 46548)
	accepted := make([]acceptedRow, 0, 38916)
	sourceValues := make([][]byte, 0, 38916)
	parentValues := make([][]byte, 0, 38916)
	for childIndex, terms := range childTerms {
		candidates, err := enumerateTypedWedges(terms, func(mode, color int, term triple) error {
			return gates.observeBucket(childIndex, mode, color, term)
		})
		if err != nil {
			return nil, fmt.Errorf("child %d factor bucket occurrence: %w", childIndex, err)
		}
		for _, candidate := range candidates {
			center, a, b := candidate.center, candidate.a, candidate.b
			residual, pass := candidate.residual, candidate.pass
			wedgeIndex := len(wedges)
			passByte := uint8(0)
			if pass {
				passByte = 1
			}
			wedges = append(wedges, wedgeRow{uint16(childIndex), uint8(center), uint8(a.color), uint8(b.color), uint8(a.leg), uint8(b.leg), uint8(residual), passByte, uint32(len(descriptors))})
			for assignment := range 2 {
				x, y, legX, legY := a.color, b.color, a.leg, b.leg
				if assignment == 1 {
					x, y, legX, legY = b.color, a.color, b.leg, a.leg
				}
				positionTable := [3][3]int{{legX, legY, residual}, {residual, legX, legY}, {legY, residual, legX}}
				for variant, positions := range positionTable {
					row := descriptorRow{wedge: uint32(wedgeIndex), child: uint16(childIndex), assignment: uint8(assignment), variant: uint8(variant), x: uint8(x), y: uint8(y), z: uint8(center), i: uint8(positions[0]), j: uint8(positions[1]), k: uint8(positions[2]), pass: passByte, terminal: 0, sourceClass: 65535, parentClass: 65535, accepted: ^uint32(0), alias: ^uint32(0)}
					if pass {
						outputs := [3]triple{terms[x], terms[y], terms[center]}
						sources, replay, mask := inverse(outputs, positions, variant)
						if !gates.validateEquations(outputs, sources, replay, mask) {
							row.terminal = 2
						} else {
							constructorSources, err := gates.constructInverse(outputs, positions, variant, pass)
							if err != nil {
								return nil, fmt.Errorf("descriptor %d inverse constructor: %w", len(descriptors), err)
							}
							if constructorSources != sources {
								return nil, fmt.Errorf("descriptor %d inverse constructor ordered sources differ", len(descriptors))
							}
							if !sourceLegal(sources) {
								row.terminal = 1
							} else {
								if err := gates.validateLocal(sources, replay, outputs); err != nil {
									return nil, fmt.Errorf("descriptor %d inverse local replay: %w", len(descriptors), err)
								}
								survivors := make([]triple, 0, 45)
								for slot, term := range terms {
									if slot != x && slot != y && slot != center {
										survivors = append(survivors, term)
									}
								}
								parent := append(append([]triple(nil), survivors...), sources[:]...)
								parentPayload := canonicalPayload(parent)
								if err := gates.validateScatter(survivors, replay, children[childIndex].value); err != nil {
									return nil, fmt.Errorf("descriptor %d accepted scatter: %w", len(descriptors), err)
								}
								parentPass := gates.validateParent(parent, target) == nil
								if !parentPass {
									row.terminal = 3
								} else {
									row.terminal = 5
									if bytes.Equal(parentPayload, rootCanonical) {
										row.terminal = 4
									}
									sortedSources := sources
									if compareTriple(sortedSources[0], sortedSources[1]) > 0 {
										sortedSources[0], sortedSources[1] = sortedSources[1], sortedSources[0]
									}
									sourcePayload := appendU16(nil, sortedSources[0][0], sortedSources[0][1], sortedSources[0][2], sortedSources[1][0], sortedSources[1][1], sortedSources[1][2])
									sourceValues = append(sourceValues, sourcePayload)
									parentValues = append(parentValues, parentPayload)
									row.accepted = uint32(len(accepted))
									accepted = append(accepted, acceptedRow{uint32(len(descriptors)), mask, sources, 0, 0, 0, 31, row.terminal})
								}
							}
						}
					}
					descriptors = append(descriptors, row)
				}
			}
		}
	}

	sourceClasses, sourceLookup, err := exactClasses(sourceValues, "source class")
	if err != nil {
		return nil, err
	}
	parentClasses, parentLookup, err := exactClasses(parentValues, "parent class")
	if err != nil {
		return nil, err
	}
	for index, class := range parentClasses {
		terms, err := decodeCanonical(class.value, 47)
		if err != nil {
			return nil, err
		}
		if err := gates.validateParentClass(terms); err != nil {
			return nil, fmt.Errorf("parent class %d exact tensor checks: %w", index, err)
		}
	}
	aliasLookup, err := reciprocalAliasLookup(forward, root)
	if err != nil {
		return nil, err
	}
	for index := range accepted {
		row := &accepted[index]
		descriptor := &descriptors[row.descriptor]
		row.sourceClass = uint16(sourceLookup[string(sourceValues[index])])
		row.parentClass = uint16(parentLookup[string(parentValues[index])])
		descriptor.sourceClass = row.sourceClass
		descriptor.parentClass = row.parentClass
	}
	if err := assignReciprocalAliases(accepted, descriptors, aliasLookup); err != nil {
		return nil, err
	}
	if err := encodeTailSections(sections, wedges, descriptors, accepted, sourceClasses, parentClasses, rootCanonical); err != nil {
		return nil, err
	}
	counts := gates.counts
	if counts.plusConstructor != len(forward) || counts.forwardExact != len(forward) {
		return nil, fmt.Errorf("forward constructor/check counts are %d/%d, want %d", counts.plusConstructor, counts.forwardExact, len(forward))
	}
	if counts.inverseConstructor != counts.equationHits || counts.equationHits != 38916 {
		return nil, fmt.Errorf("inverse constructor/equation counts are %d/%d", counts.inverseConstructor, counts.equationHits)
	}
	if counts.localReplay != len(accepted) || counts.scatterReplay != len(accepted) || counts.parentExact != len(accepted) {
		return nil, fmt.Errorf("accepted replay counts are local=%d scatter=%d parent=%d accepted=%d", counts.localReplay, counts.scatterReplay, counts.parentExact, len(accepted))
	}
	if counts.bucketOccurrences != len(children)*48*3 {
		return nil, fmt.Errorf("factor bucket occurrence count is %d", counts.bucketOccurrences)
	}
	semantic, err := buildSemantic(sections, root, raw, rootOrdered, rootCanonical, children, wedges, descriptors, accepted, sourceClasses, parentClasses, forward, outcome)
	if err != nil {
		return nil, err
	}
	return &regeneration{sections: sections, semantic: semantic, validation: counts}, nil
}

type aliasKey struct {
	child         uint16
	first, second triple
}

func assignReciprocalAliases(accepted []acceptedRow, descriptors []descriptorRow, lookup map[aliasKey]uint32) error {
	for index := range accepted {
		row := &accepted[index]
		if int(row.descriptor) >= len(descriptors) {
			return fmt.Errorf("accepted witness descriptor is out of range")
		}
		descriptor := &descriptors[row.descriptor]
		alias, ok := lookup[aliasKey{descriptor.child, row.sources[0], row.sources[1]}]
		if !ok {
			return fmt.Errorf("accepted witness has no reciprocal alias")
		}
		row.alias = alias
		descriptor.alias = alias
	}
	return nil
}

func reciprocalAliasLookup(forward []forwardRow, root []triple) (map[aliasKey]uint32, error) {
	lookup := make(map[aliasKey]uint32, len(forward))
	for index, row := range forward {
		if int(row.first) >= len(root) || int(row.second) >= len(root) {
			return nil, fmt.Errorf("forward descriptor %d source slot is out of range", index)
		}
		key := aliasKey{row.child, root[row.first], root[row.second]}
		if previous, exists := lookup[key]; exists {
			return nil, fmt.Errorf("reciprocal alias key collision between forward descriptors %d and %d", previous, index)
		}
		lookup[key] = uint32(index)
	}
	return lookup, nil
}

func decodeCanonical(value []byte, rank int) ([]triple, error) {
	if len(value) != 8+6*rank || value[0] != 4 || value[2] != 4 || value[4] != 4 || int(value[6]) != rank {
		return nil, fmt.Errorf("canonical payload header/size mismatch")
	}
	terms := make([]triple, rank)
	for index := range rank {
		offset := 8 + 6*index
		terms[index] = triple{uint16(value[offset]) | uint16(value[offset+1])<<8, uint16(value[offset+2]) | uint16(value[offset+3])<<8, uint16(value[offset+4]) | uint16(value[offset+5])<<8}
	}
	return terms, nil
}

func profile(values map[int]int) map[string]any {
	result := make(map[string]any, len(values))
	for key, value := range values {
		result[strconv.Itoa(key)] = value
	}
	return result
}
