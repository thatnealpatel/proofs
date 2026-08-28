package main

import (
	"bytes"
	"fmt"
	"slices"
)

func parentClassification(value, rootCanonical []byte) (byte, byte) {
	if bytes.Equal(value, rootCanonical) {
		return 0, 0
	}
	return 1, 1
}

func encodeTailSections(sections map[string][]byte, wedges []wedgeRow, descriptors []descriptorRow, accepted []acceptedRow, sources, parents []exactClass, rootCanonical []byte) error {
	var data []byte
	for _, row := range wedges {
		data = appendU16(data, row.child)
		data = append(data, row.center, row.a, row.b, row.legA, row.legB, row.residual, row.pass)
		data = appendU32(data, row.firstDescriptor)
	}
	sections["raw_wedges"] = data
	data = nil
	for _, row := range descriptors {
		data = appendU32(data, row.wedge)
		data = appendU16(data, row.child)
		data = append(data, row.assignment, row.variant, row.x, row.y, row.z, row.i, row.j, row.k, row.pass, row.terminal)
		data = appendU16(data, row.sourceClass, row.parentClass)
		data = appendU32(data, row.accepted, row.alias)
	}
	sections["derived_descriptors"] = data
	data = nil
	for _, row := range accepted {
		data = appendU32(data, row.descriptor)
		data = appendU16(data, row.mask)
		data = appendU16(data, row.sources[0][0], row.sources[0][1], row.sources[0][2], row.sources[1][0], row.sources[1][1], row.sources[1][2])
		data = appendU16(data, row.sourceClass, row.parentClass)
		data = appendU32(data, row.alias)
		data = append(data, row.flags, row.terminal)
	}
	sections["accepted_records"] = data
	data = nil
	for _, class := range sources {
		if len(class.members) > 65535 {
			return fmt.Errorf("source class multiplicity overflow")
		}
		data = append(data, class.value...)
		data = appendU16(data, uint16(len(class.members)))
	}
	sections["source_classes"] = data
	data = nil
	for _, class := range parents {
		classification, orbitStatus := parentClassification(class.value, rootCanonical)
		data = append(data, class.value...)
		data = appendU32(data, uint32(len(class.members)))
		data = append(data, classification, orbitStatus)
	}
	sections["parent_classes"] = data
	type coverageRow struct{ alias, accepted uint32 }
	coverage := make([]coverageRow, len(accepted))
	for index, row := range accepted {
		coverage[index] = coverageRow{row.alias, uint32(index)}
	}
	slices.SortFunc(coverage, func(a, b coverageRow) int {
		if a.alias < b.alias {
			return -1
		}
		if a.alias > b.alias {
			return 1
		}
		if a.accepted < b.accepted {
			return -1
		}
		if a.accepted > b.accepted {
			return 1
		}
		return 0
	})
	data = nil
	for _, row := range coverage {
		data = appendU32(data, row.alias, row.accepted)
	}
	sections["alias_inverse_coverage"] = data
	return nil
}

func classifyTerminal(residual, equations, sources, parent, exactRoot bool) int {
	if !residual {
		return 0
	}
	if !equations {
		return 2
	}
	if !sources {
		return 1
	}
	if !parent {
		return 3
	}
	if exactRoot {
		return 4
	}
	return 5
}

type outcomeDeriver func(map[string]int, int) (string, string, int, int, error)
type semanticDigestDeriver func(map[string]any) (string, error)

func deriveOutcome(partition map[string]int, total int) (string, string, int, int, error) {
	sum := 0
	for _, name := range terminals {
		value, ok := partition[name]
		if !ok || value < 0 {
			return "", "", 0, 0, fmt.Errorf("terminal partition is incomplete")
		}
		sum += value
	}
	if len(partition) != len(terminals) || sum != total {
		return "", "", 0, 0, fmt.Errorf("terminal partition total mismatch")
	}
	failures := partition["source_policy_failure"] + partition["inverse_equation_failure"] + partition["invalid_parent"]
	alternates := partition["alternate_valid_parent"]
	if failures != 0 {
		return "incomplete", "incomplete", failures, alternates, nil
	}
	if alternates != 0 {
		return "complete", "complete_counterexample_found", failures, alternates, nil
	}
	return "complete", "complete_no_counterexample_found", failures, alternates, nil
}

func deriveSemanticDigest(semantic map[string]any) (string, error) {
	encoded, err := canonicalJSON(semantic)
	if err != nil {
		return "", err
	}
	return digest(append([]byte(schema+"\x00semantic\x00"), encoded...)), nil
}

func buildManifest(sections map[string][]byte) ([]any, []byte, error) {
	manifest := make([]any, 0, len(sectionContracts))
	corpus := make([]byte, 0, corpusSize)
	offset := 0
	for index, contract := range sectionContracts {
		if contract.name != sectionOrder[index] {
			return nil, nil, fmt.Errorf("section contract order mismatch")
		}
		value, ok := sections[contract.name]
		if !ok {
			return nil, nil, fmt.Errorf("section omitted: %s", contract.name)
		}
		if len(value)%contract.recordSize != 0 {
			return nil, nil, fmt.Errorf("section %s record size mismatch", contract.name)
		}
		manifest = append(manifest, map[string]any{"id": contract.name, "offset": offset, "size": len(value), "count": len(value) / contract.recordSize, "record_size": contract.recordSize, "endianness": "little", "layout": contract.layout, "fields": contract.fields, "payload_sha256": digest(value), "domain_separated_sha256": sectionDigest(contract.name, value)})
		corpus = append(corpus, value...)
		offset += len(value)
	}
	return manifest, corpus, nil
}

func domainContract() map[string]any {
	positions := make([]any, len(orientations))
	for index, value := range orientations {
		positions[index] = []int{value[0], value[1], value[2]}
	}
	return map[string]any{
		"field":                  "GF(2) with bitwise-XOR addition",
		"forward":                "all exact 47x46 ordered source-slot pairs, then orientations in the frozen order, variant 0 only",
		"orientation_order":      orientationNames,
		"orientation_positions":  positions,
		"forward_enumeration":    "source_first_root_slot major, source_second_root_slot major skipping equality, orientation major",
		"forward_formula":        formulas[0],
		"child_canonicalization": "<4H dimensions/rank followed by 48 complete numeric <A,B,C> tuples sorted lexicographically by their unsigned 16-bit values, each then encoded as exact little-endian <HHH> bytes",
		"wedge_enumeration":      "child byte order, center canonical slot, unordered color slots color_a<color_b; each color must share the center factor on exactly one leg and the two unique legs must differ",
		"factor_buckets":         "for every child and mode, map each exact 16-bit factor word to every canonical color occurrence; no color or occurrence is discarded",
		"derived_enumeration":    "wedge major, color assignment 0 then 1, variant 0 then 1 then 2",
		"assignment_semantics":   "assignment 0 is X=color_a,Y=color_b and assignment 1 swaps them; Z is center",
		"orientation_table":      map[string]any{"variant_0": []string{"leg_X", "leg_Y", "residual_leg"}, "variant_1": []string{"residual_leg", "leg_X", "leg_Y"}, "variant_2": []string{"leg_Y", "residual_leg", "leg_X"}},
		"formulas":               formulas,
		"residual_closure":       "direct 16-bit XOR equality Z[residual_leg]=X[residual_leg] XOR Y[residual_leg]; no matrix or rank factorization",
		"inverse":                "recover from formula outputs X and Y, record all nine factor equations, replay the executable formula, enforce both sources nonzero and unequal factorwise, replace X/Y/Z by the sources, and validate exact tensor/nonzero/distinct/scatter bytes",
		"parent_classification":  "exact equality of the 290-byte canonical parent payload with the frozen c659 canonical payload; every other valid exact payload is retained as alternate with unknown orbit status",
	}
}

func buildSemantic(sections map[string][]byte, root []triple, raw, rootOrdered, rootCanonical []byte, children []exactClass, wedges []wedgeRow, descriptors []descriptorRow, accepted []acceptedRow, sourceClasses, parentClasses []exactClass, forward []forwardRow, outcome outcomeDeriver) (map[string]any, error) {
	manifest, corpus, err := buildManifest(sections)
	if err != nil {
		return nil, err
	}
	terminalCounts := make(map[string]int, len(terminals))
	for _, name := range terminals {
		terminalCounts[name] = 0
	}
	residualAdmissible := 0
	childWedges := make(map[int]int)
	for _, row := range wedges {
		childWedges[int(row.child)]++
	}
	wedgeProfile := make(map[int]int)
	for child := range children {
		wedgeProfile[childWedges[child]]++
	}
	for _, row := range descriptors {
		if int(row.terminal) >= len(terminals) {
			return nil, fmt.Errorf("terminal code out of range")
		}
		terminalCounts[terminals[row.terminal]]++
		residualAdmissible += int(row.pass)
	}
	aliasProfile := make(map[int]int)
	for _, class := range children {
		aliasProfile[len(class.members)]++
	}
	sourceProfile := make(map[int]int)
	for _, class := range sourceClasses {
		sourceProfile[len(class.members)]++
	}
	coverageCounts := make(map[uint32]int)
	for _, row := range accepted {
		coverageCounts[row.alias]++
	}
	coverageProfile := make(map[int]int)
	for _, count := range coverageCounts {
		coverageProfile[count]++
	}
	exactParentClasses := 0
	for _, class := range parentClasses {
		if bytes.Equal(class.value, rootCanonical) {
			exactParentClasses++
		}
	}
	status, result, integrityFailures, alternateCount, err := outcome(terminalCounts, len(descriptors))
	if err != nil {
		return nil, err
	}
	terminalPartition := make(map[string]any, len(terminals))
	terminalCodes := make(map[string]any, len(terminals))
	for index, name := range terminals {
		terminalPartition[name] = terminalCounts[name]
		terminalCodes[name] = index
	}
	checks := map[string]any{
		"all_forward_children_exact_tensor_nonzero_distinct": true,
		"digest_collisions_on_differing_exact_bytes_fatal":   true,
		"every_child_has_two_forward_aliases":                true,
		"ordered_maps_complete_and_inverse":                  true,
		"all_nine_inverse_equations_recorded":                true,
		"accepted_sources_nonzero_and_factorwise_different":  true,
		"accepted_parents_exact_tensor_nonzero_distinct":     true,
		"accepted_forward_scatter_exact":                     true,
		"reciprocal_alias_coverage_complete":                 len(coverageCounts) == len(forward),
	}
	for _, row := range accepted {
		if row.mask != 511 || row.flags != 31 || !sourceLegal(row.sources) {
			return nil, fmt.Errorf("accepted record check failed")
		}
	}
	counts := map[string]any{
		"forward_descriptors": len(forward), "unique_children": len(children), "forward_alias_multiplicity_profile": profile(aliasProfile), "child_payload_stream_bytes": len(sections["child_payloads"]),
		"raw_wedges": len(wedges), "child_raw_wedge_profile": profile(wedgeProfile), "derived_descriptors": len(descriptors), "terminal_partition": terminalPartition,
		"residual_failures": len(descriptors) - residualAdmissible, "residual_admissible": residualAdmissible, "accepted_records": len(accepted), "source_classes": len(sourceClasses), "source_class_multiplicity_profile": profile(sourceProfile),
		"parent_payload_classes": len(parentClasses), "exact_c659_parent_classes": exactParentClasses, "alternate_parent_classes": len(parentClasses) - exactParentClasses,
		"forward_aliases_covered": len(coverageCounts), "inverse_witnesses_per_forward_alias_profile": profile(coverageProfile),
	}
	negativeScope := map[string]any{"statement": "No alternate exact parent occurs in the enumerated domain when result is complete_no_counterexample_found.", "included": "the exact frozen c659 root, fixed variant-0 all-forward-child domain, and all-term typed-wedge descriptors described here", "excluded": []string{"other roots", "other forward variants", "nonliteral equivalence", "the c680 bridge", "rank 46", "global orbit classification", "tensor-rank minimality"}}
	semantic := map[string]any{
		"schema": schema, "status": status, "result": result,
		"stable_ids": map[string]any{"source": sourceID, "summary": summaryID, "corpus": corpusID, "root": rootID},
		"root":       map[string]any{"raw_bytes": len(raw), "raw_sha256": digest(raw), "ordered_factor_major_bytes": len(rootOrdered), "ordered_factor_major_sha256": digest(rootOrdered), "unordered_canonical_bytes": len(rootCanonical), "unordered_canonical_sha256": digest(rootCanonical), "tensor_bytes": 512, "tensor_sha256": digest(tensorBytes(targetTensor())), "tensor_exact": true, "nonzero": true, "distinct": true},
		"domain":     domainContract(), "counts": counts,
		"outcome": map[string]any{"complete_partition": true, "integrity_or_replay_failure_count": integrityFailures, "exact_c659_parent_witnesses": terminalCounts["exact_c659_parent"], "alternate_valid_parent_witnesses": alternateCount, "alternate_orbit_status": func() string {
			if alternateCount != 0 {
				return "unknown"
			}
			return "not_applicable"
		}()},
		"negative_scope": negativeScope,
		"corpus":         map[string]any{"repository_relative_id": corpusID, "bytes": len(corpus), "sha256": digest(corpus), "section_digest_domain": "SHA-256(schema ASCII || NUL || 'section' || NUL || section id ASCII || NUL || exact section bytes)", "strict_section_order": sectionOrder, "sections": manifest, "sentinels": map[string]any{"missing_u16": 65535, "missing_u32": uint64(4294967295)}, "terminal_codes": terminalCodes},
		"checks":         checks,
	}
	return semantic, nil
}
