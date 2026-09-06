#!/usr/bin/env python3
"""Exact native-move census for F3 profile (1,2,2) at altitude four."""

import argparse
import hashlib
import json
import math
import resource
import signal
from collections import Counter, defaultdict, deque
from itertools import combinations, product
from pathlib import Path

P = 3
DIMS = (1, 2, 2)
ALTITUDE = 4
MEMORY_LIMIT = 4 << 30
TIME_LIMIT = 180
MODE_NAMES = ("first", "second", "third")
SPLIT_NAMES = MODE_NAMES
FLIP_SPECS = (
    ("firstSecond", 0, 1, 2),
    ("secondFirst", 1, 0, 2),
    ("firstThird", 0, 2, 1),
    ("thirdFirst", 2, 0, 1),
    ("secondThird", 1, 2, 0),
    ("thirdSecond", 2, 1, 0),
)


def nonzero_vectors(n):
    return tuple(v for v in product(range(P), repeat=n) if any(v))


def add_vectors(x, y):
    return tuple((a + b) % P for a, b in zip(x, y))


def sub_vectors(x, y):
    return tuple((a - b) % P for a, b in zip(x, y))


def scale_vector(q, x):
    return tuple(q * a % P for a in x)


def tensor(factors, coefficient=1):
    return tuple(
        coefficient * factors[0][i] * factors[1][j] * factors[2][k] % P
        for i in range(DIMS[0])
        for j in range(DIMS[1])
        for k in range(DIMS[2])
    )


def mask_of(indices):
    mask = 0
    for index in indices:
        mask |= 1 << index
    return mask


def mask_indices(mask):
    return [index for index in range(32) if mask >> index & 1]


def mask_key(mask):
    return f"{mask:08x}"


def evaluation_code(value):
    return sum(coordinate * P**index for index, coordinate in enumerate(value))


def digest_records(records):
    digest = hashlib.sha256()
    for record in sorted(records):
        digest.update(",".join(str(field) for field in record).encode("ascii"))
        digest.update(b"\n")
    return digest.hexdigest()


def contexts(avoid, maximum_size):
    available = [index for index in range(32) if not (avoid >> index & 1)]
    yield 0
    for size in range(1, maximum_size + 1):
        for choice in combinations(available, size):
            yield mask_of(choice)


def context_count(avoid, maximum_size):
    available = 32 - avoid.bit_count()
    return sum(math.comb(available, size) for size in range(maximum_size + 1))


def state_record(mask, atoms, evaluations, state_index):
    vertex = state_index[mask]
    return {
        "id": vertex,
        "mask": mask_key(mask),
        "cardinality": mask.bit_count(),
        "atom_indices": mask_indices(mask),
        "atoms": [list(atoms[index]) for index in mask_indices(mask)],
        "evaluation": list(evaluations[vertex]),
        "evaluation_code": evaluation_code(evaluations[vertex]),
    }


def split_witness_record(witness):
    mode, factors, x, y = witness
    common = {
        MODE_NAMES[index]: list(factors[index])
        for index in range(3)
        if index != mode
    }
    return {
        "orientation": SPLIT_NAMES[mode],
        "x": list(x),
        "y": list(y),
        "x_plus_y": list(add_vectors(x, y)),
        "common_factors": common,
    }


def flip_witness_record(witness):
    orientation, common, x1, x2, y1, y2 = witness
    name, x_mode, y_mode, common_mode = FLIP_SPECS[orientation]
    return {
        "orientation": name,
        "x_mode": MODE_NAMES[x_mode],
        "y_mode": MODE_NAMES[y_mode],
        "common_mode": MODE_NAMES[common_mode],
        "common": list(common),
        "x1": list(x1),
        "x2": list(x2),
        "y1": list(y1),
        "y2": list(y2),
        "x1_plus_x2": list(add_vectors(x1, x2)),
        "y2_minus_y1": list(sub_vectors(y2, y1)),
    }


def main_census():
    factors = tuple(nonzero_vectors(dimension) for dimension in DIMS)
    assert tuple(map(len, factors)) == (2, 8, 8)

    absorbed_presentations = tuple(product(*factors))
    coefficientful = tuple(
        (coefficient,) + presentation
        for coefficient in (1, 2)
        for presentation in absorbed_presentations
    )
    coefficientful_values = Counter(
        tensor(presentation, coefficient)
        for coefficient, *presentation in coefficientful
    )
    atoms = tuple(sorted(coefficientful_values))
    atom_index = {atom: index for index, atom in enumerate(atoms)}
    assert len(atoms) == 32
    assert set(coefficientful_values.values()) == {8}
    assert all(any(atom) for atom in atoms)
    assert all((atom[0] * atom[3] - atom[1] * atom[2]) % P == 0 for atom in atoms)

    presentation_by_atom = [[] for _ in atoms]
    for presentation in absorbed_presentations:
        presentation_by_atom[atom_index[tensor(presentation)]].append(presentation)
    assert {len(presentations) for presentations in presentation_by_atom} == {4}

    split_by_orientation = [set() for _ in range(3)]
    split_witnesses = {}
    split_stats = []
    for mode in range(3):
        fixed_modes = tuple(index for index in range(3) if index != mode)
        candidate_count = 0
        nonzero_sum_count = 0
        distinct_count = 0
        contextual_witness_incidence = 0
        for fixed0, fixed1, x, y in product(
            factors[fixed_modes[0]],
            factors[fixed_modes[1]],
            factors[mode],
            factors[mode],
        ):
            candidate_count += 1
            summed = add_vectors(x, y)
            if not any(summed):
                continue
            nonzero_sum_count += 1
            full = [None, None, None]
            full[fixed_modes[0]] = fixed0
            full[fixed_modes[1]] = fixed1
            full[mode] = summed
            source = atom_index[tensor(full)]
            full[mode] = x
            left = atom_index[tensor(full)]
            full[mode] = y
            right = atom_index[tensor(full)]
            if left == right:
                continue
            distinct_count += 1
            local = (1 << source, (1 << left) | (1 << right))
            split_by_orientation[mode].add(local)
            witness = (mode, tuple(full), x, y)
            if local not in split_witnesses or witness < split_witnesses[local]:
                split_witnesses[local] = witness
            maximum_context = min(
                ALTITUDE - local[0].bit_count(), ALTITUDE - local[1].bit_count()
            )
            contextual_witness_incidence += context_count(
                local[0] | local[1], maximum_context
            )
        split_stats.append(
            {
                "orientation": SPLIT_NAMES[mode],
                "parameter_tuples": candidate_count,
                "nonzero_sum_witnesses": nonzero_sum_count,
                "finite_set_distinct_witnesses": distinct_count,
                "unique_directed_local_relations": len(split_by_orientation[mode]),
                "contextual_witness_incidences": contextual_witness_incidence,
            }
        )

    flip_by_orientation = [set() for _ in FLIP_SPECS]
    flip_witnesses = {}
    flip_stats = []
    for orientation, (name, x_mode, y_mode, common_mode) in enumerate(FLIP_SPECS):
        candidate_count = 0
        nonzero_output_count = 0
        distinct_count = 0
        contextual_witness_incidence = 0
        for common, x1, x2, y1, y2 in product(
            factors[common_mode],
            factors[x_mode],
            factors[x_mode],
            factors[y_mode],
            factors[y_mode],
        ):
            candidate_count += 1
            summed = add_vectors(x1, x2)
            difference = sub_vectors(y2, y1)
            if not any(summed) or not any(difference):
                continue
            nonzero_output_count += 1
            full = [None, None, None]
            full[common_mode] = common
            full[x_mode], full[y_mode] = x1, y1
            source1 = atom_index[tensor(full)]
            full[x_mode], full[y_mode] = x2, y2
            source2 = atom_index[tensor(full)]
            full[x_mode], full[y_mode] = summed, y1
            target1 = atom_index[tensor(full)]
            full[x_mode], full[y_mode] = x2, difference
            target2 = atom_index[tensor(full)]
            if source1 == source2 or target1 == target2:
                continue
            distinct_count += 1
            local = (
                (1 << source1) | (1 << source2),
                (1 << target1) | (1 << target2),
            )
            flip_by_orientation[orientation].add(local)
            witness = (orientation, common, x1, x2, y1, y2)
            if local not in flip_witnesses or witness < flip_witnesses[local]:
                flip_witnesses[local] = witness
            maximum_context = min(
                ALTITUDE - local[0].bit_count(), ALTITUDE - local[1].bit_count()
            )
            contextual_witness_incidence += context_count(
                local[0] | local[1], maximum_context
            )
        flip_stats.append(
            {
                "orientation": name,
                "x_mode": MODE_NAMES[x_mode],
                "y_mode": MODE_NAMES[y_mode],
                "common_mode": MODE_NAMES[common_mode],
                "parameter_tuples": candidate_count,
                "nonzero_sum_and_difference_witnesses": nonzero_output_count,
                "finite_set_distinct_witnesses": distinct_count,
                "unique_directed_local_relations": len(flip_by_orientation[orientation]),
                "contextual_witness_incidences": contextual_witness_incidence,
            }
        )

    split_relations = set().union(*split_by_orientation)
    flip_relations = set().union(*flip_by_orientation)
    assert len(split_relations) == 192
    assert len(flip_relations) == 1552
    assert all((target, source) in flip_relations for source, target in flip_relations)

    split_oracle = [set() for _ in range(3)]
    for mode in range(3):
        for left in range(32):
            for right in range(left + 1, 32):
                for left_presentation in presentation_by_atom[left]:
                    for right_presentation in presentation_by_atom[right]:
                        if any(
                            left_presentation[index] != right_presentation[index]
                            for index in range(3)
                            if index != mode
                        ):
                            continue
                        summed = add_vectors(
                            left_presentation[mode], right_presentation[mode]
                        )
                        if not any(summed):
                            continue
                        source_presentation = list(left_presentation)
                        source_presentation[mode] = summed
                        source = atom_index[tensor(source_presentation)]
                        split_oracle[mode].add(
                            (1 << source, (1 << left) | (1 << right))
                        )

    flip_oracle = [set() for _ in FLIP_SPECS]
    for orientation, (_, x_mode, y_mode, common_mode) in enumerate(FLIP_SPECS):
        for source1 in range(32):
            for source2 in range(32):
                if source1 == source2:
                    continue
                for first_presentation in presentation_by_atom[source1]:
                    for second_presentation in presentation_by_atom[source2]:
                        if (
                            first_presentation[common_mode]
                            != second_presentation[common_mode]
                        ):
                            continue
                        x1, x2 = (
                            first_presentation[x_mode],
                            second_presentation[x_mode],
                        )
                        y1, y2 = (
                            first_presentation[y_mode],
                            second_presentation[y_mode],
                        )
                        summed = add_vectors(x1, x2)
                        difference = sub_vectors(y2, y1)
                        if not any(summed) or not any(difference):
                            continue
                        target1_presentation = list(first_presentation)
                        target1_presentation[x_mode] = summed
                        target1 = atom_index[tensor(target1_presentation)]
                        target2_presentation = list(second_presentation)
                        target2_presentation[y_mode] = difference
                        target2 = atom_index[tensor(target2_presentation)]
                        if target1 == target2:
                            continue
                        flip_oracle[orientation].add(
                            (
                                (1 << source1) | (1 << source2),
                                (1 << target1) | (1 << target2),
                            )
                        )

    assert split_oracle == split_by_orientation
    assert flip_oracle == flip_by_orientation

    states = []
    for cardinality in range(ALTITUDE + 1):
        states.extend(mask_of(choice) for choice in combinations(range(32), cardinality))
    state_index = {mask: index for index, mask in enumerate(states)}
    assert len(states) == 41449

    evaluations = []
    for state in states:
        value = [0, 0, 0, 0]
        for index in mask_indices(state):
            value = [(x + y) % P for x, y in zip(value, atoms[index])]
        evaluations.append(tuple(value))

    def expand_relations(relations):
        expanded = set()
        for source, target in relations:
            maximum_context = min(
                ALTITUDE - source.bit_count(), ALTITUDE - target.bit_count()
            )
            for context in contexts(source | target, maximum_context):
                expanded.add((source | context, target | context))
        return expanded

    split_context_by_orientation = [
        expand_relations(relations) for relations in split_by_orientation
    ]
    flip_context_by_orientation = [
        expand_relations(relations) for relations in flip_by_orientation
    ]
    split_edges = set().union(*split_context_by_orientation)
    reduction_edges = {(target, source) for source, target in split_edges}
    flip_edges = set().union(*flip_context_by_orientation)
    assert len(split_edges) == 83712
    assert len(reduction_edges) == 83712
    assert len(flip_edges) == 632488
    assert flip_edges == {(target, source) for source, target in flip_edges}

    edge_sets = {
        "split": split_edges,
        "reduction": reduction_edges,
        "flip": flip_edges,
    }
    for edge_kind, edges in edge_sets.items():
        for source, target in edges:
            assert source in state_index and target in state_index, edge_kind
            assert source.bit_count() <= ALTITUDE and target.bit_count() <= ALTITUDE
            assert evaluations[state_index[source]] == evaluations[state_index[target]]

    split_undirected = {
        (min(source, target), max(source, target))
        for source, target in split_edges | reduction_edges
    }
    flip_undirected = {
        (min(source, target), max(source, target)) for source, target in flip_edges
    }
    graph_edges = split_undirected | flip_undirected
    loop_count = sum(source == target for source, target in graph_edges)
    loop_states = {source for source, target in flip_edges if source == target}
    loop_local_source_incidences = sum(
        context_count(
            source,
            min(ALTITUDE - source.bit_count(), ALTITUDE - target.bit_count()),
        )
        for source, target in flip_relations
        if source == target
    )
    strict_edges = {
        (source, target) for source, target in graph_edges if source != target
    }
    assert len(graph_edges) == 403624
    assert loop_count == 7336
    assert len(loop_states) == 7336
    assert loop_local_source_incidences == 7456
    assert len(strict_edges) == 396288

    adjacency = [set() for _ in states]
    for source, target in strict_edges:
        source_vertex, target_vertex = state_index[source], state_index[target]
        adjacency[source_vertex].add(target_vertex)
        adjacency[target_vertex].add(source_vertex)
    adjacency = [tuple(sorted(neighbors, key=lambda x: states[x])) for neighbors in adjacency]
    assert sum(map(len, adjacency)) == 2 * len(strict_edges)

    component = [-1] * len(states)
    components = []
    for root in range(len(states)):
        if component[root] != -1:
            continue
        component_id = len(components)
        queue = [root]
        component[root] = component_id
        for vertex in queue:
            for neighbor in adjacency[vertex]:
                if component[neighbor] == -1:
                    component[neighbor] = component_id
                    queue.append(neighbor)
        components.append(queue)

    component_edge_counts = [0] * len(components)
    evaluation_edge_counts = Counter()
    for source, target in strict_edges:
        source_vertex, target_vertex = state_index[source], state_index[target]
        assert component[source_vertex] == component[target_vertex]
        component_edge_counts[component[source_vertex]] += 1
        evaluation_edge_counts[evaluations[source_vertex]] += 1

    fibers = defaultdict(list)
    endpoint_fibers = defaultdict(list)
    for vertex, value in enumerate(evaluations):
        fibers[value].append(vertex)
        if states[vertex].bit_count() <= 3:
            endpoint_fibers[value].append(vertex)
    assert len(fibers) == 81

    fiber_records = []
    for value in sorted(fibers, key=evaluation_code):
        vertices = fibers[value]
        component_counts = Counter(component[vertex] for vertex in vertices)
        fiber_records.append(
            {
                "evaluation": list(value),
                "evaluation_code": evaluation_code(value),
                "vertex_count": len(vertices),
                "vertices_by_cardinality": {
                    str(cardinality): sum(
                        states[vertex].bit_count() == cardinality for vertex in vertices
                    )
                    for cardinality in range(ALTITUDE + 1)
                },
                "endpoint_count_cardinality_at_most_3": len(endpoint_fibers[value]),
                "strict_edge_count": evaluation_edge_counts[value],
                "component_sizes": sorted(component_counts.values(), reverse=True),
            }
        )

    separated_pairs = []
    distance_distribution = Counter()
    maximum_distance = -1
    maximum_pair = None
    maximum_path = None
    identity_pair_count = 0
    for value in sorted(endpoint_fibers, key=evaluation_code):
        vertices = endpoint_fibers[value]
        for offset, source in enumerate(vertices):
            distances = {source: 0}
            predecessors = {}
            queue = deque([source])
            while queue:
                vertex = queue.popleft()
                for neighbor in adjacency[vertex]:
                    if neighbor not in distances:
                        distances[neighbor] = distances[vertex] + 1
                        predecessors[neighbor] = vertex
                        queue.append(neighbor)
            identity_pair_count += 1
            for target in vertices[offset + 1 :]:
                source_mask, target_mask = states[source], states[target]
                canonical_pair = tuple(sorted((source_mask, target_mask)))
                if component[source] != component[target]:
                    separated_pairs.append(canonical_pair)
                    continue
                distance = distances[target]
                distance_distribution[distance] += 1
                if maximum_pair is None or distance > maximum_distance or (
                    distance == maximum_distance and canonical_pair < maximum_pair
                ):
                    path = [target]
                    while path[-1] != source:
                        path.append(predecessors[path[-1]])
                    path.reverse()
                    path_masks = [states[vertex] for vertex in path]
                    if path_masks[0] != canonical_pair[0]:
                        path_masks.reverse()
                    maximum_distance = distance
                    maximum_pair = canonical_pair
                    maximum_path = path_masks

    separated_pairs = sorted(set(separated_pairs))
    assert len(separated_pairs) == 80
    assert maximum_distance == 4
    assert sum(distance_distribution.values()) + len(separated_pairs) == 183480

    def contextual_witness(source, target):
        candidates = []
        for local_source, local_target in split_relations:
            if local_source & source != local_source:
                continue
            context = source ^ local_source
            if context & (local_source | local_target):
                continue
            if target == context | local_target:
                candidates.append(
                    (
                        0,
                        local_source,
                        local_target,
                        context,
                        split_witnesses[(local_source, local_target)],
                    )
                )
        for local_target, local_source in split_relations:
            if local_source & source != local_source:
                continue
            context = source ^ local_source
            if context & (local_source | local_target):
                continue
            if target == context | local_target:
                candidates.append(
                    (
                        1,
                        local_source,
                        local_target,
                        context,
                        split_witnesses[(local_target, local_source)],
                    )
                )
        for local_source, local_target in flip_relations:
            if local_source & source != local_source:
                continue
            context = source ^ local_source
            if context & (local_source | local_target):
                continue
            if target == context | local_target:
                candidates.append(
                    (
                        2,
                        local_source,
                        local_target,
                        context,
                        flip_witnesses[(local_source, local_target)],
                    )
                )
        assert candidates
        candidate = min(candidates)
        kind_index, local_source, local_target, context, witness = candidate
        return {
            "kind": ("split", "reduction", "flip")[kind_index],
            "local_source_mask": mask_key(local_source),
            "local_source_atoms": mask_indices(local_source),
            "local_target_mask": mask_key(local_target),
            "local_target_atoms": mask_indices(local_target),
            "context_mask": mask_key(context),
            "context_atoms": mask_indices(context),
            "parameters": split_witness_record(witness)
            if kind_index < 2
            else flip_witness_record(witness),
        }

    maximum_path_records = []
    for index, state in enumerate(maximum_path):
        record = state_record(state, atoms, evaluations, state_index)
        if index + 1 < len(maximum_path):
            record["next_edge_witness"] = contextual_witness(
                state, maximum_path[index + 1]
            )
        maximum_path_records.append(record)

    smallest_pair = min(
        separated_pairs,
        key=lambda pair: (
            pair[0].bit_count() + pair[1].bit_count(),
            max(pair[0].bit_count(), pair[1].bit_count()),
            min(pair[0].bit_count(), pair[1].bit_count()),
            pair,
        ),
    )
    assert smallest_pair == (0, 3)
    assert not adjacency[state_index[0]]

    atom_records = [
        {"index": index, "coordinates": list(atom)}
        for index, atom in enumerate(atoms)
    ]
    component_size_distribution = Counter(map(len, components))
    component_signature_distribution = Counter(
        (len(vertices), component_edge_counts[index])
        for index, vertices in enumerate(components)
    )
    degree_distribution = Counter(map(len, adjacency))

    census_hashes = {
        "format": "sha256 over lexicographically sorted records; decimal fields joined by comma and terminated by LF",
        "atoms_index_then_4_coordinates": digest_records(
            (index,) + atom for index, atom in enumerate(atoms)
        ),
        "vertices_state_masks": digest_records((state,) for state in states),
        "local_split_relations_source_target_masks": digest_records(split_relations),
        "local_flip_relations_source_target_masks": digest_records(flip_relations),
        "contextual_split_directed_edges": digest_records(split_edges),
        "contextual_reduction_directed_edges": digest_records(reduction_edges),
        "contextual_flip_directed_edges": digest_records(flip_edges),
        "undirected_graph_edges_including_loops": digest_records(graph_edges),
        "state_mask_then_4_evaluation_coordinates": digest_records(
            (state,) + evaluations[index] for index, state in enumerate(states)
        ),
        "state_mask_then_component_id": digest_records(
            (state, component[index]) for index, state in enumerate(states)
        ),
        "separated_endpoint_pairs": digest_records(separated_pairs),
    }

    result = {
        "schema": "f3-122-field-native-connectivity-census-v1",
        "status": "DISCONNECTED",
        "scope": {
            "field": "F3",
            "profile": [1, 2, 2],
            "altitude": ALTITUDE,
            "endpoint_cardinality_limit": 3,
            "statement": "finite semantic-atom Finset graph only; not a Lean theorem and not an unbounded F3-LG result",
            "source_contract": "Proofs/BilinearComplexity/FieldNativeMoves.lean at accepted revision 318734eb6daa04fa0d960de42c36aa041efb5908",
            "limits": {"seconds": TIME_LIMIT, "address_space_bytes": MEMORY_LIMIT},
        },
        "provenance": {
            "script": "Programs/BilinearComplexity/f3_122_native_connectivity.py",
            "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "deterministic_encoding": {
                "atom": "lexicographic (T000,T001,T010,T011) in {0,1,2}^4",
                "state": "32-bit mask; bit i is atom i",
                "evaluation": "coordinate tuple and little-endian base-3 code sum coordinate[i]*3^i",
                "vertex_order": "cardinality 0..4, then lexicographic atom-index combination",
                "component_order": "first unseen vertex in vertex order",
            },
        },
        "generator_coverage": {
            "nonzero_factor_counts_by_mode": [2, 8, 8],
            "coefficientful_raw_representatives": len(coefficientful),
            "coefficientful_representatives_per_atom": 8,
            "coefficient_absorbed_presentations": len(absorbed_presentations),
            "absorbed_presentations_per_atom": 4,
            "split_orientations": split_stats,
            "flip_orientations": flip_stats,
            "independent_source_presentation_oracle_matches_all_orientation_relations": True,
            "completeness_basis": [
                "Every semantic atom is reached by coefficient absorption; every raw F3 nonzero factor and every absorbed gauge presentation was enumerated.",
                "The three Split constructors and six ordered Flip constructors were enumerated directly with their exact nonzero sum/difference and finite-set distinctness guards.",
                "A second source-presentation enumeration reproduced every orientation-specific local relation exactly.",
                "Every NativeStep is its local source/target plus the unique unchanged context D\\source; all fresh contexts respecting both endpoint altitude bounds were enumerated.",
            ],
        },
        "atoms": {
            "count": len(atoms),
            "all_nonzero_rank_one": True,
            "records": atom_records,
        },
        "vertices": {
            "count": len(states),
            "by_cardinality": {
                str(cardinality): sum(state.bit_count() == cardinality for state in states)
                for cardinality in range(ALTITUDE + 1)
            },
        },
        "edges": {
            "directed_contextual_relations_by_move_kind": {
                "split": len(split_edges),
                "reduction": len(reduction_edges),
                "flip_including_loops": len(flip_edges),
                "all_move_kinds_union_including_loops": len(
                    split_edges | reduction_edges | flip_edges
                ),
            },
            "orientation_specific_contextual_relation_counts_before_cross_orientation_dedup": {
                "split": {
                    SPLIT_NAMES[index]: len(edges)
                    for index, edges in enumerate(split_context_by_orientation)
                },
                "flip": {
                    FLIP_SPECS[index][0]: len(edges)
                    for index, edges in enumerate(flip_context_by_orientation)
                },
            },
            "simple_undirected_endpoint_pairs_by_family": {
                "split_reduction": len(split_undirected),
                "flip_including_loops": len(flip_undirected),
                "all_including_loops": len(graph_edges),
                "loops": loop_count,
                "loop_states_by_cardinality": {
                    str(cardinality): sum(
                        state.bit_count() == cardinality for state in loop_states
                    )
                    for cardinality in range(ALTITUDE + 1)
                },
                "distinct_loop_local_source_incidences": loop_local_source_incidences,
                "strict_nonloop_edges_used_for_connectivity": len(strict_edges),
                "strict_split_reduction_by_endpoint_cardinalities": {
                    f"{left}-{right}": count
                    for (left, right), count in sorted(
                        Counter(
                            tuple(sorted((source.bit_count(), target.bit_count())))
                            for source, target in split_undirected
                            if source != target
                        ).items()
                    )
                },
                "strict_flip_by_endpoint_cardinality": {
                    str(cardinality): count
                    for cardinality, count in sorted(
                        Counter(
                            source.bit_count()
                            for source, target in flip_undirected
                            if source != target
                        ).items()
                    )
                },
            },
            "all_generated_contextual_edges_preserve_exact_evaluation": True,
            "all_generated_contextual_endpoints_are_legal_vertices": True,
            "directed_flip_reverse_closure": True,
            "directed_split_reduction_reverse_closure": True,
        },
        "components": {
            "count": len(components),
            "size_distribution": [
                {"size": size, "count": count}
                for size, count in sorted(component_size_distribution.items())
            ],
            "size_edge_signature_distribution": [
                {"vertices": signature[0], "strict_edges": signature[1], "count": count}
                for signature, count in sorted(component_signature_distribution.items())
            ],
            "strict_degree_distribution": [
                {"degree": degree, "vertex_count": count}
                for degree, count in sorted(degree_distribution.items())
            ],
            "fiber_count": len(fibers),
            "fiber_records": fiber_records,
        },
        "endpoint_pair_census": {
            "endpoint_vertices": sum(len(vertices) for vertices in endpoint_fibers.values()),
            "unordered_distinct_equal_evaluation_pairs": 183480,
            "connected_pairs": sum(distance_distribution.values()),
            "separated_pairs": len(separated_pairs),
            "identity_pairs_not_in_distinct_pair_count": identity_pair_count,
            "connected_distance_distribution": {
                str(distance): distance_distribution[distance]
                for distance in sorted(distance_distribution)
            },
            "maximum_connected_distance": maximum_distance,
            "maximum_distance_pair": [mask_key(mask) for mask in maximum_pair],
            "maximum_distance_path": maximum_path_records,
            "all_separated_pairs": [
                [mask_key(source), mask_key(target)]
                for source, target in separated_pairs
            ],
        },
        "smallest_separated_pair": {
            "ordering": "minimize total cardinality, then maximum cardinality, then minimum cardinality, then masks",
            "left": state_record(
                smallest_pair[0], atoms, evaluations, state_index
            ),
            "right": state_record(
                smallest_pair[1], atoms, evaluations, state_index
            ),
            "certificate": [
                "Both evaluations are (0,0,0,0): atom 1 is -atom 0 in F3.",
                "Every NativeReplacement source is a singleton or a distinct pair.",
                "NativeStep.source_subset therefore rules out every step from the empty state.",
                "The exhaustive graph gives the empty state strict degree zero; the other 536 zero-fiber vertices form one component.",
                "All 80 separated endpoint pairs are the empty state paired with a nonempty zero-evaluation state of cardinality at most three.",
            ],
        },
        "census_hashes": census_hashes,
        "checks": {
            "atom_universe_from_all_coefficients_and_gauges": True,
            "all_atoms_nonzero_and_rank_one": True,
            "independent_local_oracle_exact_match": True,
            "local_evaluation_preservation": all(
                evaluations[state_index[source]] == evaluations[state_index[target]]
                for source, target in split_relations | flip_relations
            ),
            "contextual_evaluation_preservation": True,
            "state_legality": True,
            "component_partition_complete": sum(map(len, components)) == len(states),
            "endpoint_pair_partition_complete": sum(distance_distribution.values())
            + len(separated_pairs)
            == 183480,
        },
    }
    return result


def serialized_result():
    return (json.dumps(main_census(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def impose_limits():
    soft, hard = resource.getrlimit(resource.RLIMIT_AS)
    finite_hard = MEMORY_LIMIT if hard == resource.RLIM_INFINITY else min(hard, MEMORY_LIMIT)
    finite_soft = min(MEMORY_LIMIT, finite_hard)
    resource.setrlimit(resource.RLIMIT_AS, (finite_soft, finite_hard))
    signal.alarm(TIME_LIMIT)


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--verify", type=Path)
    return parser.parse_args()


def run():
    arguments = parse_args()
    impose_limits()
    output = serialized_result()
    if arguments.verify is None:
        print(output.decode("utf-8"), end="")
        return
    expected = arguments.verify.read_bytes()
    if output != expected:
        raise SystemExit(f"census mismatch: regenerate {arguments.verify}")
    print(f"verified {arguments.verify} ({hashlib.sha256(output).hexdigest()})")


if __name__ == "__main__":
    run()
