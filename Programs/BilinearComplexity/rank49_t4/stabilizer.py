#!/usr/bin/env python3
"""Deterministic producer and checker for the fixed rank-49 T4-A stabilizer artifact."""

from __future__ import annotations

import argparse
import collections
import hashlib
import itertools
import json
import math
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
REPOSITORY_RELATIVE_DIRECTORY = Path("Programs/BilinearComplexity/rank49_t4")
SOURCE_REPOSITORY_RELATIVE = REPOSITORY_RELATIVE_DIRECTORY / "fixtures" / "4x4x4_m49_c680_iteration65_Z2.txt"
ORIGINAL_EXTERNAL_SOURCE_LOCATOR = "/home/exedev/x/tensor/data/z2/4x4x4_m49_c680_iteration65_Z2.txt"
SOURCE = HERE / "fixtures" / "4x4x4_m49_c680_iteration65_Z2.txt"
SOURCE_SHA256 = "5fc92a6bf83fc29d9527ab100bad5d72d769178b616b31a36c3c0c0b8ad9d09d"
REPOSITORY_REVISION = "6866f8be63692dc918e26d75db9414325b03b78c"
PRODUCER_REPOSITORY_RELATIVE = REPOSITORY_RELATIVE_DIRECTORY / "stabilizer.py"
REPLAY_REPOSITORY_RELATIVE = REPOSITORY_RELATIVE_DIRECTORY / "stabilizer_replay.py"
ARTIFACT_REPOSITORY_RELATIVE = REPOSITORY_RELATIVE_DIRECTORY / "artifacts" / "stabilizer.json"
ARTIFACT = HERE / "artifacts" / "stabilizer.json"
REPLAY = HERE / "stabilizer_replay.py"
ORIENTATIONS = ("id", "cyc", "cyc2", "rev", "rev_cyc", "rev_cyc2")
ORIENTATION_FORMULAS = {
    "id": "(U,V,W)",
    "cyc": "(V,W,U)",
    "cyc2": "(W,U,V)",
    "rev": "(T(W),T(V),T(U))",
    "rev_cyc": "(T(U),T(W),T(V))",
    "rev_cyc2": "(T(V),T(U),T(W))",
}
OUTER_TORUS_COORDINATE_LABELS = {
    "id": "(p,q,r)",
    "cyc": "(q,r,p)",
    "cyc2": "(r,p,q)",
    "rev": "(p^(-1),r^(-1),q^(-1))",
    "rev_cyc": "(q^(-1),p^(-1),r^(-1))",
    "rev_cyc2": "(r^(-1),q^(-1),p^(-1))",
}
OUTER_TORUS_MONOMIAL_ACTION = {
    "id": ((0, 1), (1, 1), (2, 1)),
    "cyc": ((1, 1), (2, 1), (0, 1)),
    "cyc2": ((2, 1), (0, 1), (1, 1)),
    "rev": ((0, -1), (2, -1), (1, -1)),
    "rev_cyc": ((1, -1), (0, -1), (2, -1)),
    "rev_cyc2": ((2, -1), (1, -1), (0, -1)),
}
INVERSE_ORIENTATION = {
    "id": "id",
    "cyc": "cyc2",
    "cyc2": "cyc",
    "rev": "rev",
    "rev_cyc": "rev_cyc",
    "rev_cyc2": "rev_cyc2",
}
IDENTITY_MASK = 0x8421
TERM_COUNT = 49
FACTOR_BITS = 16


def canonical_bytes(value: Any) -> bytes:
    return (json.dumps(value, sort_keys=True, indent=2, separators=(",", ": ")) + "\n").encode()


def digest_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def digest_json(value: Any) -> str:
    return digest_bytes(canonical_bytes(value))


def file_digest(path: Path) -> str:
    return digest_bytes(path.read_bytes())


def parse_source() -> tuple[list[tuple[int, int, int]], dict[str, Any]]:
    raw = SOURCE.read_bytes()
    actual_hash = digest_bytes(raw)
    if actual_hash != SOURCE_SHA256:
        raise RuntimeError(f"source SHA-256 mismatch: {actual_hash}")
    text = raw.decode("ascii")
    lines = text.splitlines()
    if len(lines) != 4 or lines[0].split() != ["4", "4", "4", "49"]:
        raise RuntimeError("unexpected source header or line count")
    factor_lists: list[list[int]] = []
    for leg, line in zip("UVW", lines[1:]):
        entries = [int(x) for x in line.split()]
        if len(entries) != TERM_COUNT * FACTOR_BITS or set(entries) - {0, 1}:
            raise RuntimeError(f"invalid {leg} factor row")
        factor_lists.append(
            [sum(entries[FACTOR_BITS * i + j] << j for j in range(FACTOR_BITS)) for i in range(TERM_COUNT)]
        )
    terms = list(zip(*factor_lists))
    if any(x == 0 for term in terms for x in term):
        raise RuntimeError("zero factor in source")
    distinct = [len(set(term[f] for term in terms)) for f in range(3)]
    if distinct != [49, 49, 49]:
        raise RuntimeError(f"factor lists are not pairwise distinct: {distinct}")
    summary = {
        "bytes": len(raw),
        "header": [4, 4, 4, 49],
        "factor_coordinate_encoding": "each 16-bit word is row-major: bit 4*i+j is matrix entry (i,j)",
        "factor_list_distinct_counts": distinct,
        "factor_list_nonzero_counts": [sum(term[f] != 0 for term in terms) for f in range(3)],
        "source_line_count": len(lines),
    }
    return terms, summary


def transpose_mask(value: int) -> int:
    return sum(((value >> (4 * i + j)) & 1) << (4 * j + i) for i in range(4) for j in range(4))


def orient_terms(terms: list[tuple[int, int, int]], orientation: str) -> list[tuple[int, int, int]]:
    output = []
    for u, v, w in terms:
        if orientation == "id":
            item = (u, v, w)
        elif orientation == "cyc":
            item = (v, w, u)
        elif orientation == "cyc2":
            item = (w, u, v)
        elif orientation == "rev":
            item = (transpose_mask(w), transpose_mask(v), transpose_mask(u))
        elif orientation == "rev_cyc":
            item = (transpose_mask(u), transpose_mask(w), transpose_mask(v))
        elif orientation == "rev_cyc2":
            item = (transpose_mask(v), transpose_mask(u), transpose_mask(w))
        else:
            raise ValueError(orientation)
        output.append(item)
    return output


def binary_vector_rank(values: list[int]) -> int:
    basis: dict[int, int] = {}
    for value in values:
        x = value
        while x:
            pivot = x.bit_length() - 1
            if pivot in basis:
                x ^= basis[pivot]
            else:
                basis[pivot] = x
                break
    return len(basis)


def matrix_rank(mask: int) -> int:
    return binary_vector_rank([(mask >> (4 * i)) & 15 for i in range(4)])


def three_circuits(terms: list[tuple[int, int, int]]) -> list[list[tuple[int, int, int]]]:
    return [
        [
            triple
            for triple in itertools.combinations(range(TERM_COUNT), 3)
            if terms[triple[0]][leg] ^ terms[triple[1]][leg] ^ terms[triple[2]][leg] == 0
        ]
        for leg in range(3)
    ]


def circuit_incidences(circuits: list[list[tuple[int, int, int]]]) -> list[list[list[tuple[int, int]]]]:
    incidence: list[list[list[tuple[int, int]]]] = [[[] for _ in range(TERM_COUNT)] for _ in range(3)]
    for leg in range(3):
        for triple in circuits[leg]:
            for i in triple:
                others = tuple(j for j in triple if j != i)
                incidence[leg][i].append(others)
    return incidence


def degree_counter(circuits: list[list[tuple[int, int, int]]]) -> collections.Counter[tuple[int, int, int]]:
    incidence = circuit_incidences(circuits)
    return collections.Counter(
        tuple(len(incidence[leg][i]) for leg in range(3)) for i in range(TERM_COUNT)
    )


def counter_records(counter: collections.Counter[tuple[int, ...]], key: str) -> list[dict[str, Any]]:
    return [{key: list(item), "count": counter[item]} for item in sorted(counter)]


def circuit_records(terms: list[tuple[int, int, int]]) -> tuple[dict[str, Any], dict[str, list[list[tuple[int, int, int]]]]]:
    raw: dict[str, list[list[tuple[int, int, int]]]] = {}
    for orientation in ORIENTATIONS:
        raw[orientation] = three_circuits(orient_terms(terms, orientation))
    target = raw["id"]
    target_counts = [len(x) for x in target]
    target_degrees = degree_counter(target)
    records = []
    for orientation in ORIENTATIONS:
        circuits = raw[orientation]
        counts = [len(x) for x in circuits]
        degrees = degree_counter(circuits)
        serialized = [[[a, b, c] for a, b, c in leg] for leg in circuits]
        record: dict[str, Any] = {
            "orientation": orientation,
            "physical_formula": ORIENTATION_FORMULAS[orientation],
            "circuits_by_output_leg": {name: triples for name, triples in zip("UVW", serialized)},
            "ordered_circuit_counts": counts,
            "circuit_transcript_sha256": digest_json(serialized),
            "vertex_incidence_degree_histogram": counter_records(degrees, "degree_triple"),
            "calculation_status": "computational",
        }
        if orientation == "id":
            record.update({"branch_status": "survives_invariant_filter", "deduction_status": "proved"})
        elif counts != target_counts:
            mismatch_leg = next(i for i in range(3) if counts[i] != target_counts[i])
            record.update(
                {
                    "branch_status": "proved_no_solution",
                    "deduction_status": "proved",
                    "rejection": {
                        "invariant": "ordered projective three-circuit counts",
                        "output_leg": "UVW"[mismatch_leg],
                        "oriented_count": counts[mismatch_leg],
                        "target_count": target_counts[mismatch_leg],
                    },
                }
            )
        else:
            mismatch = next(item for item in sorted(set(degrees) | set(target_degrees)) if degrees[item] != target_degrees[item])
            record.update(
                {
                    "branch_status": "proved_no_solution",
                    "deduction_status": "proved",
                    "rejection": {
                        "invariant": "multiset of output-leg three-circuit incidence degrees",
                        "degree_triple": list(mismatch),
                        "oriented_count": degrees[mismatch],
                        "target_count": target_degrees[mismatch],
                    },
                }
            )
        records.append(record)
    if target_counts != [29, 29, 27]:
        raise RuntimeError(f"unexpected circuit counts: {target_counts}")
    if [record["branch_status"] for record in records] != ["survives_invariant_filter"] + ["proved_no_solution"] * 5:
        raise RuntimeError("outer-orientation circuit coverage failed")
    certificate = {
        "status": "proved",
        "calculation_status": "computational",
        "scope": "all field extensions K/F2",
        "extension_stability_lemma": {
            "status": "proved",
            "statement": "For vectors with F2 coordinates, subset rank is unchanged after scalar extension K/F2. An invertible sandwich with nonzero term gauges is a projective linear isomorphism on each factor space, so it preserves each leg's projective circuits and their common term incidence.",
            "checked_hypotheses": {
                "all_factors_nonzero": True,
                "factor_vectors_pairwise_distinct_within_each_leg": True,
                "source_characteristic": 2,
            },
        },
        "target_ordered_circuit_counts": target_counts,
        "orientation_branches": records,
        "coverage": {"orientations_total": 6, "orientations_rejected": 5, "orientations_surviving": ["id"]},
    }
    return certificate, raw


def jsonify_tuple(value: Any) -> Any:
    if isinstance(value, tuple):
        return [jsonify_tuple(x) for x in value]
    if isinstance(value, list):
        return [jsonify_tuple(x) for x in value]
    return value


def canonicalize_signatures(signatures: list[tuple[Any, ...]]) -> tuple[list[int], list[tuple[Any, ...]]]:
    definitions = sorted(set(signatures))
    lookup = {signature: i for i, signature in enumerate(definitions)}
    return [lookup[signature] for signature in signatures], definitions


def refinement_certificate(
    terms: list[tuple[int, int, int]], circuits: list[list[tuple[int, int, int]]]
) -> dict[str, Any]:
    incidence = circuit_incidences(circuits)
    signatures: list[tuple[Any, ...]] = [
        (
            tuple(matrix_rank(x) for x in terms[i]),
            tuple(len(incidence[leg][i]) for leg in range(3)),
        )
        for i in range(TERM_COUNT)
    ]
    colors, definitions = canonicalize_signatures(signatures)
    levels = []
    for level in range(3):
        classes: dict[int, list[int]] = collections.defaultdict(list)
        for term, color in enumerate(colors):
            classes[color].append(term)
        class_histogram = collections.Counter(len(items) for items in classes.values())
        levels.append(
            {
                "level": level,
                "color_definition": (
                    "(ordered factor-rank triple, ordered circuit-incidence degree triple)"
                    if level == 0
                    else "(previous color, for each output leg the sorted multiset of unordered previous-color pairs on the other two circuit vertices)"
                ),
                "colors_by_zero_based_term": colors,
                "color_signatures": [
                    {"color": i, "signature": jsonify_tuple(signature)} for i, signature in enumerate(definitions)
                ],
                "classes": [{"color": color, "terms": classes[color]} for color in sorted(classes)],
                "distinct_colors": len(classes),
                "class_size_histogram": [
                    {"class_size": size, "number_of_classes": class_histogram[size]}
                    for size in sorted(class_histogram)
                ],
            }
        )
        if level == 2:
            break
        next_signatures = []
        for i in range(TERM_COUNT):
            per_leg = []
            for leg in range(3):
                pairs = [tuple(sorted((colors[j], colors[k]))) for j, k in incidence[leg][i]]
                per_leg.append(tuple(sorted(pairs)))
            next_signatures.append((colors[i], tuple(per_leg)))
        signatures = next_signatures
        colors, definitions = canonicalize_signatures(signatures)
    counts = [level["distinct_colors"] for level in levels]
    if counts != [16, 46, 49] or any(len(item["terms"]) != 1 for item in levels[-1]["classes"]):
        raise RuntimeError(f"unexpected identity refinement: {counts}")
    return {
        "status": "proved",
        "calculation_status": "computational",
        "orientation": "id",
        "refinement_invariance_lemma": {
            "status": "proved",
            "statement": "Every simultaneous automorphism of the three colored circuit hypergraphs preserves level 0 and, inductively, every refinement level. A discrete final coloring fixes every term.",
        },
        "levels": levels,
        "distinct_color_counts": counts,
        "coverage": {
            "all_49_terms_have_unique_final_colors": True,
            "only_compatible_permutation": list(range(TERM_COUNT)),
            "compatible_permutation_count": 1,
        },
        "conclusion": "Every identity-orientation stabilizer field point over every K/F2 has pi=id.",
    }


def rank_one_vectors(mask: int) -> tuple[int, int]:
    if matrix_rank(mask) != 1:
        raise RuntimeError("frame factor is not rank one")
    columns = [sum(((mask >> (4 * i + j)) & 1) << i for i in range(4)) for j in range(4)]
    column = next(value for value in columns if value)
    if any(value not in (0, column) for value in columns):
        raise RuntimeError("invalid rank-one factorization")
    row = sum(1 << j for j, value in enumerate(columns) if value == column)
    expected = sum(((column >> i) & 1) * ((row >> j) & 1) << (4 * i + j) for i in range(4) for j in range(4))
    if expected != mask:
        raise RuntimeError("rank-one reconstruction failed")
    return column, row


def basis_coordinates(vector: int, basis: list[int]) -> int:
    answers = []
    for coefficient_mask in range(16):
        value = 0
        for i, item in enumerate(basis):
            if (coefficient_mask >> i) & 1:
                value ^= item
        if value == vector:
            answers.append(coefficient_mask)
    if len(answers) != 1:
        raise RuntimeError("frame is not a basis")
    return answers[0]


def one_frame(
    terms: list[tuple[int, int, int]],
    factor: int,
    side: int,
    basis_terms: list[int],
    link_terms: list[int],
    matrix_forced: str,
) -> dict[str, Any]:
    selected = sorted(set(basis_terms + link_terms))
    vectors = {}
    factorizations = {}
    for term in selected:
        column, row = rank_one_vectors(terms[term][factor])
        vectors[term] = (column, row)[side]
        factorizations[term] = {
            "term0": term,
            "factor_matrix_hex": f"{terms[term][factor]:04x}",
            "column_vector_hex": f"{column:x}",
            "row_vector_hex": f"{row:x}",
        }
    basis = [vectors[term] for term in basis_terms]
    if binary_vector_rank(basis) != 4:
        raise RuntimeError("declared projective frame basis is singular")
    parent = list(range(4))

    def root(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    link_records = []
    graph_edges = set()
    for term in link_terms:
        coordinates = basis_coordinates(vectors[term], basis)
        support = [i for i in range(4) if (coordinates >> i) & 1]
        if len(support) < 2:
            raise RuntimeError("link vector does not connect basis eigenvalues")
        for endpoint in support[1:]:
            edge = tuple(sorted((support[0], endpoint)))
            graph_edges.add(edge)
            a, b = root(edge[0]), root(edge[1])
            if a != b:
                parent[b] = a
        reconstructed = 0
        for i in support:
            reconstructed ^= basis[i]
        if reconstructed != vectors[term]:
            raise RuntimeError("link coordinate reconstruction failed")
        link_records.append(
            {
                "term0": term,
                "vector_hex": f"{vectors[term]:x}",
                "basis_coordinates_hex": f"{coordinates:x}",
                "coordinate_support": support,
                "xor_reconstruction_hex": f"{reconstructed:x}",
            }
        )
    connected = len({root(i) for i in range(4)}) == 1
    if not connected:
        raise RuntimeError("projective frame support graph is disconnected")
    operator = {"P": "P", "Q": "Q^(-T)", "R": "R^(-T)"}[matrix_forced]
    return {
        "status": "proved",
        "factor": "UVW"[factor],
        "projective_side": ("column", "row")[side],
        "operator_fixing_lines": operator,
        "matrix_forced_scalar": matrix_forced,
        "rank_one_factorizations": [factorizations[term] for term in selected],
        "basis": [
            {"term0": term, "vector_hex": f"{vectors[term]:x}"} for term in basis_terms
        ],
        "basis_rank_over_F2": 4,
        "links": link_records,
        "support_graph_edges": [list(edge) for edge in sorted(graph_edges)],
        "support_graph_connected": connected,
        "deduction": f"Over every K/F2, a linear automorphism fixing these basis lines is diagonal in this basis; each link equates the diagonal entries on its support, and connectedness forces {matrix_forced} to be scalar.",
    }


def frame_certificate(terms: list[tuple[int, int, int]]) -> dict[str, Any]:
    frames = [
        one_frame(terms, 0, 0, [1, 3, 4, 8], [6, 12, 16], "P"),
        one_frame(terms, 0, 1, [1, 3, 6, 9], [10, 12, 15], "Q"),
        one_frame(terms, 1, 1, [1, 3, 4, 8], [12, 13, 16], "R"),
    ]
    return {
        "status": "proved",
        "calculation_status": "computational",
        "scope": "all field extensions K/F2 after orientation=id and pi=id",
        "projective_frame_lemma": {
            "status": "proved",
            "statement": "If an invertible linear map fixes four basis lines, it is diagonal in that basis. Fixing additional lines equates diagonal entries on each coordinate support; a connected support graph forces a scalar map.",
        },
        "frames": frames,
        "conclusion": "The stabilizer equations force P=pI4, Q=qI4, R=rI4 with p,q,r nonzero.",
    }


def edge_color(a: tuple[int, int, int], b: tuple[int, int, int]) -> tuple[int, int, int]:
    return tuple(matrix_rank(a[i] ^ b[i]) for i in range(3))


def edge_counter(terms: list[tuple[int, int, int]]) -> collections.Counter[tuple[int, int, int]]:
    return collections.Counter(
        edge_color(terms[i], terms[j]) for i in range(TERM_COUNT) for j in range(i + 1, TERM_COUNT)
    )


def rooted_pair_profile(terms: list[tuple[int, int, int]], term: int) -> tuple[Any, ...]:
    counter = collections.Counter(edge_color(terms[term], terms[j]) for j in range(TERM_COUNT) if j != term)
    return tuple(matrix_rank(x) for x in terms[term]), tuple(sorted(counter.items()))


def sandwich_equation_rows(source: tuple[int, int, int], target: tuple[int, int, int]) -> list[int]:
    u, v, w = source
    up, vp, wp = target
    rows = []
    for i in range(4):
        for j in range(4):
            row = 0
            for k in range(4):
                if (u >> (4 * k + j)) & 1:
                    row ^= 1 << (4 * i + k)
                if (up >> (4 * i + k)) & 1:
                    row ^= 1 << (16 + 4 * k + j)
            if row:
                rows.append(row)
    for i in range(4):
        for j in range(4):
            row = 0
            for k in range(4):
                if (v >> (4 * k + j)) & 1:
                    row ^= 1 << (16 + 4 * i + k)
                if (vp >> (4 * i + k)) & 1:
                    row ^= 1 << (32 + 4 * k + j)
            if row:
                rows.append(row)
    for i in range(4):
        for j in range(4):
            row = 0
            for k in range(4):
                if (w >> (4 * k + j)) & 1:
                    row ^= 1 << (32 + 4 * i + k)
                if (wp >> (4 * i + k)) & 1:
                    row ^= 1 << (4 * k + j)
            if row:
                rows.append(row)
    return rows


def binary_rref(rows: list[int], columns: int) -> tuple[list[int], list[int]]:
    matrix = [row for row in rows if row]
    rank = 0
    pivots = []
    for column in range(columns):
        pivot_row = next((i for i in range(rank, len(matrix)) if (matrix[i] >> column) & 1), None)
        if pivot_row is None:
            continue
        matrix[rank], matrix[pivot_row] = matrix[pivot_row], matrix[rank]
        pivot_value = matrix[rank]
        for i in range(len(matrix)):
            if i != rank and ((matrix[i] >> column) & 1):
                matrix[i] ^= pivot_value
        pivots.append(column)
        rank += 1
        if rank == len(matrix):
            break
    nonzero = matrix[:rank]
    if any(matrix[i] for i in range(rank, len(matrix))):
        raise RuntimeError("RREF rank bookkeeping failure")
    return nonzero, pivots


def rref_nullspace(rref: list[int], pivots: list[int], columns: int) -> list[int]:
    pivot_set = set(pivots)
    output = []
    for free in range(columns):
        if free in pivot_set:
            continue
        value = 1 << free
        for row, pivot in zip(rref, pivots):
            if (row & value).bit_count() & 1:
                value ^= 1 << pivot
        output.append(value)
    return output


def binary_crosscheck(terms: list[tuple[int, int, int]]) -> dict[str, Any]:
    target_counter = edge_counter(terms)
    orientations = []
    for orientation in ORIENTATIONS:
        counter = edge_counter(orient_terms(terms, orientation))
        differences = [
            {
                "color": list(color),
                "oriented_count": counter[color],
                "target_count": target_counter[color],
            }
            for color in sorted(set(counter) | set(target_counter))
            if counter[color] != target_counter[color]
        ]
        orientations.append(
            {
                "orientation": orientation,
                "counter": counter_records(counter, "pair_sum_rank_triple"),
                "matches_target": not differences,
                "first_mismatch": differences[0] if differences else None,
            }
        )
    if not orientations[0]["matches_target"] or any(record["matches_target"] for record in orientations[1:]):
        raise RuntimeError("unexpected F2 pair-rank orientation result")
    blocks_by_profile: dict[Any, list[int]] = collections.defaultdict(list)
    for term in range(TERM_COUNT):
        blocks_by_profile[rooted_pair_profile(terms, term)].append(term)
    blocks = sorted(blocks_by_profile.values(), key=lambda block: block[0])
    candidate_count = math.prod(math.factorial(len(block)) for block in blocks)
    candidates = []
    automorphisms = []
    for choices in itertools.product(*(itertools.permutations(block) for block in blocks)):
        permutation = list(range(TERM_COUNT))
        for block, image in zip(blocks, choices):
            for source, target in zip(block, image):
                permutation[source] = target
        preserves = all(
            edge_color(terms[i], terms[j]) == edge_color(terms[permutation[i]], terms[permutation[j]])
            for i in range(TERM_COUNT)
            for j in range(i + 1, TERM_COUNT)
        )
        candidates.append({"permutation": permutation, "preserves_all_colored_edges": preserves})
        if preserves:
            automorphisms.append(permutation)
    if candidate_count != 16 or automorphisms != [list(range(TERM_COUNT))]:
        raise RuntimeError("unexpected F2 colored-pair graph automorphism coverage")
    equation_rows = []
    for term in terms:
        equation_rows.extend(sandwich_equation_rows(term, term))
    rref, pivots = binary_rref(equation_rows, 48)
    nullspace = rref_nullspace(rref, pivots, 48)
    expected = IDENTITY_MASK | (IDENTITY_MASK << 16) | (IDENTITY_MASK << 32)
    if len(rref) != 47 or nullspace != [expected]:
        raise RuntimeError("unexpected F2 sandwich nullspace")
    return {
        "status": "computational",
        "scope": "F2 only; pair-sum ranks are not asserted gauge-invariant over extensions with nontrivial units",
        "orientation_pair_sum_rank_counters": orientations,
        "identity_colored_pair_graph": {
            "rooted_profile_blocks": blocks,
            "nontrivial_blocks": [block for block in blocks if len(block) > 1],
            "candidate_count": candidate_count,
            "candidate_coverage": candidates,
            "automorphisms": automorphisms,
        },
        "identity_sandwich_linear_system": {
            "equations": ["P*U_l=U_l*Q", "Q*V_l=V_l*R", "R*W_l=W_l*P"],
            "variable_encoding": "48 bits: row-major P entries, then Q, then R",
            "generated_nonzero_rows": len(equation_rows),
            "rank": len(rref),
            "nullity": len(nullspace),
            "pivot_columns": pivots,
            "rref_rows_hex": [f"{row:012x}" for row in rref],
            "rref_sha256": digest_json([f"{row:012x}" for row in rref]),
            "nullspace_basis_hex": [f"{value:012x}" for value in nullspace],
            "only_invertible_solution": {"P_hex": "8421", "Q_hex": "8421", "R_hex": "8421"},
        },
    }


def binary_matrix_multiply(a: int, b: int) -> int:
    output = 0
    for i in range(4):
        for j in range(4):
            bit = 0
            for k in range(4):
                bit ^= ((a >> (4 * i + k)) & 1) & ((b >> (4 * k + j)) & 1)
            output |= bit << (4 * i + j)
    return output


def packed_variation(blocks: list[list[int]]) -> int:
    return sum(
        value << (FACTOR_BITS * (leg * TERM_COUNT + term))
        for leg in range(3)
        for term, value in enumerate(blocks[leg])
    )


def tangent_generators(terms: list[tuple[int, int, int]]) -> list[int]:
    generators = []
    for term, (u, v, w) in enumerate(terms):
        blocks = [[0] * TERM_COUNT for _ in range(3)]
        blocks[0][term], blocks[1][term] = u, v
        generators.append(packed_variation(blocks))
        blocks = [[0] * TERM_COUNT for _ in range(3)]
        blocks[0][term], blocks[2][term] = u, w
        generators.append(packed_variation(blocks))
    for kind in range(3):
        for i in range(4):
            for j in range(4):
                elementary = 1 << (4 * i + j)
                blocks = [[0] * TERM_COUNT for _ in range(3)]
                if kind == 0:
                    blocks[0] = [binary_matrix_multiply(elementary, term[0]) for term in terms]
                    blocks[2] = [binary_matrix_multiply(term[2], elementary) for term in terms]
                elif kind == 1:
                    blocks[0] = [binary_matrix_multiply(term[0], elementary) for term in terms]
                    blocks[1] = [binary_matrix_multiply(elementary, term[1]) for term in terms]
                else:
                    blocks[1] = [binary_matrix_multiply(term[1], elementary) for term in terms]
                    blocks[2] = [binary_matrix_multiply(elementary, term[2]) for term in terms]
                generators.append(packed_variation(blocks))
    if len(generators) != 146:
        raise RuntimeError("unexpected tangent parameter count")
    return generators


def tangent_kernel(generators: list[int]) -> tuple[dict[int, tuple[int, int]], list[int]]:
    basis: dict[int, tuple[int, int]] = {}
    relations = []
    for column, value in enumerate(generators):
        output = value
        parameters = 1 << column
        while output:
            pivot = output.bit_length() - 1
            if pivot in basis:
                output ^= basis[pivot][0]
                parameters ^= basis[pivot][1]
            else:
                basis[pivot] = (output, parameters)
                break
        if not output:
            relations.append(parameters)
    return basis, relations


def expected_torus_tangent_relations() -> tuple[list[int], list[dict[str, Any]]]:
    values = []
    semantic = []
    for name, (a, b, c) in zip(("p_scalar", "q_scalar", "r_scalar"), ((1, 0, 0), (0, 1, 0), (0, 0, 1))):
        value = 0
        first_gauge_terms = []
        second_gauge_terms = []
        for term in range(TERM_COUNT):
            if b ^ c:
                value |= 1 << (2 * term)
                first_gauge_terms.append(term)
            if c ^ a:
                value |= 1 << (2 * term + 1)
                second_gauge_terms.append(term)
        sandwich_entries = []
        for kind, coefficient in enumerate((a, b, c)):
            if coefficient:
                for i in range(4):
                    parameter = 98 + 16 * kind + 4 * i + i
                    value |= 1 << parameter
                    sandwich_entries.append(parameter)
        values.append(value)
        semantic.append(
            {
                "name": name,
                "uniform_UV_gauge_terms": first_gauge_terms,
                "uniform_UW_gauge_terms": second_gauge_terms,
                "scalar_sandwich_parameter_indices": sandwich_entries,
            }
        )
    return values, semantic


def tangent_certificate(terms: list[tuple[int, int, int]]) -> dict[str, Any]:
    generators = tangent_generators(terms)
    basis, relations = tangent_kernel(generators)
    expected, semantic = expected_torus_tangent_relations()
    for relation in relations + expected:
        image = 0
        for i, generator in enumerate(generators):
            if (relation >> i) & 1:
                image ^= generator
        if image:
            raise RuntimeError("reported tangent relation has nonzero image")
    if len(basis) != 143 or relations != expected:
        raise RuntimeError("tangent kernel is not the expected split-torus tangent")
    basis_digest_input = [
        [pivot, f"{value:x}", f"{parameters:037x}"]
        for pivot, (value, parameters) in sorted(basis.items(), reverse=True)
    ]
    return {
        "status": "computational",
        "identification_status": "proved",
        "coefficient_field": "F2",
        "output_space": {"factor_coordinates": 3 * TERM_COUNT * FACTOR_BITS, "bit_encoding": "U terms, then V terms, then W terms; 16 row-major bits per term"},
        "parameter_space": {
            "dimension": 146,
            "indices_0_through_97": "for term l: 2*l is (U_l,V_l,0), 2*l+1 is (U_l,0,W_l)",
            "indices_98_through_145": "row-major infinitesimal P, then Q, then R",
        },
        "rank": len(basis),
        "kernel_dimension": len(relations),
        "kernel_basis_hex": [f"{relation:037x}" for relation in relations],
        "kernel_basis_semantics": semantic,
        "kernel_equals_Lie_Cx": True,
        "elimination_pivot_output_coordinates": sorted(basis, reverse=True),
        "elimination_basis_sha256": digest_json(basis_digest_input),
        "deduction": "The connected action differential has rank 143 and its entire three-dimensional kernel is the infinitesimal scalar-sandwich/compensating-gauge torus.",
    }


FIELD_SPECS = {
    "F2": {"degree": 1, "modulus": 0b11, "size": 2, "labels": ["0", "1"]},
    "F4": {"degree": 2, "modulus": 0b111, "size": 4, "labels": ["0", "1", "a", "a+1"]},
}


def field_multiply(field: str, a: int, b: int) -> int:
    spec = FIELD_SPECS[field]
    product = 0
    x, y = a, b
    while y:
        if y & 1:
            product ^= x
        y >>= 1
        x <<= 1
    degree = spec["degree"]
    modulus = spec["modulus"]
    for power in range(2 * degree - 2, degree - 1, -1):
        if (product >> power) & 1:
            product ^= modulus << (power - degree)
    if not 0 <= product < spec["size"]:
        raise RuntimeError("finite-field reduction failed")
    return product


def field_power(field: str, value: int, exponent: int) -> int:
    output = 1
    base = value
    while exponent:
        if exponent & 1:
            output = field_multiply(field, output, base)
        base = field_multiply(field, base, base)
        exponent >>= 1
    return output


def field_inverse(field: str, value: int) -> int:
    if value == 0:
        raise ZeroDivisionError
    return field_power(field, value, FIELD_SPECS[field]["size"] - 2)


def field_matrix_from_mask(mask: int) -> list[int]:
    return [(mask >> i) & 1 for i in range(16)]


def field_matrix_multiply(field: str, a: list[int], b: list[int]) -> list[int]:
    output = [0] * 16
    for i in range(4):
        for j in range(4):
            value = 0
            for k in range(4):
                value ^= field_multiply(field, a[4 * i + k], b[4 * k + j])
            output[4 * i + j] = value
    return output


def field_matrix_scale(field: str, scalar: int, matrix: list[int]) -> list[int]:
    return [field_multiply(field, scalar, value) for value in matrix]


def scalar_identity(scalar: int) -> list[int]:
    return [scalar if i == j else 0 for i in range(4) for j in range(4)]


def matrix_word(matrix: list[int]) -> str:
    return "".join(format(value, "x") for value in matrix)


def matrix_record(matrix: list[int]) -> dict[str, Any]:
    return {"entries_row_major": matrix, "word": matrix_word(matrix)}


def finite_field_record(field: str) -> dict[str, Any]:
    spec = FIELD_SPECS[field]
    return {
        "name": field,
        "size": spec["size"],
        "element_encoding": {str(i): label for i, label in enumerate(spec["labels"])},
        "addition": "bitwise XOR in the polynomial basis",
        "multiplication_modulus_bits": format(spec["modulus"], "b"),
        "modulus_polynomial": "x+1" if field == "F2" else "x^2+x+1",
    }


def point_witness(terms: list[tuple[int, int, int]], field: str, p: int, q: int, r: int) -> dict[str, Any]:
    values = (p, q, r)
    if any(value == 0 for value in values):
        raise RuntimeError("torus coordinate is zero")
    p_inv, q_inv, r_inv = (field_inverse(field, value) for value in values)
    alpha = field_multiply(field, p, q_inv)
    beta = field_multiply(field, q, r_inv)
    gamma = field_multiply(field, r, p_inv)
    if field_multiply(field, field_multiply(field, alpha, beta), gamma) != 1:
        raise RuntimeError("equation-side gauge product is not one")
    replay = (field_inverse(field, alpha), field_inverse(field, beta), field_inverse(field, gamma))
    if field_multiply(field, field_multiply(field, replay[0], replay[1]), replay[2]) != 1:
        raise RuntimeError("replay-side gauge product is not one")
    matrices = [scalar_identity(value) for value in values]
    inverses = [scalar_identity(value) for value in (p_inv, q_inv, r_inv)]
    identity = scalar_identity(1)
    inverse_checks = []
    for name, matrix, inverse in zip("PQR", matrices, inverses):
        left = field_matrix_multiply(field, matrix, inverse)
        right = field_matrix_multiply(field, inverse, matrix)
        if left != identity or right != identity:
            raise RuntimeError("matrix inverse replay failed")
        inverse_checks.append({"matrix": name, "left_product": matrix_word(left), "right_product": matrix_word(right), "holds": True})
    equation_records = []
    replayed_terms = []
    for term, masks in enumerate(terms):
        source = [field_matrix_from_mask(mask) for mask in masks]
        lhs = [
            field_matrix_multiply(field, field_matrix_multiply(field, matrices[0], source[0]), inverses[1]),
            field_matrix_multiply(field, field_matrix_multiply(field, matrices[1], source[1]), inverses[2]),
            field_matrix_multiply(field, field_matrix_multiply(field, matrices[2], source[2]), inverses[0]),
        ]
        scalars = (alpha, beta, gamma)
        after_replay = []
        for leg in range(3):
            rhs = field_matrix_scale(field, scalars[leg], source[leg])
            replayed = field_matrix_scale(field, replay[leg], lhs[leg])
            if lhs[leg] != rhs or replayed != source[leg]:
                raise RuntimeError("split-torus factor equation or replay failed")
            equation_records.append(
                {
                    "zero_based_term": term,
                    "output_leg": "UVW"[leg],
                    "lhs_word": matrix_word(lhs[leg]),
                    "equation_scalar": scalars[leg],
                    "rhs_word": matrix_word(rhs),
                    "equation_holds": True,
                    "replay_multiplier": replay[leg],
                    "after_replay_word": matrix_word(replayed),
                    "target_word": matrix_word(source[leg]),
                    "replay_holds": True,
                }
            )
            after_replay.append(matrix_word(replayed))
        replayed_terms.append(after_replay)
    if len(equation_records) != 147:
        raise RuntimeError("incomplete mapped-factor equation transcript")
    labels = FIELD_SPECS[field]["labels"]
    witness = {
        "witness_id": f"{field}:p={p},q={q},r={r}",
        "field": field,
        "orientation": "id",
        "term_permutation_zero_based": list(range(TERM_COUNT)),
        "torus_coordinates": {
            "encoded": {"p": p, "q": q, "r": r},
            "labels": {"p": labels[p], "q": labels[q], "r": labels[r]},
        },
        "matrices": {name: matrix_record(matrix) for name, matrix in zip("PQR", matrices)},
        "matrix_inverses": {name + "inv": matrix_record(matrix) for name, matrix in zip("PQR", inverses)},
        "inverse_checks": inverse_checks,
        "equation_side_uniform_gauge": [alpha, beta, gamma],
        "equation_side_term_gauges": [[alpha, beta, gamma] for _ in range(TERM_COUNT)],
        "replay_side_uniform_compensating_gauge": list(replay),
        "replay_side_term_gauges": [list(replay) for _ in range(TERM_COUNT)],
        "mapped_factor_equations": equation_records,
        "mapped_factor_equation_count": len(equation_records),
        "mapped_factor_equations_sha256": digest_json(equation_records),
        "full_replay_holds": True,
        "replayed_decomposition_sha256": digest_json(replayed_terms),
    }
    return witness


def field_matrix_transpose(matrix: list[int]) -> list[int]:
    return [matrix[4 * j + i] for i in range(4) for j in range(4)]


def orient_field_triple(triple: list[list[int]], orientation: str) -> list[list[int]]:
    u, v, w = triple
    if orientation == "id":
        return [u, v, w]
    if orientation == "cyc":
        return [v, w, u]
    if orientation == "cyc2":
        return [w, u, v]
    if orientation == "rev":
        return [field_matrix_transpose(w), field_matrix_transpose(v), field_matrix_transpose(u)]
    if orientation == "rev_cyc":
        return [field_matrix_transpose(u), field_matrix_transpose(w), field_matrix_transpose(v)]
    if orientation == "rev_cyc2":
        return [field_matrix_transpose(v), field_matrix_transpose(u), field_matrix_transpose(w)]
    raise RuntimeError(f"unknown orientation {orientation}")


def orient_scalar_triple(triple: tuple[int, int, int], orientation: str) -> tuple[int, int, int]:
    u, v, w = triple
    if orientation == "id":
        return u, v, w
    if orientation == "cyc":
        return v, w, u
    if orientation == "cyc2":
        return w, u, v
    if orientation == "rev":
        return w, v, u
    if orientation == "rev_cyc":
        return u, w, v
    if orientation == "rev_cyc2":
        return v, u, w
    raise RuntimeError(f"unknown orientation {orientation}")


def apply_outer_monomial(field: str, orientation: str, coordinates: tuple[int, int, int]) -> tuple[int, int, int]:
    output = []
    for source, exponent in OUTER_TORUS_MONOMIAL_ACTION[orientation]:
        value = coordinates[source]
        output.append(value if exponent == 1 else field_inverse(field, value))
    return tuple(output)


def sandwich_scalar_factors(field: str, triple: list[list[int]], coordinates: tuple[int, int, int]) -> list[list[int]]:
    p, q, r = coordinates
    scales = (
        field_multiply(field, p, field_inverse(field, q)),
        field_multiply(field, q, field_inverse(field, r)),
        field_multiply(field, r, field_inverse(field, p)),
    )
    return [field_matrix_scale(field, scale, matrix) for scale, matrix in zip(scales, triple)]


def replay_gauges(field: str, coordinates: tuple[int, int, int]) -> tuple[int, int, int]:
    p, q, r = coordinates
    return (
        field_multiply(field, q, field_inverse(field, p)),
        field_multiply(field, r, field_inverse(field, q)),
        field_multiply(field, p, field_inverse(field, r)),
    )


def outer_action_certificate(terms: list[tuple[int, int, int]]) -> dict[str, Any]:
    actions = []
    nonzero = range(1, FIELD_SPECS["F4"]["size"])
    for orientation in ORIENTATIONS:
        transcript = []
        equation_count = 0
        for coordinates in itertools.product(nonzero, repeat=3):
            transformed = apply_outer_monomial("F4", orientation, coordinates)
            original_gauges = replay_gauges("F4", coordinates)
            transported_gauges = orient_scalar_triple(original_gauges, orientation)
            transformed_gauges = replay_gauges("F4", transformed)
            if transported_gauges != transformed_gauges:
                raise RuntimeError(f"outer gauge transport failed for {orientation}")
            for masks in terms:
                source = [field_matrix_from_mask(mask) for mask in masks]
                preoriented = orient_field_triple(source, INVERSE_ORIENTATION[orientation])
                left = orient_field_triple(sandwich_scalar_factors("F4", preoriented, coordinates), orientation)
                right = sandwich_scalar_factors("F4", source, transformed)
                if left != right:
                    raise RuntimeError(f"outer sandwich conjugation failed for {orientation}")
                equation_count += 3
            transcript.append(
                {
                    "input_coordinates": list(coordinates),
                    "output_coordinates": list(transformed),
                    "input_replay_gauges": list(original_gauges),
                    "transported_replay_gauges": list(transported_gauges),
                    "output_replay_gauges": list(transformed_gauges),
                    "sandwich_conjugation_holds_for_all_49_terms": True,
                }
            )
        if equation_count != 27 * 49 * 3:
            raise RuntimeError("outer conjugation coverage is incomplete")
        exponent_matrix = [[0, 0, 0] for _ in range(3)]
        for row, (source, exponent) in enumerate(OUTER_TORUS_MONOMIAL_ACTION[orientation]):
            exponent_matrix[row][source] = exponent
        actions.append(
            {
                "orientation": orientation,
                "physical_formula": ORIENTATION_FORMULAS[orientation],
                "inverse_orientation": INVERSE_ORIENTATION[orientation],
                "coordinate_formula": OUTER_TORUS_COORDINATE_LABELS[orientation],
                "exponent_matrix_rows": exponent_matrix,
                "contains_coordinate_inversion": any(exponent == -1 for _, exponent in OUTER_TORUS_MONOMIAL_ACTION[orientation]),
                "replay_gauge_slot_formula": ORIENTATION_FORMULAS[orientation].replace("U", "gU").replace("V", "gV").replace("W", "gW").replace("T(", "").replace(")", ""),
                "F4_nonzero_input_count": len(transcript),
                "mapped_factor_conjugation_equation_count": equation_count,
                "F4_replay_table": transcript,
                "F4_replay_table_sha256": digest_json(transcript),
                "status": "computational",
            }
        )
    return {
        "status": "proved",
        "computation_status": "computational",
        "conjugation_convention": "sigma S(P,Q,R) sigma^(-1), where S sends (U,V,W) to (P U Q^(-1), Q V R^(-1), R W P^(-1))",
        "actions": actions,
        "reflection_correction": "Every reflection both permutes and inverts the Cx coordinates because transpose reverses the sandwich products.",
        "fixed_subgroup_schemes": {
            "id": {"status": "proved", "equalizer_ideal": "(0)", "isomorphism_type": "G_m^3"},
            "cyc": {"status": "proved", "equalizer_ideal": "(p-q,q-r)", "isomorphism_type": "diagonal G_m"},
            "cyc2": {"status": "proved", "equalizer_ideal": "(p-q,q-r)", "isomorphism_type": "diagonal G_m"},
            "rev": {"status": "proved", "equalizer_ideal": "(p^2-1,q*r-1)", "isomorphism_type": "mu_2 x G_m", "coordinates": "p in mu_2, r=q^(-1)"},
            "rev_cyc": {"status": "proved", "equalizer_ideal": "(p*q-1,r^2-1)", "isomorphism_type": "G_m x mu_2", "coordinates": "q=p^(-1), r in mu_2"},
            "rev_cyc2": {"status": "proved", "equalizer_ideal": "(p*r-1,q^2-1)", "isomorphism_type": "G_m x mu_2", "coordinates": "r=p^(-1), q in mu_2"},
        },
        "subgroup_fixed_by_all_six_outer_actions": {
            "status": "proved",
            "equalizer_ideal_in_F2[p+-1,q+-1,r+-1]": "(p-q,q-r,p^2-1)",
            "isomorphism_type": "diagonal mu_2",
            "functor_of_points": "{(t,t,t): t is a unit and t^2=1}",
            "geometric_points_in_characteristic_two": 1,
            "nonreduced_warning": "mu_2 over F2 is nonreduced and can have nonidentity points over nonreduced F2-algebras.",
        },
        "central_subgroup_correction": {
            "status": "proved",
            "false_sentence": "the diagonal G_m in Cx is central",
            "correction": "The diagonal G_m is normalized and fixed by the rotations, but every reflection acts on it by t -> t^(-1). Its pointwise-fixed, hence outer-central, subgroup scheme is diagonal mu_2, not diagonal G_m.",
            "scope": "centrality of Cx elements against the six outer monomial actions; scalar sandwiches and uniform gauges commute with the connected and term-permutation factors under the explicitly declared witness functor",
        },
    }


def orbit_counts() -> list[dict[str, int]]:
    return [
        {"support_size": size, "number_of_orbits": math.comb(TERM_COUNT, size), "orbit_size": 1}
        for size in range(TERM_COUNT + 1)
    ]


def point_certificates(terms: list[tuple[int, int, int]]) -> dict[str, Any]:
    f2_witnesses = [point_witness(terms, "F2", 1, 1, 1)]
    f4_witnesses = [
        point_witness(terms, "F4", p, q, r)
        for p in range(1, 4)
        for q in range(1, 4)
        for r in range(1, 4)
    ]
    if len(f4_witnesses) != 27 or len({record["witness_id"] for record in f4_witnesses}) != 27:
        raise RuntimeError("F4 torus enumeration is incomplete")
    if len({record["replayed_decomposition_sha256"] for record in f4_witnesses}) != 1:
        raise RuntimeError("split-torus witnesses do not have one direct action image")
    term_orbits = [[i] for i in range(TERM_COUNT)]
    common = {
        "term_orbits": term_orbits,
        "support_action": "identity on every subset of {0,...,48}",
        "support_orbit_counts_by_size": orbit_counts(),
        "five_support_orbit_count": math.comb(49, 5),
        "five_support_orbit_size": 1,
    }
    return {
        "status": "proved",
        "computation_status": "computational",
        "split_torus_symbolic_witness": {
            "status": "proved",
            "field_scope": "every field K/F2",
            "orientation": "id",
            "permutation": "pi(l)=l for l=0,...,48",
            "matrices": {"P": "p*I4", "Pinv": "p^(-1)*I4", "Q": "q*I4", "Qinv": "q^(-1)*I4", "R": "r*I4", "Rinv": "r^(-1)*I4"},
            "hypotheses": ["p,q,r are nonzero"],
            "equation_side_gauges": ["p/q", "q/r", "r/p"],
            "replay_side_compensating_gauges": ["q/p", "r/q", "p/r"],
            "mapped_factor_equations": [
                "(pI) U_l (q^(-1)I) = (p/q) U_l",
                "(qI) V_l (r^(-1)I) = (q/r) V_l",
                "(rI) W_l (p^(-1)I) = (r/p) W_l",
            ],
            "replay_statement": "Multiplying the three sandwiched factors by q/p, r/q, p/r respectively returns every raw factor exactly.",
        },
        "F2": {
            "status": "proved",
            "field": finite_field_record("F2"),
            "complete_witness_point_count": 1,
            "Cx_point_count": 1,
            "direct_effective_point_image_order": 1,
            "quotient_scheme_K_points": {"status": "unknown", "value": None, "reason": "No quotient representability/surjectivity/descent certificate is used."},
            "witnesses": f2_witnesses,
            "orbits_under_direct_effective_point_image": common,
        },
        "F4": {
            "status": "proved",
            "field": finite_field_record("F4"),
            "complete_witness_point_count": 27,
            "point_count_formula": "|Cx(F4)|=(4-1)^3=27",
            "Cx_point_count": 27,
            "direct_effective_point_image_order": 1,
            "point_count_distinction": "The witness point group has 27 points, while its directly computed effective action image has one element.",
            "quotient_scheme_K_points": {"status": "unknown", "value": None, "reason": "No identification with Stab_wit,x(F4)/Cx(F4) and no descent claim is made."},
            "witnesses": f4_witnesses,
            "orbits_under_direct_effective_point_image": common,
        },
        "geometric_field_points": {
            "status": "proved",
            "statement": "For every field extension K/F2, including an algebraic closure, Stab_wit,x(K)=Cx(K) and the direct effective point image is trivial.",
            "basis": "all outer orientations are rejected by extension-stable circuits; identity refinement forces pi=id; projective frames force scalar P,Q,R; nonzero factors determine the uniform gauges",
            "does_not_assert": "an equality of group schemes or any formula for K-points of a quotient group scheme",
        },
    }


def scheme_boundary() -> dict[str, Any]:
    return {
        "finite_type_witness_group_scheme_functor": {
            "status": "paper-level-unformalized",
            "base": "k=F2",
            "definition": "H_wit=(GL4^3 x D) semidirect Gamma, with D={(g_l^U,g_l^V,g_l^W) in G_m^147: g_l^U*g_l^V*g_l^W=1 for every l} isomorphic to (G_m^2)^49, and Gamma the constant finite k-group scheme S49 x S3.",
            "arbitrary_algebra_points": "For a commutative k-algebra A, Gamma(A) means locally constant choices on the idempotent components of Spec(A), not merely one abstract permutation when A is disconnected. On each component an A-point is (P,Q,R) in GL4(A)^3, 147 unit gauges with per-term product one, a term permutation, and one physical orientation.",
            "action_order": [
                "apply the selected physical orientation to every raw factor triple",
                "apply the sandwich (U,V,W) -> (P U Q^(-1), Q V R^(-1), R W P^(-1))",
                "apply replay-side gauges (g_l^U,g_l^V,g_l^W)",
                "relabel the 49 summands by the selected term permutation",
            ],
            "group_law": "composition of these natural transformations of the presentation functor",
            "outer_action_on_sandwich_coordinates": {
                "id": "(P,Q,R)",
                "cyc": "(Q,R,P)",
                "cyc2": "(R,P,Q)",
                "rev": "(P^(-T),R^(-T),Q^(-T))",
                "rev_cyc": "(Q^(-T),P^(-T),R^(-T))",
                "rev_cyc2": "(R^(-T),Q^(-T),P^(-T))",
            },
            "outer_action_on_replay_gauge_slots": {
                "id": "(gU,gV,gW)",
                "cyc": "(gV,gW,gU)",
                "cyc2": "(gW,gU,gV)",
                "rev": "(gW,gV,gU)",
                "rev_cyc": "(gU,gW,gV)",
                "rev_cyc2": "(gV,gU,gW)",
            },
            "representability_premise": "GL4, D, and the finite constant components are affine of finite type; the displayed semidirect action should be expanded into Hopf-algebra maps for a machine-checked construction.",
        },
        "witness_stabilizer_group_scheme": {
            "status": "paper-level-unformalized",
            "definition": "Stab_wit,x is the equalizer/fiber subgroup functor of H_wit whose natural action returns the fixed ordered 49-term presentation x exactly.",
            "componentwise_equations": [
                "g_l^U P U_l^sigma Q^(-1)=U_pi(l)",
                "g_l^V Q V_l^sigma R^(-1)=V_pi(l)",
                "g_l^W R W_l^sigma P^(-1)=W_pi(l)",
                "g_l^U*g_l^V*g_l^W=1",
            ],
            "finite_type_closedness_premise": "After adjoining determinant inverses and gauge inverses, these are polynomial equalizer equations on each finite component; the coordinate-ring equalizer has not been emitted by the checker.",
        },
        "Cx_subgroup_scheme_embedding": {
            "status": "paper-level-unformalized",
            "source_group_scheme": "Cx=G_m^3 over F2",
            "natural_transformation": "iota_A(p,q,r)=(pI4,qI4,rI4; uniform replay gauges q/p,r/q,p/r; pi=id; sigma=id)",
            "raw_action": "Every raw triple is fixed because (q/p)(pUq^(-1))=U, (r/q)(qVr^(-1))=V, and (p/r)(rWp^(-1))=W.",
            "closed_immersion_premise": "The three scalar diagonal matrix entries recover p,q,r and all other coordinates are the displayed Laurent monomials; an explicit coordinate-ring retraction is not materialized here.",
            "status_separation": "The field-point theorem below does not itself certify this closed subgroup-scheme statement.",
        },
        "Cx_normality": {
            "status": "paper-level-unformalized",
            "claim": "Cx is normalized by H_wit under the declared group law.",
            "evidence": "Scalar matrices commute with the connected sandwiches, uniform gauges commute with D and term relabeling, and the six outer conjugations are the explicitly replayed monomial automorphisms recorded in outer_Cx_action.",
            "missing_machine_checked_step": "Expand composition on all finite components or the corresponding Hopf-algebra coaction and verify the normal closed subgroup scheme identity over arbitrary F2-algebras.",
        },
        "field_point_result": {
            "status": "proved",
            "scope": "fields only",
            "statement": "Stab_wit,x(K)=Cx(K) for every field extension K/F2, where both sides denote points in the explicitly displayed identity-component parametrization.",
            "does_not_imply_by_itself": ["scheme equality", "equality on nonreduced test algebras", "a quotient-point formula"],
        },
        "scheme_equality_argument": {
            "status": "paper-level-unformalized",
            "conditional_conclusion": "If premises P1-P5 below are established for the displayed functors, then Stab_wit,x=Cx as F2-group schemes.",
            "premises": [
                {"id": "P1", "status": "paper-level-unformalized", "statement": "H_wit is the affine finite-type group scheme representing the displayed functor and Stab_wit,x is its affine finite-type closed stabilizer subgroup scheme."},
                {"id": "P2", "status": "paper-level-unformalized", "statement": "iota:Cx=G_m^3 -> Stab_wit,x is the displayed closed immersion."},
                {"id": "P3", "status": "proved", "statement": "After base change to an algebraic closure kbar/F2, every geometric point of Stab_wit,x lies in Cx; this is the extension-stable circuit/refinement/frame theorem."},
                {"id": "P4", "status": "computational", "statement": "The emitted 146-parameter stabilizer differential has rank 143 over F2, hence a three-dimensional kernel after every field extension."},
                {"id": "P5", "status": "paper-level-unformalized", "statement": "The emitted differential is the Zariski tangent map of the closed stabilizer in P1, and its three kernel vectors identify with d(iota)(Lie(Cx))."},
            ],
            "standard_algebraic_geometry_steps": [
                "Finite-type schemes over kbar are Jacobson. P3 therefore makes the underlying closed subsets |Stab_kbar| and |Cx_kbar| equal, because their closed points agree.",
                "That common support has local dimension three. P4-P5 give embedding dimension dim tangent=3 at the identity, so the Noetherian local ring there is regular.",
                "Translation by each Cx(kbar) point makes every closed-point local ring regular. A nonzero nilradical on a finite-type kbar-scheme has support containing a closed point, so Stab_kbar is reduced.",
                "Cx_kbar and Stab_kbar are then reduced closed subschemes of the same affine ambient scheme with the same support, hence their radical defining ideals agree and the closed subschemes are equal.",
                "Equality of the two defining ideals descends along the faithfully flat extension kbar/F2.",
            ],
            "why_not_promoted": "P1, P2, and P5 are explicit but are not independently coordinate-ring replayed; the checker therefore does not certify the conditional conclusion as proved.",
        },
        "arbitrary_test_algebra_equality": {
            "status": "unknown",
            "claim": None,
            "reason": "It would follow from a completed scheme-equality proof, but field points plus one tangent calculation are not substituted for that proof.",
        },
        "quotient_group_scheme": {
            "status": "unknown",
            "claim": None,
            "reason": "No quotient Stab_wit,x/Cx is constructed, no representability or fppf-sheaf assertion is certified, and quotient-scheme A-points are never identified with a naive quotient of point groups.",
        },
        "ambient_tensor_isotropy_distinction": {
            "status": "proved",
            "statement": "The ambient matrix-multiplication tensor isotropy contains sandwiches and all six physical orientations whether or not they return this 49-term presentation. Only certified return witnesses belong to Stab_wit,x.",
        },
    }


def build_artifact() -> dict[str, Any]:
    terms, source_summary = parse_source()
    circuits, raw_circuits = circuit_records(terms)
    refinement = refinement_certificate(terms, raw_circuits["id"])
    frames = frame_certificate(terms)
    binary = binary_crosscheck(terms)
    tangent = tangent_certificate(terms)
    points = point_certificates(terms)
    outer = outer_action_certificate(terms)
    code_path = Path(__file__).resolve()
    replay_path = REPLAY.resolve()
    source_term_words = [[f"{value:04x}" for value in term] for term in terms]
    artifact = {
        "schema": "proofs.rank49_t4.stabilizer.v2",
        "scope": "T4-A exact decomposition stabilizer of the fixed binary 4x4x4 length-49 presentation",
        "status_legend": {
            "proved": "A complete mathematical deduction whose finite inputs and witnesses are replayed by this checker; not necessarily formalized in Lean.",
            "computational": "An exact deterministic finite calculation reproduced from the canonical source, with no heuristic cap or timeout.",
            "paper-level-unformalized": "A stated mathematical argument or required structure not encoded by this checker and not promoted to a computational theorem.",
            "unknown": "No conclusion is certified.",
        },
        "provenance": {
            "source": {
                "canonical_path": SOURCE_REPOSITORY_RELATIVE.as_posix(),
                "fixture_repository_relative_path": SOURCE_REPOSITORY_RELATIVE.as_posix(),
                "fixture_resolution": "resolve fixtures/4x4x4_m49_c680_iteration65_Z2.txt relative to the producer or replayer file; no external source is opened",
                "original_external_locator": ORIGINAL_EXTERNAL_SOURCE_LOCATOR,
                "original_external_locator_usage": "provenance only; producer and replayer never open this locator",
                "sha256": SOURCE_SHA256,
                "summary": source_summary,
                "terms_row_major_hex": source_term_words,
                "terms_sha256": digest_json(source_term_words),
            },
            "producer": {
                "code_path": PRODUCER_REPOSITORY_RELATIVE.as_posix(),
                "replayer_path": REPLAY_REPOSITORY_RELATIVE.as_posix(),
                "current_owned_code_file_hashes": {
                    PRODUCER_REPOSITORY_RELATIVE.as_posix(): file_digest(code_path),
                    REPLAY_REPOSITORY_RELATIVE.as_posix(): file_digest(replay_path),
                },
                "base_git_revision": REPOSITORY_REVISION,
                "repository_mutation": "none: the producer and replayer do not invoke git",
                "diff_provenance": "Both executable inputs are identified by current_owned_code_file_hashes; no helper module or generated source is imported.",
                "python_requirement": ">=3.10, standard library only",
                "field": "F2",
                "random_seed": None,
                "solver_limits": None,
                "limits_status": "complete finite coverage; no heuristic cap, timeout, randomized search, or external solver",
                "commands": {
                    "produce": "python3 Programs/BilinearComplexity/rank49_t4/stabilizer.py --produce",
                    "producer_check_plus_independent_replay": "python3 Programs/BilinearComplexity/rank49_t4/stabilizer.py --check",
                    "independent_consumer_only": "python3 Programs/BilinearComplexity/rank49_t4/stabilizer_replay.py --check",
                },
                "artifact_path": ARTIFACT_REPOSITORY_RELATIVE.as_posix(),
                "artifact_publication": "write a same-directory temporary file, flush and fsync it, atomically replace stabilizer.json, then fsync the artifacts directory",
                "artifact_hash_policy": "The artifact SHA-256 cannot be embedded in itself; produce/check stdout reports its current hash.",
            },
        },
        "conventions": {
            "base_field": "F2",
            "term_indices": "zero-based 0,...,48",
            "matrix_encoding": "4x4 row-major; source bit 4*i+j is entry (i,j)",
            "physical_orientation_formulas": ORIENTATION_FORMULAS,
            "physical_orientation_order": list(ORIENTATIONS),
            "orientation_replay_order": "orient source factors, apply sandwich, compare equation-side gauge times target[pi], then apply inverse compensating replay gauges when replaying raw factors",
            "sandwich_equations": [
                "P U_l^sigma Q^(-1) = alpha_l U_pi(l)",
                "Q V_l^sigma R^(-1) = beta_l V_pi(l)",
                "R W_l^sigma P^(-1) = gamma_l W_pi(l)",
                "alpha_l beta_l gamma_l = 1",
            ],
            "gauge_convention": {
                "equation_side": "alpha,beta,gamma are scalars on the right sides of the displayed sandwich equations",
                "replay_side": "the actual post-sandwich raw-factor multipliers are alpha^(-1), beta^(-1), gamma^(-1)",
                "scalar_torus_equation_side": ["p/q", "q/r", "r/p"],
                "scalar_torus_replay_side": ["q/p", "r/q", "p/r"],
            },
        },
        "certificates": {
            "extension_stable_circuit_hypergraphs": circuits,
            "identity_permutation_refinement": refinement,
            "projective_scalar_frames": frames,
            "F2_independent_pair_graph_and_linear_crosscheck": binary,
            "split_torus_and_point_images": points,
            "outer_Cx_action": outer,
            "connected_action_tangent": tangent,
            "scheme_theoretic_boundary": scheme_boundary(),
        },
        "claims": [
            {"status": "proved", "claim": "All five nonidentity physical orientations have no stabilizer field point over any K/F2."},
            {"status": "proved", "claim": "The identity branch has only pi=id over every K/F2."},
            {"status": "proved", "claim": "Every stabilizer field point over K/F2 has P=pI, Q=qI, R=rI and the uniquely determined uniform gauges."},
            {"status": "proved", "claim": "Stab_wit,x(K)=Cx(K) and the direct effective point image is trivial for every field extension K/F2."},
            {"status": "computational", "claim": "Over F2 the full witness point group and direct effective point image both have order one; all term and support orbits are singleton."},
            {"status": "computational", "claim": "Over F4 the full witness point group has 27 explicitly replayed split-torus points while the direct effective point image has order one."},
            {"status": "computational", "claim": "The 146-parameter connected action differential over F2 has rank 143 and its three-dimensional kernel is exactly the emitted split-torus tangent basis."},
            {"status": "proved", "claim": "Under sigma S sigma^(-1), rotations permute (p,q,r), while every reflection both permutes and inverts them; all six actions have complete F4 conjugation replays."},
            {"status": "proved", "claim": "The Cx subgroup fixed by all six outer actions is diagonal mu_2. Diagonal G_m is normalized but not central because reflections act by inversion."},
            {"status": "paper-level-unformalized", "claim": "A five-premise finite-type/geometric-points/Lie-tangent argument would imply Stab_wit,x=Cx scheme-theoretically; the unmaterialized premises are listed and the conclusion is not promoted."},
            {"status": "unknown", "claim": "Equality on arbitrary test algebras and the points of any quotient group scheme Stab_wit,x/Cx are not computed by this artifact."},
        ],
        "direct_effective_action_consequences": {
            "status": "proved",
            "F2_term_action": "identity",
            "F2_support_action": "identity",
            "F2_five_support_orbits": 1906884,
            "action_on_any_functorially_induced_vector_space_at_x": "identity for the certified direct effective field-point image",
            "named_spaces": ["ker J", "image(dH)", "ker J/image(dH)", "coker J"],
            "matrix_materialization_status": "not emitted because the certified point image contains only the identity; this statement does not assert a quotient-group-scheme representation",
        },
        "unknowns": [
            {"status": "unknown", "item": "A machine-replayed affine/Hopf-algebra construction proving the displayed finite-type witness functor, Cx closed immersion and normality, tangent identification, and resulting scheme equality."},
            {"status": "unknown", "item": "Equality Stab_wit,x(A)=Cx(A) for arbitrary, especially nonreduced or disconnected, F2-algebras A."},
            {"status": "unknown", "item": "Representability and A-points of Stab_wit,x/Cx; no naive point-group quotient is used."},
            {"status": "unknown", "item": "Transporters between the base presentation and nonbase points of the known deformation family."},
            {"status": "unknown", "item": "Stabilizers of nonbase family fibers and the induced correspondence on the family parameter."},
            {"status": "unknown", "item": "Any analogous statement after changing the base characteristic away from two."},
            {"status": "unknown", "item": "Minimal tensor rank; a length-49 presentation is not a minimality proof."},
        ],
    }
    schema = artifact.pop("schema")
    provenance = artifact.pop("provenance")
    payload = artifact
    return {
        "schema": schema,
        "provenance": provenance,
        "certificate_payload_sha256": digest_json(payload),
        "certificate_payload": payload,
        "run_information": {
            "stored_in_certificate_payload": False,
            "dynamic_values": [],
            "stdout_only": ["artifact_sha256", "process return status", "independent replay summary"],
            "reason": "timestamps, elapsed time, host data, and mutable working-tree status are excluded from deterministic certificate bytes",
        },
    }


def publish_artifact_atomically(data: bytes) -> None:
    ARTIFACT.parent.mkdir(parents=True, exist_ok=True)
    temporary_path: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="wb",
            dir=ARTIFACT.parent,
            prefix=f".{ARTIFACT.name}.",
            suffix=".tmp",
            delete=False,
        ) as temporary:
            temporary_path = Path(temporary.name)
            temporary.write(data)
            temporary.flush()
            os.fsync(temporary.fileno())
        os.replace(temporary_path, ARTIFACT)
        temporary_path = None
        directory_flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
        directory_fd = os.open(ARTIFACT.parent, directory_flags)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
    finally:
        if temporary_path is not None:
            temporary_path.unlink(missing_ok=True)


def produce() -> None:
    artifact = build_artifact()
    publish_artifact_atomically(canonical_bytes(artifact))
    print(
        json.dumps(
            {
                "status": "produced",
                "artifact": str(ARTIFACT),
                "artifact_sha256": file_digest(ARTIFACT),
                "code_sha256": file_digest(Path(__file__).resolve()),
                "replayer_sha256": file_digest(REPLAY.resolve()),
                "source_sha256": SOURCE_SHA256,
            },
            sort_keys=True,
        )
    )


def check() -> None:
    if not ARTIFACT.is_file():
        raise RuntimeError(f"artifact does not exist: {ARTIFACT}")
    checked_in = ARTIFACT.read_bytes()
    expected = canonical_bytes(build_artifact())
    if checked_in != expected:
        actual_hash = digest_bytes(checked_in)
        expected_hash = digest_bytes(expected)
        raise RuntimeError(f"artifact mismatch: actual {actual_hash}, recomputed {expected_hash}")
    parsed = json.loads(checked_in)
    provenance = parsed["provenance"]["producer"]
    owned_hashes = provenance["current_owned_code_file_hashes"]
    if owned_hashes[PRODUCER_REPOSITORY_RELATIVE.as_posix()] != file_digest(Path(__file__).resolve()):
        raise RuntimeError("artifact producer-code provenance does not match checker")
    if owned_hashes[REPLAY_REPOSITORY_RELATIVE.as_posix()] != file_digest(REPLAY.resolve()):
        raise RuntimeError("artifact replayer-code provenance does not match checker")
    replay_process = subprocess.run(
        [sys.executable, str(REPLAY.resolve()), "--check", "--artifact", str(ARTIFACT.resolve())],
        check=False,
        capture_output=True,
        text=True,
    )
    if replay_process.returncode != 0:
        raise RuntimeError(f"independent replayer failed: {replay_process.stderr.strip()}")
    replay_result = json.loads(replay_process.stdout)
    if replay_result.get("status") != "independently-replayed":
        raise RuntimeError("independent replayer did not return its verified status")
    payload = parsed["certificate_payload"]
    print(
        json.dumps(
            {
                "status": "verified",
                "artifact": str(ARTIFACT),
                "artifact_sha256": digest_bytes(checked_in),
                "code_sha256": file_digest(Path(__file__).resolve()),
                "replayer_sha256": file_digest(REPLAY.resolve()),
                "source_sha256": SOURCE_SHA256,
                "claims": {
                    "F2_witness_point_order": payload["certificates"]["split_torus_and_point_images"]["F2"]["complete_witness_point_count"],
                    "F2_effective_image_order": payload["certificates"]["split_torus_and_point_images"]["F2"]["direct_effective_point_image_order"],
                    "F4_witness_point_order": payload["certificates"]["split_torus_and_point_images"]["F4"]["complete_witness_point_count"],
                    "F4_effective_image_order": payload["certificates"]["split_torus_and_point_images"]["F4"]["direct_effective_point_image_order"],
                    "tangent_rank": payload["certificates"]["connected_action_tangent"]["rank"],
                    "tangent_kernel_dimension": payload["certificates"]["connected_action_tangent"]["kernel_dimension"],
                    "outer_fixed_subgroup_scheme": payload["certificates"]["outer_Cx_action"]["subgroup_fixed_by_all_six_outer_actions"]["isomorphism_type"],
                    "scheme_equality_status": payload["certificates"]["scheme_theoretic_boundary"]["scheme_equality_argument"]["status"],
                    "quotient_status": payload["certificates"]["scheme_theoretic_boundary"]["quotient_group_scheme"]["status"],
                },
                "independent_replay": replay_result,
            },
            sort_keys=True,
        )
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--produce", action="store_true", help="recompute and write the deterministic artifact")
    mode.add_argument("--check", action="store_true", help="recompute/byte-check and run the independent JSON consumer/replayer")
    arguments = parser.parse_args()
    if arguments.produce:
        produce()
    else:
        check()


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print(json.dumps({"status": "error", "error": str(error)}, sort_keys=True), file=sys.stderr)
        raise
