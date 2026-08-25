#!/usr/bin/env python3
"""Independent consumer and algebraic replay checker for the rank-49 T4-A artifact."""

from __future__ import annotations

import argparse
import collections
import hashlib
import itertools
import json
import sys
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
REPOSITORY_RELATIVE_DIRECTORY = Path("Programs/BilinearComplexity/rank49_t4")
SOURCE_REPOSITORY_RELATIVE = REPOSITORY_RELATIVE_DIRECTORY / "fixtures" / "4x4x4_m49_c680_iteration65_Z2.txt"
ORIGINAL_EXTERNAL_SOURCE_LOCATOR = "/home/exedev/x/tensor/data/z2/4x4x4_m49_c680_iteration65_Z2.txt"
SOURCE = HERE / "fixtures" / "4x4x4_m49_c680_iteration65_Z2.txt"
SOURCE_SHA256 = "5fc92a6bf83fc29d9527ab100bad5d72d769178b616b31a36c3c0c0b8ad9d09d"
PRODUCER_REPOSITORY_RELATIVE = REPOSITORY_RELATIVE_DIRECTORY / "stabilizer.py"
REPLAYER_REPOSITORY_RELATIVE = REPOSITORY_RELATIVE_DIRECTORY / "stabilizer_replay.py"
ARTIFACT = HERE / "artifacts" / "stabilizer.json"
PRODUCER = HERE / "stabilizer.py"
ORIENTATIONS = ("id", "cyc", "cyc2", "rev", "rev_cyc", "rev_cyc2")
PHYSICAL = {
    "id": "(U,V,W)",
    "cyc": "(V,W,U)",
    "cyc2": "(W,U,V)",
    "rev": "(T(W),T(V),T(U))",
    "rev_cyc": "(T(U),T(W),T(V))",
    "rev_cyc2": "(T(V),T(U),T(W))",
}
INVERSE_ORIENTATION = {
    "id": "id",
    "cyc": "cyc2",
    "cyc2": "cyc",
    "rev": "rev",
    "rev_cyc": "rev_cyc",
    "rev_cyc2": "rev_cyc2",
}
MONOMIAL = {
    "id": ((0, 1), (1, 1), (2, 1)),
    "cyc": ((1, 1), (2, 1), (0, 1)),
    "cyc2": ((2, 1), (0, 1), (1, 1)),
    "rev": ((0, -1), (2, -1), (1, -1)),
    "rev_cyc": ((1, -1), (0, -1), (2, -1)),
    "rev_cyc2": ((2, -1), (1, -1), (0, -1)),
}
MONOMIAL_FORMULAS = {
    "id": "(p,q,r)",
    "cyc": "(q,r,p)",
    "cyc2": "(r,p,q)",
    "rev": "(p^(-1),r^(-1),q^(-1))",
    "rev_cyc": "(q^(-1),p^(-1),r^(-1))",
    "rev_cyc2": "(r^(-1),q^(-1),p^(-1))",
}
TERM_COUNT = 49


def canonical_bytes(value: Any) -> bytes:
    return (json.dumps(value, sort_keys=True, indent=2, separators=(",", ": ")) + "\n").encode()


def digest_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def digest_json(value: Any) -> str:
    return digest_bytes(canonical_bytes(value))


def file_digest(path: Path) -> str:
    return digest_bytes(path.read_bytes())


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def parse_source() -> list[tuple[int, int, int]]:
    raw = SOURCE.read_bytes()
    require(digest_bytes(raw) == SOURCE_SHA256, "canonical source hash mismatch")
    lines = raw.decode("ascii").splitlines()
    require(len(lines) == 4 and lines[0].split() == ["4", "4", "4", "49"], "source shape mismatch")
    factors = []
    for line in lines[1:]:
        entries = [int(value) for value in line.split()]
        require(len(entries) == 49 * 16 and set(entries) <= {0, 1}, "source factor encoding mismatch")
        factors.append([sum(entries[16 * term + bit] << bit for bit in range(16)) for term in range(49)])
    terms = list(zip(*factors))
    require(all(value for term in terms for value in term), "source has a zero factor")
    require([len({term[leg] for term in terms}) for leg in range(3)] == [49, 49, 49], "source factor collision")
    return terms


def transpose_mask(value: int) -> int:
    return sum(((value >> (4 * i + j)) & 1) << (4 * j + i) for i in range(4) for j in range(4))


def orient_masks(terms: list[tuple[int, int, int]], orientation: str) -> list[tuple[int, int, int]]:
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
            raise RuntimeError(f"bad orientation {orientation}")
        output.append(item)
    return output


def vector_rank(values: list[int]) -> int:
    basis: dict[int, int] = {}
    for value in values:
        while value:
            pivot = value.bit_length() - 1
            if pivot in basis:
                value ^= basis[pivot]
            else:
                basis[pivot] = value
                break
    return len(basis)


def matrix_rank(mask: int) -> int:
    return vector_rank([(mask >> (4 * i)) & 15 for i in range(4)])


def three_circuits(terms: list[tuple[int, int, int]]) -> list[list[tuple[int, int, int]]]:
    return [
        [triple for triple in itertools.combinations(range(49), 3) if terms[triple[0]][leg] ^ terms[triple[1]][leg] ^ terms[triple[2]][leg] == 0]
        for leg in range(3)
    ]


def circuit_incidence(circuits: list[list[tuple[int, int, int]]]) -> list[list[list[tuple[int, int]]]]:
    output: list[list[list[tuple[int, int]]]] = [[[] for _ in range(49)] for _ in range(3)]
    for leg in range(3):
        for triple in circuits[leg]:
            for vertex in triple:
                output[leg][vertex].append(tuple(other for other in triple if other != vertex))
    return output


def degree_counter(circuits: list[list[tuple[int, int, int]]]) -> collections.Counter[tuple[int, int, int]]:
    incidence = circuit_incidence(circuits)
    return collections.Counter(tuple(len(incidence[leg][term]) for leg in range(3)) for term in range(49))


def signatures_to_colors(signatures: list[tuple[Any, ...]]) -> tuple[list[int], list[tuple[Any, ...]]]:
    definitions = sorted(set(signatures))
    lookup = {signature: color for color, signature in enumerate(definitions)}
    return [lookup[signature] for signature in signatures], definitions


def independent_refinement(terms: list[tuple[int, int, int]], circuits: list[list[tuple[int, int, int]]]) -> list[list[int]]:
    incidence = circuit_incidence(circuits)
    signatures = [
        (tuple(matrix_rank(value) for value in terms[term]), tuple(len(incidence[leg][term]) for leg in range(3)))
        for term in range(49)
    ]
    colors, _ = signatures_to_colors(signatures)
    levels = []
    for level in range(3):
        levels.append(colors)
        if level == 2:
            break
        following = []
        for term in range(49):
            per_leg = []
            for leg in range(3):
                pairs = [tuple(sorted((colors[a], colors[b]))) for a, b in incidence[leg][term]]
                per_leg.append(tuple(sorted(pairs)))
            following.append((colors[term], tuple(per_leg)))
        colors, _ = signatures_to_colors(following)
    return levels


def replay_geometric_certificate(artifact: dict[str, Any], terms: list[tuple[int, int, int]]) -> dict[str, Any]:
    certificate = artifact["certificates"]["extension_stable_circuit_hypergraphs"]
    branches = certificate["orientation_branches"]
    require([branch["orientation"] for branch in branches] == list(ORIENTATIONS), "orientation branch coverage/order mismatch")
    raw: dict[str, list[list[tuple[int, int, int]]]] = {}
    for branch in branches:
        orientation = branch["orientation"]
        require(branch["physical_formula"] == PHYSICAL[orientation], f"physical formula mismatch for {orientation}")
        circuits = three_circuits(orient_masks(terms, orientation))
        raw[orientation] = circuits
        serialized = [[[a, b, c] for a, b, c in leg] for leg in circuits]
        require(branch["circuits_by_output_leg"] == dict(zip("UVW", serialized)), f"circuit transcript mismatch for {orientation}")
        require(branch["ordered_circuit_counts"] == [len(leg) for leg in circuits], f"circuit counts mismatch for {orientation}")
        require(branch["circuit_transcript_sha256"] == digest_json(serialized), f"circuit digest mismatch for {orientation}")
    require([len(leg) for leg in raw["id"]] == [29, 29, 27], "target circuit counts changed")
    target_counter = degree_counter(raw["id"])
    for orientation in ORIENTATIONS[1:]:
        counts = [len(leg) for leg in raw[orientation]]
        require(counts != [29, 29, 27] or degree_counter(raw[orientation]) != target_counter, f"orientation {orientation} was not rejected")
    levels = independent_refinement(terms, raw["id"])
    emitted_levels = artifact["certificates"]["identity_permutation_refinement"]["levels"]
    require(len(emitted_levels) == 3, "refinement level count mismatch")
    for level, emitted in enumerate(emitted_levels):
        require(emitted["colors_by_zero_based_term"] == levels[level], f"refinement colors mismatch at level {level}")
    require([len(set(colors)) for colors in levels] == [16, 46, 49], "refinement is not discrete")
    require(artifact["certificates"]["identity_permutation_refinement"]["coverage"]["only_compatible_permutation"] == list(range(49)), "identity permutation certificate mismatch")
    return {"orientation_count": 6, "rejected_orientation_count": 5, "refinement_color_counts": [16, 46, 49]}


def outer_product_mask(column: int, row: int) -> int:
    output = 0
    for i in range(4):
        for j in range(4):
            output |= (((column >> i) & 1) & ((row >> j) & 1)) << (4 * i + j)
    return output


def independent_rank_one_factorization(mask: int) -> tuple[int, int]:
    require(matrix_rank(mask) == 1, "projective-frame factor does not have matrix rank one")
    candidates = [
        (column, row)
        for column in range(1, 16)
        for row in range(1, 16)
        if outer_product_mask(column, row) == mask
    ]
    require(len(candidates) == 1, "rank-one factorization over F2 is not unique")
    column, row = candidates[0]
    require(outer_product_mask(column, row) == mask, "rank-one outer-product reconstruction failed")
    return column, row


def independent_basis_coordinates(vector: int, basis: list[int]) -> int:
    solutions = []
    for coefficients in range(16):
        reconstructed = 0
        for index, basis_vector in enumerate(basis):
            if (coefficients >> index) & 1:
                reconstructed ^= basis_vector
        if reconstructed == vector:
            solutions.append(coefficients)
    require(len(solutions) == 1, "projective link does not have unique basis coordinates")
    return solutions[0]


def replay_projective_scalar_frames(artifact: dict[str, Any], terms: list[tuple[int, int, int]]) -> dict[str, Any]:
    certificate = artifact["certificates"]["projective_scalar_frames"]
    frames = certificate["frames"]
    require(len(frames) == 3, "projective scalar-frame count mismatch")
    expected = {
        "P": (0, "U", "column", "P"),
        "Q": (0, "U", "row", "Q^(-T)"),
        "R": (1, "V", "row", "R^(-T)"),
    }
    require({frame["matrix_forced_scalar"] for frame in frames} == set(expected), "frames do not cover exactly P,Q,R")
    summaries = []
    total_factorizations = 0
    total_links = 0
    for frame in frames:
        matrix_name = frame["matrix_forced_scalar"]
        factor_index, factor_name, side_name, operator_name = expected[matrix_name]
        require(frame["factor"] == factor_name, f"{matrix_name} frame uses the wrong tensor factor")
        require(frame["projective_side"] == side_name, f"{matrix_name} frame uses the wrong projective side")
        require(frame["operator_fixing_lines"] == operator_name, f"{matrix_name} frame names the wrong induced operator")
        side_index = 0 if side_name == "column" else 1
        basis_records = frame["basis"]
        link_records = frame["links"]
        require(len(basis_records) == 4, f"{matrix_name} frame does not contain four basis lines")
        basis_terms = [record["term0"] for record in basis_records]
        link_terms = [record["term0"] for record in link_records]
        require(len(set(basis_terms)) == 4 and not (set(basis_terms) & set(link_terms)), f"{matrix_name} frame term coverage overlaps")
        selected_terms = set(basis_terms + link_terms)
        factorization_records = {record["term0"]: record for record in frame["rank_one_factorizations"]}
        require(len(factorization_records) == len(frame["rank_one_factorizations"]), f"{matrix_name} factorization terms repeat")
        require(set(factorization_records) == selected_terms, f"{matrix_name} rank-one factorization coverage mismatch")
        vectors: dict[int, int] = {}
        for term in sorted(selected_terms):
            mask = terms[term][factor_index]
            column, row = independent_rank_one_factorization(mask)
            record = factorization_records[term]
            require(record["factor_matrix_hex"] == f"{mask:04x}", f"{matrix_name} source factor record mismatch")
            require(record["column_vector_hex"] == f"{column:x}", f"{matrix_name} column factor mismatch")
            require(record["row_vector_hex"] == f"{row:x}", f"{matrix_name} row factor mismatch")
            vectors[term] = (column, row)[side_index]
        basis = [vectors[term] for term in basis_terms]
        require(vector_rank(basis) == 4, f"{matrix_name} four-vector basis has rank below four")
        require(frame["basis_rank_over_F2"] == 4, f"{matrix_name} emitted basis rank mismatch")
        for term, record, vector in zip(basis_terms, basis_records, basis):
            require(record["term0"] == term and record["vector_hex"] == f"{vector:x}", f"{matrix_name} emitted basis vector mismatch")
        graph_edges: set[tuple[int, int]] = set()
        link_supports = []
        for record in link_records:
            term = record["term0"]
            vector = vectors[term]
            coordinates = independent_basis_coordinates(vector, basis)
            support = [index for index in range(4) if (coordinates >> index) & 1]
            require(len(support) >= 2, f"{matrix_name} link does not equate two basis eigenvalues")
            reconstructed = 0
            for index in support:
                reconstructed ^= basis[index]
            require(reconstructed == vector, f"{matrix_name} link reconstruction failed")
            require(record["vector_hex"] == f"{vector:x}", f"{matrix_name} link vector record mismatch")
            require(record["basis_coordinates_hex"] == f"{coordinates:x}", f"{matrix_name} link coordinate record mismatch")
            require(record["coordinate_support"] == support, f"{matrix_name} link support record mismatch")
            require(record["xor_reconstruction_hex"] == f"{reconstructed:x}", f"{matrix_name} link reconstruction record mismatch")
            for endpoint in support[1:]:
                graph_edges.add(tuple(sorted((support[0], endpoint))))
            link_supports.append(support)
        adjacency = [set() for _ in range(4)]
        for left, right in graph_edges:
            adjacency[left].add(right)
            adjacency[right].add(left)
        reached = {0}
        frontier = [0]
        while frontier:
            vertex = frontier.pop()
            for neighbor in adjacency[vertex] - reached:
                reached.add(neighbor)
                frontier.append(neighbor)
        require(reached == set(range(4)), f"{matrix_name} projective support graph is disconnected")
        require(frame["support_graph_edges"] == [list(edge) for edge in sorted(graph_edges)], f"{matrix_name} support graph edge record mismatch")
        require(frame["support_graph_connected"] is True, f"{matrix_name} support graph status mismatch")
        require(all(support for support in link_supports), f"{matrix_name} has an empty link support")
        summaries.append(
            {
                "matrix": matrix_name,
                "factor": factor_name,
                "side": side_name,
                "basis_rank": 4,
                "link_count": len(link_records),
                "support_graph_connected": True,
                "deduced_scalar": True,
            }
        )
        total_factorizations += len(factorization_records)
        total_links += len(link_records)
    require(certificate["conclusion"] == "The stabilizer equations force P=pI4, Q=qI4, R=rI4 with p,q,r nonzero.", "projective frame scalar conclusion mismatch")
    return {
        "frames_replayed": 3,
        "rank_one_factorizations_replayed": total_factorizations,
        "basis_ranks": [summary["basis_rank"] for summary in summaries],
        "links_replayed": total_links,
        "connected_support_graphs": 3,
        "matrices_independently_forced_scalar": [summary["matrix"] for summary in summaries],
        "frame_summaries": summaries,
    }


FIELD = {
    "F2": {"size": 2, "degree": 1, "modulus": 0b11},
    "F4": {"size": 4, "degree": 2, "modulus": 0b111},
}


def ff_mul(field: str, a: int, b: int) -> int:
    spec = FIELD[field]
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
    for power in range(2 * spec["degree"] - 2, spec["degree"] - 1, -1):
        if (result >> power) & 1:
            result ^= spec["modulus"] << (power - spec["degree"])
    require(0 <= result < spec["size"], "finite field reduction failed")
    return result


def ff_pow(field: str, value: int, exponent: int) -> int:
    answer = 1
    while exponent:
        if exponent & 1:
            answer = ff_mul(field, answer, value)
        value = ff_mul(field, value, value)
        exponent >>= 1
    return answer


def ff_inv(field: str, value: int) -> int:
    require(value != 0, "attempt to invert zero")
    return ff_pow(field, value, FIELD[field]["size"] - 2)


def mat_from_mask(mask: int) -> list[int]:
    return [(mask >> bit) & 1 for bit in range(16)]


def mat_word(matrix: list[int]) -> str:
    return "".join(format(value, "x") for value in matrix)


def mat_mul(field: str, left: list[int], right: list[int]) -> list[int]:
    require(len(left) == len(right) == 16, "matrix shape mismatch")
    output = [0] * 16
    for i in range(4):
        for j in range(4):
            value = 0
            for k in range(4):
                value ^= ff_mul(field, left[4 * i + k], right[4 * k + j])
            output[4 * i + j] = value
    return output


def mat_scale(field: str, scalar: int, matrix: list[int]) -> list[int]:
    return [ff_mul(field, scalar, value) for value in matrix]


def mat_transpose(matrix: list[int]) -> list[int]:
    return [matrix[4 * j + i] for i in range(4) for j in range(4)]


def mat_identity() -> list[int]:
    return [1 if i == j else 0 for i in range(4) for j in range(4)]


def mat_inverse(field: str, matrix: list[int]) -> list[int]:
    rows = [[matrix[4 * i + j] for j in range(4)] + [1 if i == j else 0 for j in range(4)] for i in range(4)]
    for column in range(4):
        pivot = next((row for row in range(column, 4) if rows[row][column]), None)
        require(pivot is not None, "singular recorded matrix")
        rows[column], rows[pivot] = rows[pivot], rows[column]
        inverse_pivot = ff_inv(field, rows[column][column])
        rows[column] = [ff_mul(field, inverse_pivot, value) for value in rows[column]]
        for row in range(4):
            if row != column and rows[row][column]:
                coefficient = rows[row][column]
                rows[row] = [a ^ ff_mul(field, coefficient, b) for a, b in zip(rows[row], rows[column])]
    require([row[:4] for row in rows] == [[1 if i == j else 0 for j in range(4)] for i in range(4)], "inverse elimination failed")
    return [rows[i][4 + j] for i in range(4) for j in range(4)]


def orient_matrices(triple: list[list[int]], orientation: str) -> list[list[int]]:
    u, v, w = triple
    if orientation == "id":
        return [u, v, w]
    if orientation == "cyc":
        return [v, w, u]
    if orientation == "cyc2":
        return [w, u, v]
    if orientation == "rev":
        return [mat_transpose(w), mat_transpose(v), mat_transpose(u)]
    if orientation == "rev_cyc":
        return [mat_transpose(u), mat_transpose(w), mat_transpose(v)]
    if orientation == "rev_cyc2":
        return [mat_transpose(v), mat_transpose(u), mat_transpose(w)]
    raise RuntimeError(f"bad orientation {orientation}")


def orient_scalars(triple: tuple[int, int, int], orientation: str) -> tuple[int, int, int]:
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
    raise RuntimeError(f"bad orientation {orientation}")


def monomial(field: str, orientation: str, coordinates: tuple[int, int, int]) -> tuple[int, int, int]:
    return tuple(coordinates[index] if exponent == 1 else ff_inv(field, coordinates[index]) for index, exponent in MONOMIAL[orientation])


def replay_gauges(field: str, coordinates: tuple[int, int, int]) -> tuple[int, int, int]:
    p, q, r = coordinates
    return ff_mul(field, q, ff_inv(field, p)), ff_mul(field, r, ff_inv(field, q)), ff_mul(field, p, ff_inv(field, r))


def scalar_sandwich(field: str, triple: list[list[int]], coordinates: tuple[int, int, int]) -> list[list[int]]:
    gauges = replay_gauges(field, coordinates)
    equation_scales = tuple(ff_inv(field, value) for value in gauges)
    return [mat_scale(field, scale, matrix) for scale, matrix in zip(equation_scales, triple)]


def matrix_record(record: dict[str, Any], field: str) -> list[int]:
    matrix = record["entries_row_major"]
    require(isinstance(matrix, list) and len(matrix) == 16 and all(isinstance(value, int) and 0 <= value < FIELD[field]["size"] for value in matrix), "invalid matrix record")
    require(record["word"] == mat_word(matrix), "matrix word mismatch")
    return matrix


def replay_witness(witness: dict[str, Any], terms: list[tuple[int, int, int]]) -> str:
    field = witness["field"]
    require(field in FIELD, "unsupported witness field")
    permutation = witness["term_permutation_zero_based"]
    require(sorted(permutation) == list(range(49)), "recorded term map is not a permutation")
    orientation = witness["orientation"]
    require(orientation in ORIENTATIONS, "recorded witness orientation is invalid")
    matrices = [matrix_record(witness["matrices"][name], field) for name in "PQR"]
    inverses = [matrix_record(witness["matrix_inverses"][name + "inv"], field) for name in "PQR"]
    identity = mat_identity()
    for name, matrix, inverse in zip("PQR", matrices, inverses):
        require(mat_inverse(field, matrix) == inverse, f"stored {name} inverse is not the independent inverse")
        require(mat_mul(field, matrix, inverse) == identity and mat_mul(field, inverse, matrix) == identity, f"{name} inverse product failed")
    equation_gauges = witness["equation_side_term_gauges"]
    replay_side = witness["replay_side_term_gauges"]
    require(len(equation_gauges) == len(replay_side) == 49, "term gauge coverage mismatch")
    records = witness["mapped_factor_equations"]
    require(len(records) == witness["mapped_factor_equation_count"] == 147, "mapped equation coverage mismatch")
    lookup = {(record["zero_based_term"], "UVW".index(record["output_leg"])): record for record in records}
    require(len(lookup) == 147, "mapped equation keys are not unique")
    oriented_terms = orient_masks(terms, orientation)
    replayed = []
    for term in range(49):
        source = [mat_from_mask(value) for value in oriented_terms[term]]
        target = [mat_from_mask(value) for value in terms[permutation[term]]]
        lhs = [
            mat_mul(field, mat_mul(field, matrices[0], source[0]), inverses[1]),
            mat_mul(field, mat_mul(field, matrices[1], source[1]), inverses[2]),
            mat_mul(field, mat_mul(field, matrices[2], source[2]), inverses[0]),
        ]
        eq = equation_gauges[term]
        rep = replay_side[term]
        require(len(eq) == len(rep) == 3, "gauge triple shape mismatch")
        require(ff_mul(field, ff_mul(field, eq[0], eq[1]), eq[2]) == 1, "equation gauge product failed")
        require(ff_mul(field, ff_mul(field, rep[0], rep[1]), rep[2]) == 1, "replay gauge product failed")
        term_words = []
        for leg in range(3):
            require(rep[leg] == ff_inv(field, eq[leg]), "replay gauge is not inverse equation gauge")
            rhs = mat_scale(field, eq[leg], target[leg])
            after = mat_scale(field, rep[leg], lhs[leg])
            require(lhs[leg] == rhs and after == target[leg], "mapped-factor equation or compensating replay failed")
            record = lookup[(term, leg)]
            require(record["lhs_word"] == mat_word(lhs[leg]), "recorded lhs word mismatch")
            require(record["equation_scalar"] == eq[leg] and record["rhs_word"] == mat_word(rhs), "recorded equation rhs mismatch")
            require(record["replay_multiplier"] == rep[leg] and record["after_replay_word"] == mat_word(after), "recorded replay mismatch")
            require(record["target_word"] == mat_word(target[leg]) and record["equation_holds"] and record["replay_holds"], "recorded target/status mismatch")
            term_words.append(mat_word(after))
        replayed.append(term_words)
    require(witness["mapped_factor_equations_sha256"] == digest_json(records), "mapped equation digest mismatch")
    require(witness["replayed_decomposition_sha256"] == digest_json(replayed), "replayed decomposition digest mismatch")
    require(witness["full_replay_holds"] is True, "witness full replay flag is false")
    return digest_json(replayed)


def replay_field_points(artifact: dict[str, Any], terms: list[tuple[int, int, int]]) -> dict[str, Any]:
    points = artifact["certificates"]["split_torus_and_point_images"]
    result = {}
    for field, expected_coordinates in (
        ("F2", {(1, 1, 1)}),
        ("F4", set(itertools.product(range(1, 4), repeat=3))),
    ):
        section = points[field]
        witnesses = section["witnesses"]
        coordinates = {tuple(witness["torus_coordinates"]["encoded"][name] for name in "pqr") for witness in witnesses}
        require(coordinates == expected_coordinates, f"{field} torus enumeration is incomplete")
        images = {replay_witness(witness, terms) for witness in witnesses}
        require(len(images) == 1, f"{field} direct action image is not singleton")
        require(section["complete_witness_point_count"] == len(expected_coordinates), f"{field} witness count mismatch")
        require(section["direct_effective_point_image_order"] == 1, f"{field} direct image order mismatch")
        result[field] = {"witnesses_replayed": len(witnesses), "mapped_factor_equations_replayed": 147 * len(witnesses), "direct_image_order": len(images)}
    return result


def replay_outer_action(artifact: dict[str, Any], terms: list[tuple[int, int, int]]) -> dict[str, Any]:
    certificate = artifact["certificates"]["outer_Cx_action"]
    actions = certificate["actions"]
    require([record["orientation"] for record in actions] == list(ORIENTATIONS), "outer action coverage/order mismatch")
    for record in actions:
        orientation = record["orientation"]
        require(record["physical_formula"] == PHYSICAL[orientation], f"outer physical formula mismatch for {orientation}")
        require(record["coordinate_formula"] == MONOMIAL_FORMULAS[orientation], f"outer monomial formula mismatch for {orientation}")
        exponent_matrix = [[0, 0, 0] for _ in range(3)]
        for row, (column, exponent) in enumerate(MONOMIAL[orientation]):
            exponent_matrix[row][column] = exponent
        require(record["exponent_matrix_rows"] == exponent_matrix, f"outer exponent matrix mismatch for {orientation}")
        table = record["F4_replay_table"]
        require(len(table) == 27 and record["F4_nonzero_input_count"] == 27, f"outer F4 table coverage mismatch for {orientation}")
        lookup = {tuple(row["input_coordinates"]): row for row in table}
        require(set(lookup) == set(itertools.product(range(1, 4), repeat=3)), f"outer F4 inputs incomplete for {orientation}")
        equation_count = 0
        for coordinates, row in lookup.items():
            transformed = monomial("F4", orientation, coordinates)
            gauges = replay_gauges("F4", coordinates)
            transported = orient_scalars(gauges, orientation)
            output_gauges = replay_gauges("F4", transformed)
            require(transformed == tuple(row["output_coordinates"]), f"outer coordinate replay mismatch for {orientation}")
            require(gauges == tuple(row["input_replay_gauges"]), f"outer input gauge mismatch for {orientation}")
            require(transported == output_gauges == tuple(row["transported_replay_gauges"]) == tuple(row["output_replay_gauges"]), f"outer gauge transport mismatch for {orientation}")
            for masks in terms:
                source = [mat_from_mask(mask) for mask in masks]
                left = orient_matrices(scalar_sandwich("F4", orient_matrices(source, INVERSE_ORIENTATION[orientation]), coordinates), orientation)
                right = scalar_sandwich("F4", source, transformed)
                require(left == right, f"outer sandwich conjugation mismatch for {orientation}")
                equation_count += 3
        require(equation_count == record["mapped_factor_conjugation_equation_count"] == 3969, f"outer equation count mismatch for {orientation}")
        require(record["F4_replay_table_sha256"] == digest_json(table), f"outer table digest mismatch for {orientation}")
    for coordinates in itertools.product(range(1, 4), repeat=3):
        require(monomial("F4", "cyc", monomial("F4", "cyc", monomial("F4", "cyc", coordinates))) == coordinates, "cyclic action does not cube to identity")
        for reflection in ("rev", "rev_cyc", "rev_cyc2"):
            require(monomial("F4", reflection, monomial("F4", reflection, coordinates)) == coordinates, f"{reflection} does not square to identity")
    fixed = certificate["fixed_subgroup_schemes"]
    expected_fixed = {
        "id": ("(0)", "G_m^3"),
        "cyc": ("(p-q,q-r)", "diagonal G_m"),
        "cyc2": ("(p-q,q-r)", "diagonal G_m"),
        "rev": ("(p^2-1,q*r-1)", "mu_2 x G_m"),
        "rev_cyc": ("(p*q-1,r^2-1)", "G_m x mu_2"),
        "rev_cyc2": ("(p*r-1,q^2-1)", "G_m x mu_2"),
    }
    for name, (ideal, kind) in expected_fixed.items():
        require(fixed[name]["equalizer_ideal"] == ideal and fixed[name]["isomorphism_type"] == kind, f"fixed subgroup analysis mismatch for {name}")
    all_fixed = certificate["subgroup_fixed_by_all_six_outer_actions"]
    require(all_fixed["isomorphism_type"] == "diagonal mu_2", "outer-central subgroup is not diagonal mu_2")
    require(all_fixed["equalizer_ideal_in_F2[p+-1,q+-1,r+-1]"] == "(p-q,q-r,p^2-1)", "outer-central equalizer ideal mismatch")
    correction = certificate["central_subgroup_correction"]
    require("not diagonal G_m" in correction["correction"] and "t -> t^(-1)" in correction["correction"], "central subgroup correction is absent")
    fixed_counts = {
        orientation: sum(monomial("F4", orientation, coordinates) == coordinates for coordinates in itertools.product(range(1, 4), repeat=3))
        for orientation in ORIENTATIONS
    }
    require(fixed_counts == {"id": 27, "cyc": 3, "cyc2": 3, "rev": 3, "rev_cyc": 3, "rev_cyc2": 3}, "F4 fixed-point counts disagree with equalizers")
    return {"actions_replayed": 6, "mapped_factor_conjugation_equations_replayed": 6 * 3969, "F4_fixed_point_counts": fixed_counts, "all_outer_fixed_scheme": "diagonal mu_2"}


def binary_mat_mul(left: int, right: int) -> int:
    output = 0
    for i in range(4):
        for j in range(4):
            bit = 0
            for k in range(4):
                bit ^= ((left >> (4 * i + k)) & 1) & ((right >> (4 * k + j)) & 1)
            output |= bit << (4 * i + j)
    return output


def packed(blocks: list[list[int]]) -> int:
    return sum(value << (16 * (leg * 49 + term)) for leg in range(3) for term, value in enumerate(blocks[leg]))


def tangent_generators(terms: list[tuple[int, int, int]]) -> list[int]:
    generators = []
    for term, (u, v, w) in enumerate(terms):
        blocks = [[0] * 49 for _ in range(3)]
        blocks[0][term], blocks[1][term] = u, v
        generators.append(packed(blocks))
        blocks = [[0] * 49 for _ in range(3)]
        blocks[0][term], blocks[2][term] = u, w
        generators.append(packed(blocks))
    for kind in range(3):
        for i in range(4):
            for j in range(4):
                elementary = 1 << (4 * i + j)
                blocks = [[0] * 49 for _ in range(3)]
                if kind == 0:
                    blocks[0] = [binary_mat_mul(elementary, term[0]) for term in terms]
                    blocks[2] = [binary_mat_mul(term[2], elementary) for term in terms]
                elif kind == 1:
                    blocks[0] = [binary_mat_mul(term[0], elementary) for term in terms]
                    blocks[1] = [binary_mat_mul(elementary, term[1]) for term in terms]
                else:
                    blocks[1] = [binary_mat_mul(term[1], elementary) for term in terms]
                    blocks[2] = [binary_mat_mul(elementary, term[2]) for term in terms]
                generators.append(packed(blocks))
    require(len(generators) == 146, "tangent generator count mismatch")
    return generators


def tangent_elimination(generators: list[int]) -> tuple[int, list[int]]:
    basis: dict[int, tuple[int, int]] = {}
    relations = []
    for column, generator in enumerate(generators):
        value = generator
        parameters = 1 << column
        while value:
            pivot = value.bit_length() - 1
            if pivot in basis:
                value ^= basis[pivot][0]
                parameters ^= basis[pivot][1]
            else:
                basis[pivot] = (value, parameters)
                break
        if not value:
            relations.append(parameters)
    return len(basis), relations


def expected_torus_relations() -> list[int]:
    output = []
    for a, b, c in ((1, 0, 0), (0, 1, 0), (0, 0, 1)):
        relation = 0
        for term in range(49):
            if b ^ c:
                relation |= 1 << (2 * term)
            if c ^ a:
                relation |= 1 << (2 * term + 1)
        for kind, coefficient in enumerate((a, b, c)):
            if coefficient:
                for i in range(4):
                    relation |= 1 << (98 + 16 * kind + 4 * i + i)
        output.append(relation)
    return output


def replay_tangent(artifact: dict[str, Any], terms: list[tuple[int, int, int]]) -> dict[str, int]:
    rank, relations = tangent_elimination(tangent_generators(terms))
    require(rank == 143 and relations == expected_torus_relations(), "independent tangent kernel mismatch")
    emitted = artifact["certificates"]["connected_action_tangent"]
    require(emitted["rank"] == rank and emitted["kernel_dimension"] == len(relations), "emitted tangent dimensions mismatch")
    require(emitted["kernel_basis_hex"] == [f"{relation:037x}" for relation in relations], "emitted tangent basis mismatch")
    return {"rank": rank, "kernel_dimension": len(relations)}


def replay_status_boundaries(artifact: dict[str, Any]) -> None:
    boundary = artifact["certificates"]["scheme_theoretic_boundary"]
    require(boundary["field_point_result"]["status"] == "proved", "field-point result is not separately proved")
    for key in ("finite_type_witness_group_scheme_functor", "witness_stabilizer_group_scheme", "Cx_subgroup_scheme_embedding", "Cx_normality", "scheme_equality_argument"):
        require(boundary[key]["status"] == "paper-level-unformalized", f"scheme premise {key} is overstated")
    for key in ("arbitrary_test_algebra_equality", "quotient_group_scheme"):
        require(boundary[key]["status"] == "unknown", f"unknown boundary {key} is overstated")
    require(len(boundary["scheme_equality_argument"]["premises"]) == 5, "scheme equality premises are incomplete")


def replay_provenance(artifact: dict[str, Any], document: dict[str, Any], artifact_bytes: bytes, terms: list[tuple[int, int, int]]) -> None:
    require(artifact_bytes == canonical_bytes(document), "artifact is not canonical JSON")
    require(document["schema"] == "proofs.rank49_t4.stabilizer.v2", "artifact schema mismatch")
    require(document["certificate_payload_sha256"] == digest_json(document["certificate_payload"]), "certificate payload digest mismatch")
    source = artifact["provenance"]["source"]
    relative_source = SOURCE_REPOSITORY_RELATIVE.as_posix()
    require(source["canonical_path"] == relative_source, "canonical fixture locator mismatch")
    require(source["fixture_repository_relative_path"] == relative_source, "repository-relative fixture provenance mismatch")
    require(source["original_external_locator"] == ORIGINAL_EXTERNAL_SOURCE_LOCATOR, "original external locator provenance mismatch")
    require(source["original_external_locator_usage"] == "provenance only; producer and replayer never open this locator", "external locator usage policy mismatch")
    require(source["sha256"] == SOURCE_SHA256, "canonical source hash provenance mismatch")
    words = [[f"{value:04x}" for value in term] for term in terms]
    require(source["terms_row_major_hex"] == words and source["terms_sha256"] == digest_json(words), "source term provenance mismatch")
    producer = artifact["provenance"]["producer"]
    hashes = producer["current_owned_code_file_hashes"]
    require(producer["base_git_revision"] == "6866f8be63692dc918e26d75db9414325b03b78c", "base git revision mismatch")
    require(hashes[PRODUCER_REPOSITORY_RELATIVE.as_posix()] == file_digest(PRODUCER), "producer hash provenance mismatch")
    require(hashes[REPLAYER_REPOSITORY_RELATIVE.as_posix()] == file_digest(Path(__file__).resolve()), "replayer hash provenance mismatch")
    require(producer["field"] == "F2", "base field provenance mismatch")
    require(producer["random_seed"] is None and producer["solver_limits"] is None, "producer has an unrecorded seed or limit")
    policy = artifact["run_information"]
    require(policy["stored_in_certificate_payload"] is False and policy["dynamic_values"] == [], "dynamic run data leaked into certificate payload")


def check(path: Path) -> dict[str, Any]:
    artifact_bytes = path.read_bytes()
    document = json.loads(artifact_bytes)
    artifact = dict(document["certificate_payload"])
    artifact["schema"] = document["schema"]
    artifact["provenance"] = document["provenance"]
    artifact["run_information"] = document["run_information"]
    terms = parse_source()
    replay_provenance(artifact, document, artifact_bytes, terms)
    geometric = replay_geometric_certificate(artifact, terms)
    frames = replay_projective_scalar_frames(artifact, terms)
    points = replay_field_points(artifact, terms)
    outer = replay_outer_action(artifact, terms)
    tangent = replay_tangent(artifact, terms)
    replay_status_boundaries(artifact)
    return {
        "status": "independently-replayed",
        "artifact": str(path),
        "artifact_sha256": digest_bytes(artifact_bytes),
        "source_sha256": SOURCE_SHA256,
        "source_fixture_repository_relative": SOURCE_REPOSITORY_RELATIVE.as_posix(),
        "replayer_sha256": file_digest(Path(__file__).resolve()),
        "producer_sha256": file_digest(PRODUCER),
        "geometric_certificate": geometric,
        "projective_scalar_frame_replay": frames,
        "field_point_replay": points,
        "outer_Cx_action_replay": outer,
        "tangent_replay": tangent,
        "scheme_equality_status": artifact["certificates"]["scheme_theoretic_boundary"]["scheme_equality_argument"]["status"],
        "quotient_status": artifact["certificates"]["scheme_theoretic_boundary"]["quotient_group_scheme"]["status"],
        "arbitrary_test_algebra_status": artifact["certificates"]["scheme_theoretic_boundary"]["arbitrary_test_algebra_equality"]["status"],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", required=True)
    parser.add_argument("--artifact", type=Path, default=ARTIFACT)
    arguments = parser.parse_args()
    print(json.dumps(check(arguments.artifact.resolve()), sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print(json.dumps({"status": "error", "error": str(error)}, sort_keys=True), file=sys.stderr)
        raise
