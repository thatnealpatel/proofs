#!/usr/bin/env python3
"""Exact support-five census for the fixed binary rank-49 presentation."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import itertools
import json
import math
import os
import struct
import subprocess
import sys
import tempfile
import time
from collections import Counter, defaultdict
from pathlib import Path

SOURCE_SHA256 = "5fc92a6bf83fc29d9527ab100bad5d72d769178b616b31a36c3c0c0b8ad9d09d"
GENERATION_BASE_REVISION = "6866f8be63692dc918e26d75db9414325b03b78c"
GENERATION_BASE_POLICY = "fixed generation base; verified present and ancestor of generation/check HEAD"
REPO_ROOT = Path(__file__).resolve().parents[3]
SCRIPT_RELATIVE = Path("Programs/BilinearComplexity/rank49_t4/support5_census.py")
FIXTURE_RELATIVE = Path("Programs/BilinearComplexity/rank49_t4/fixtures/4x4x4_m49_c680_iteration65_Z2.txt")
ARTIFACT_RELATIVE = Path("Programs/BilinearComplexity/rank49_t4/artifacts/support5_census.json")
ORBIT_DIRECTORY_RELATIVE = Path("Programs/BilinearComplexity/rank49_t4/artifacts")
GENERIC_ORBIT_RELATIVE = ORBIT_DIRECTORY_RELATIVE / "support5_orbits.jsonl.gz"
EXTERNAL_SOURCE_PROVENANCE_LOCATOR = "~/x/tensor/data/z2/4x4x4_m49_c680_iteration65_Z2.txt"
FIXTURE_DEFAULT = REPO_ROOT / FIXTURE_RELATIVE
ARTIFACT_DEFAULT = REPO_ROOT / ARTIFACT_RELATIVE
ORBIT_DIRECTORY_DEFAULT = REPO_ROOT / ORBIT_DIRECTORY_RELATIVE
ORIENTATION_NAMES = ("abc", "bca", "cab", "acb", "cba", "bac")
LOCAL_TRIPLES = tuple(itertools.combinations(range(5), 3))
SUPPORT_COUNT = math.comb(49, 5)
SCHEMA = "rank49-t4-support5-census-v4"
ORBIT_SCHEMA = "rank49-t4-support5-singleton-orbits-v3"
CERTIFICATE_SCHEMA = "rank49-t4-support5-certificate-content-v2"
DEFAULT_MAX_HASSE_ORDER = 4
DEFAULT_BRANCH_CAP = 4096
DEFAULT_ENUM_KERNEL_DIM = 12


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_json(value) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()


def base_revision() -> str:
    commit = f"{GENERATION_BASE_REVISION}^{{commit}}"
    exists = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "cat-file", "-e", commit],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False)
    if exists.returncode != 0:
        raise ValueError(f"fixed generation base does not exist: {GENERATION_BASE_REVISION}")
    ancestor = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "merge-base", "--is-ancestor",
         GENERATION_BASE_REVISION, "HEAD"],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False)
    if ancestor.returncode != 0:
        raise ValueError(
            f"fixed generation base is not an ancestor of HEAD: {GENERATION_BASE_REVISION}")
    return GENERATION_BASE_REVISION


def bits(x: int):
    while x:
        q = x & -x
        yield q.bit_length() - 1
        x ^= q


def bitset_hex(x: int, width: int) -> str:
    return x.to_bytes((width + 7) // 8, "little").hex()


def bitset_from_hex(value: str) -> int:
    return int.from_bytes(bytes.fromhex(value), "little")


def parity_pair(x: int, y: int) -> int:
    return (x & y).bit_count() & 1


def read_scheme(path: Path):
    raw = path.read_bytes()
    digest = sha256_bytes(raw)
    if digest != SOURCE_SHA256:
        raise ValueError(f"source SHA-256 mismatch: {digest}")
    tokens = raw.split()
    if len(tokens) != 4 + 3 * 49 * 16:
        raise ValueError(f"wrong token count: {len(tokens)}")
    try:
        values = [int(token) for token in tokens]
    except ValueError as exc:
        raise ValueError("non-integer source token") from exc
    if values[:4] != [4, 4, 4, 49]:
        raise ValueError(f"wrong source header: {values[:4]}")
    payload = values[4:]
    if any(value not in (0, 1) for value in payload):
        raise ValueError("source is not binary")
    modes = []
    offset = 0
    for _ in range(3):
        mode = []
        for _ in range(49):
            factor = 0
            for coordinate in range(16):
                factor |= payload[offset] << coordinate
                offset += 1
            mode.append(factor)
        modes.append(mode)
    terms = list(zip(*modes))
    return raw, terms


def transpose(a: int) -> int:
    return sum(((a >> (4 * i + j)) & 1) << (4 * j + i)
               for i in range(4) for j in range(4))


def matmul(a: int, b: int) -> int:
    out = 0
    rows = [(b >> (4 * i)) & 15 for i in range(4)]
    for i in range(4):
        selector = (a >> (4 * i)) & 15
        row = 0
        for j in range(4):
            if (selector >> j) & 1:
                row ^= rows[j]
        out |= row << (4 * i)
    return out


def oriented_terms(terms):
    return {
        "abc": terms,
        "bca": [(v, w, u) for u, v, w in terms],
        "cab": [(w, u, v) for u, v, w in terms],
        "acb": [(transpose(w), transpose(v), transpose(u)) for u, v, w in terms],
        "cba": [(transpose(v), transpose(u), transpose(w)) for u, v, w in terms],
        "bac": [(transpose(u), transpose(w), transpose(v)) for u, v, w in terms],
    }


def inverse_orient_variation(name: str, delta):
    u, v, w = delta
    if name == "abc":
        return u, v, w
    if name == "bca":
        return w, u, v
    if name == "cab":
        return v, w, u
    if name == "acb":
        return transpose(w), transpose(v), transpose(u)
    if name == "cba":
        return transpose(v), transpose(u), transpose(w)
    if name == "bac":
        return transpose(u), transpose(w), transpose(v)
    raise ValueError(name)


def outer3(a: int, b: int, c: int) -> int:
    out = 0
    for i in bits(a):
        for j in bits(b):
            base = 256 * i + 16 * j
            for k in bits(c):
                out ^= 1 << (base + k)
    return out


def source_facts(terms):
    represented = 0
    evaluated = []
    for u, v, w in terms:
        if not u or not v or not w:
            raise ValueError("zero source factor")
        tensor = outer3(u, v, w)
        represented ^= tensor
        evaluated.append(tensor)
    target = 0
    for a in range(4):
        for b in range(4):
            for c in range(4):
                i = 4 * a + b
                j = 4 * b + c
                k = 4 * c + a
                target ^= 1 << (256 * i + 16 * j + k)
    if represented != target:
        raise ValueError("source fails Brent equations")
    if len(set(evaluated)) != 49:
        raise ValueError("source evaluated terms are not pairwise distinct")
    return {
        "brent_equations_checked": 4096,
        "brent_residual_weight": (represented ^ target).bit_count(),
        "nonzero_evaluated_terms": 49,
        "pairwise_distinct_evaluated_terms": True,
        "distinct_nonzero_factor_counts": [len(set(term[m] for term in terms)) for m in range(3)],
        "target_weight": target.bit_count(),
    }


def derivative_columns(term):
    u, v, w = term
    return ([outer3(1 << e, v, w) for e in range(16)]
            + [outer3(u, 1 << e, w) for e in range(16)]
            + [outer3(u, v, 1 << e) for e in range(16)])


def add_plain(basis: dict[int, int], x: int) -> bool:
    while x:
        p = x.bit_length() - 1
        old = basis.get(p)
        if old is None:
            basis[p] = x
            return True
        x ^= old
    return False


def rank_vectors(vectors) -> int:
    basis = {}
    for vector in vectors:
        add_plain(basis, vector)
    return len(basis)


def multiply_columns(columns, coefficients: int) -> int:
    out = 0
    for index in bits(coefficients):
        out ^= columns[index]
    return out


def tagged_elimination(columns):
    basis = {}
    dependencies = []
    pivot_columns = []
    for index, column in enumerate(columns):
        x = column
        tag = 1 << index
        while x:
            p = x.bit_length() - 1
            old = basis.get(p)
            if old is None:
                basis[p] = (x, tag)
                pivot_columns.append(index)
                break
            x ^= old[0]
            tag ^= old[1]
        if not x:
            if not tag or multiply_columns(columns, tag):
                raise AssertionError("invalid kernel dependency")
            dependencies.append(tag)
    if rank_vectors(dependencies) != len(dependencies):
        raise AssertionError("dependent kernel certificate")
    return basis, dependencies, pivot_columns


def solve_with_basis(basis, target: int):
    x = target
    tag = 0
    while x:
        p = x.bit_length() - 1
        old = basis.get(p)
        if old is None:
            return None
        x ^= old[0]
        tag ^= old[1]
    return tag


def rref_vectors_from_basis(basis):
    rows = {p: value[0] if isinstance(value, tuple) else value
            for p, value in basis.items()}
    pivots = sorted(rows)
    for i, p in enumerate(pivots):
        low = rows[p]
        for q in pivots[i + 1:]:
            if (rows[q] >> p) & 1:
                rows[q] ^= low
    for p, row in rows.items():
        if ((row >> p) & 1) != 1:
            raise AssertionError("bad RREF pivot")
        for q in pivots:
            if q != p and ((row >> q) & 1):
                raise AssertionError("uncleared RREF pivot")
    return rows


def canonical_remainder(rref, target: int) -> int:
    out = target
    for p, row in rref.items():
        if (out >> p) & 1:
            out ^= row
    return out


def left_null_witness(columns, basis, target: int) -> int:
    rref = rref_vectors_from_basis(basis)
    residual = canonical_remainder(rref, target)
    if not residual:
        raise ValueError("target is in the column span")
    free = (residual & -residual).bit_length() - 1
    witness = 1 << free
    for pivot, row in rref.items():
        if (row >> free) & 1:
            witness |= 1 << pivot
    if any(parity_pair(witness, column) for column in columns):
        raise AssertionError("left-null witness does not annihilate matrix")
    if parity_pair(witness, target) != 1:
        raise AssertionError("left-null witness misses target")
    return witness


def local_reduced_block(term):
    columns = derivative_columns(term)
    basis = {}
    kept = []
    for original_index, original in enumerate(columns):
        x = original
        tag = 1 << len(kept)
        while x:
            p = x.bit_length() - 1
            old = basis.get(p)
            if old is None:
                basis[p] = (x, tag)
                kept.append(original_index)
                break
            x ^= old[0]
            tag ^= old[1]
    if len(kept) != 46:
        raise AssertionError(f"local derivative rank {len(kept)}")

    def coordinates(image: int) -> int:
        x = image
        tag = 0
        while x:
            p = x.bit_length() - 1
            old = basis.get(p)
            if old is None:
                raise ValueError("image outside local derivative range")
            x ^= old[0]
            tag ^= old[1]
        return tag

    reduced = [columns[index] for index in kept]
    deleted = [index for index in range(48) if index not in set(kept)]
    return reduced, kept, deleted, coordinates


def variation_image(term, delta) -> int:
    u, v, w = term
    du, dv, dw = delta
    return outer3(du, v, w) ^ outer3(u, dv, w) ^ outer3(u, v, dw)


def quotient_sandwich_vectors(terms, coordinate_maps):
    vectors = []
    for kind in range(3):
        for p in range(4):
            for q in range(4):
                elementary = 1 << (4 * p + q)
                packed = 0
                for slot, (term, coordinates) in enumerate(zip(terms, coordinate_maps)):
                    u, v, w = term
                    if kind == 0:
                        delta = matmul(elementary, u), 0, matmul(w, elementary)
                    elif kind == 1:
                        delta = matmul(u, elementary), matmul(elementary, v), 0
                    else:
                        delta = 0, matmul(v, elementary), matmul(elementary, w)
                    local = coordinates(variation_image(term, delta))
                    packed |= local << (46 * slot)
                vectors.append(packed)
    basis, _, pivots = tagged_elimination(vectors)
    independent = [vectors[index] for index in pivots]
    if len(independent) != 45 or len(basis) != 45:
        raise AssertionError(f"quotient sandwich rank {len(independent)}")
    return vectors, independent


def three_circuits(values):
    if any(not value for value in values) or len(set(values)) != len(values):
        raise ValueError("three-circuit input is not simple")
    index = {value: i for i, value in enumerate(values)}
    result = []
    for i in range(len(values)):
        for j in range(i + 1, len(values)):
            k = index.get(values[i] ^ values[j])
            if k is not None and j < k:
                result.append((i, j, k))
    return result


def motif_witnesses(terms):
    us = [term[0] for term in terms]
    vs = [term[1] for term in terms]
    ws = [term[2] for term in terms]
    circuits = three_circuits(vs)
    by_term = defaultdict(list)
    for circuit in circuits:
        for shared in circuit:
            by_term[shared].append(circuit)
    result = set()
    for shared, containing in by_term.items():
        for first0, second0 in itertools.combinations(containing, 2):
            if set(first0) & set(second0) != {shared}:
                continue
            for first, second in ((first0, second0), (second0, first0)):
                first_other = sorted(set(first) - {shared})
                second_other = sorted(set(second) - {shared})
                for a, d in (tuple(first_other), tuple(reversed(first_other))):
                    for b, c in (tuple(second_other), tuple(reversed(second_other))):
                        if us[b] ^ us[d] ^ us[shared]:
                            continue
                        if ws[a] ^ ws[c] ^ ws[shared]:
                            continue
                        result.add((a, b, c, d, shared))
    return circuits, sorted(result)


def circuit_and_motif_data(terms):
    factor_circuits = []
    triple_code = {}
    for mode in range(3):
        circuits = three_circuits([term[mode] for term in terms])
        factor_circuits.append(circuits)
        for circuit in circuits:
            triple_code[circuit] = triple_code.get(circuit, 0) | (1 << mode)
    by_support = defaultdict(list)
    per_orientation = {}
    all_oriented = oriented_terms(terms)
    for orientation_index, name in enumerate(ORIENTATION_NAMES):
        middle_circuits, witnesses = motif_witnesses(all_oriented[name])
        supports = set()
        for labels in witnesses:
            support = tuple(sorted(labels))
            supports.add(support)
            by_support[support].append({"orientation": name, "labels": list(labels)})
        per_orientation[name] = {
            "middle_factor_three_circuit_count": len(middle_circuits),
            "ordered_witness_count": len(witnesses),
            "support_count": len(supports),
        }
    for support in by_support:
        by_support[support].sort(key=lambda item: (ORIENTATION_NAMES.index(item["orientation"]), item["labels"]))
    return factor_circuits, triple_code, by_support, per_orientation


def support_circuit_signature(support, triple_code):
    packed = 0
    readable = {"U": [], "V": [], "W": []}
    for local_index, local_triple in enumerate(LOCAL_TRIPLES):
        actual = tuple(support[index] for index in local_triple)
        code = triple_code.get(actual, 0)
        packed |= code << (3 * local_index)
        for mode, name in enumerate(("U", "V", "W")):
            if (code >> mode) & 1:
                readable[name].append(list(actual))
    return packed, readable


def support_rank(blocks, support):
    basis = {}
    for slot in support:
        for column in blocks[slot]:
            add_plain(basis, column)
    return len(basis)


def derivative_block_circuit(blocks, support, rank, kernel_basis=None):
    if rank == 230:
        return {
            "signature": "I:r230",
            "kind": "independent",
            "combined_rank": 230,
            "rank_deficiency": 0,
            "is_minimal_dependence": False,
        }
    proper_ranks = []
    for omitted in range(5):
        columns = [column for local, slot in enumerate(support) if local != omitted
                   for column in blocks[slot]]
        proper_ranks.append(rank_vectors(columns))
    if kernel_basis is None:
        columns = [column for slot in support for column in blocks[slot]]
        _, kernel_basis, _ = tagged_elimination(columns)
    kernel_block_masks = []
    for vector in kernel_basis:
        mask = 0
        for local in range(5):
            if (vector >> (46 * local)) & ((1 << 46) - 1):
                mask |= 1 << local
        kernel_block_masks.append(mask)
    deficiency = 230 - rank
    minimal = all(value == 184 for value in proper_ranks) and all(mask == 31 for mask in kernel_block_masks)
    signature = (f"C:def{deficiency}:r{rank}:p" + ",".join(map(str, proper_ranks))
                 + ":k" + ",".join(f"{mask:02x}" for mask in kernel_block_masks))
    return {
        "signature": signature,
        "kind": "minimal_dependent" if minimal else "dependent_not_verified_minimal",
        "combined_rank": rank,
        "rank_deficiency": deficiency,
        "proper_four_block_ranks_in_omitted_local_slot_order": proper_ranks,
        "kernel_block_support_masks_hex": [f"{mask:02x}" for mask in kernel_block_masks],
        "is_minimal_dependence": minimal,
    }


def restricted_gauge_basis(independent_gauge, support):
    inside = 0
    for slot in support:
        inside |= ((1 << 46) - 1) << (46 * slot)
    all_mask = (1 << (49 * 46)) - 1
    outside = all_mask ^ inside
    projected = [vector & outside for vector in independent_gauge]
    _, dependencies, _ = tagged_elimination(projected)
    result = []
    for dependency in dependencies:
        vector = multiply_columns(independent_gauge, dependency)
        if vector & outside:
            raise AssertionError("gauge intersection vector leaks outside support")
        local = 0
        for local_slot, global_slot in enumerate(support):
            local |= ((vector >> (46 * global_slot)) & ((1 << 46) - 1)) << (46 * local_slot)
        result.append(local)
    if rank_vectors(result) != len(result):
        raise AssertionError("dependent gauge-intersection basis")
    return result


def quotient_complement(kernel_basis, gauge_basis):
    span = {}
    for vector in gauge_basis:
        if not add_plain(span, vector):
            raise AssertionError("dependent restricted gauge basis")
    normal = []
    for vector in kernel_basis:
        if add_plain(span, vector):
            normal.append(vector)
    if len(normal) != len(kernel_basis) - len(gauge_basis):
        raise AssertionError("wrong normal complement dimension")
    return normal


def reduced_support_to_raw(support, reduced: int, kept_indices):
    result = []
    for local_slot, global_slot in enumerate(support):
        local = (reduced >> (46 * local_slot)) & ((1 << 46) - 1)
        raw = 0
        for index in bits(local):
            raw |= 1 << kept_indices[global_slot][index]
        result.append((raw & 0xFFFF, (raw >> 16) & 0xFFFF, (raw >> 32) & 0xFFFF))
    return result


def reduced_global_to_raw(reduced: int, kept_indices):
    result = []
    for slot in range(49):
        local = (reduced >> (46 * slot)) & ((1 << 46) - 1)
        raw = 0
        for index in bits(local):
            raw |= 1 << kept_indices[slot][index]
        result.append((raw & 0xFFFF, (raw >> 16) & 0xFFFF, (raw >> 32) & 0xFFFF))
    return result


def raw_variation_record(support, variation):
    return [{"slot": slot, "U": f"{delta[0]:04x}", "V": f"{delta[1]:04x}", "W": f"{delta[2]:04x}"}
            for slot, delta in zip(support, variation)]


def quadratic_coefficient(terms, support, variation):
    out = 0
    for slot, (du, dv, dw) in zip(support, variation):
        u, v, w = terms[slot]
        out ^= outer3(du, dv, w)
        out ^= outer3(du, v, dw)
        out ^= outer3(u, dv, dw)
    return out


def mixed_quadratic_coefficient(terms, support, first, second):
    out = 0
    for slot, d, e in zip(support, first, second):
        u, v, w = terms[slot]
        du, dv, dw = d
        eu, ev, ew = e
        out ^= outer3(du, ev, w) ^ outer3(eu, dv, w)
        out ^= outer3(du, v, ew) ^ outer3(eu, v, dw)
        out ^= outer3(u, dv, ew) ^ outer3(u, ev, dw)
    return out


def obstruction_certificate(columns, basis, target, width):
    solution = solve_with_basis(basis, target)
    if solution is not None:
        if multiply_columns(columns, solution) != target:
            raise AssertionError("bad positive obstruction preimage")
        return {
            "status": "vanishes",
            "preimage_reduced_lsb_hex": bitset_hex(solution, len(columns)),
            "preimage_weight": solution.bit_count(),
        }
    witness = left_null_witness(columns, basis, target)
    return {
        "status": "nonzero",
        "left_null_lsb_hex": bitset_hex(witness, width),
        "left_null_weight": witness.bit_count(),
        "pairing": 1,
    }


def obstruction_ideal(terms, support, normal_basis, kept_indices, columns, basis):
    variations = [reduced_support_to_raw(support, vector, kept_indices) for vector in normal_basis]
    rref = rref_vectors_from_basis(basis)
    monomials = []
    residuals = []
    for i in range(len(normal_basis)):
        for j in range(i, len(normal_basis)):
            monomials.append([i, j])
            if i == j:
                tensor = quadratic_coefficient(terms, support, variations[i])
            else:
                tensor = mixed_quadratic_coefficient(terms, support, variations[i], variations[j])
            residuals.append(canonical_remainder(rref, tensor))
    equations_by_coordinate = {}
    for monomial_index, residual in enumerate(residuals):
        for coordinate in bits(residual):
            equations_by_coordinate[coordinate] = equations_by_coordinate.get(coordinate, 0) ^ (1 << monomial_index)
    equation_basis = {}
    for equation in equations_by_coordinate.values():
        add_plain(equation_basis, equation)
    equations = sorted(equation_basis.values())
    return {
        "coefficient_field": "F2",
        "variables": [f"z{i}" for i in range(len(normal_basis))],
        "monomials": monomials,
        "equation_coefficient_bitsets_lsb_hex": [bitset_hex(eq, len(monomials)) for eq in equations],
        "independent_equation_count": len(equations),
        "status": "full_projective_quadratic_ideal_emitted_geometry_unknown",
    }


def tangent_for_witness(terms, support, witness, coordinate_maps):
    name = witness["orientation"]
    labels = witness["labels"]
    oriented = oriented_terms(terms)[name]
    a, b, c, d, e = labels
    coefficient_a = (outer3(oriented[d][0], oriented[a][1], oriented[a][2])
                     ^ outer3(oriented[d][0], oriented[d][1], oriented[d][2])
                     ^ outer3(oriented[d][0], oriented[e][1], oriented[e][2]))
    coefficient_b = (outer3(oriented[b][0], oriented[b][1], oriented[c][2])
                     ^ outer3(oriented[b][0], oriented[c][1], oriented[c][2])
                     ^ outer3(oriented[d][0], oriented[d][1], oriented[a][2] ^ oriented[d][2])
                     ^ outer3(oriented[e][0], oriented[e][1], oriented[c][2]))
    coefficient_c = (outer3(oriented[d][0], oriented[d][1], oriented[a][2] ^ oriented[d][2])
                     ^ outer3(oriented[d][0], oriented[e][1], oriented[c][2]))
    if coefficient_a != coefficient_b or coefficient_a != coefficient_c:
        raise AssertionError("paired-T3 coefficient equality failed")
    oriented_delta = {
        a: (oriented[d][0], 0, 0),
        b: (0, 0, oriented[c][2]),
        c: (oriented[b][0], 0, 0),
        d: (oriented[d][0], 0, oriented[a][2] ^ oriented[d][2]),
        e: (oriented[d][0], 0, oriented[c][2]),
    }
    original_delta = {slot: inverse_orient_variation(name, oriented_delta[slot]) for slot in labels}
    packed = 0
    for local_slot, slot in enumerate(support):
        delta = original_delta[slot]
        local = coordinate_maps[slot](variation_image(terms[slot], delta))
        packed |= local << (46 * local_slot)
    return packed, [original_delta[slot] for slot in support], coefficient_a


def _poly_factor(base, s_delta, t_delta):
    result = {(0, 0): base}
    if s_delta:
        result[(1, 0)] = result.get((1, 0), 0) ^ s_delta
    if t_delta:
        result[(0, 1)] = result.get((0, 1), 0) ^ t_delta
    return {key: value for key, value in result.items() if value}


def _expand_tensor_polynomial(first, second, third):
    result = {}
    for (i, j), u in first.items():
        for (k, ell), v in second.items():
            for (m, n), w in third.items():
                key = (i + k + m, j + ell + n)
                result[key] = result.get(key, 0) ^ outer3(u, v, w)
    return {key: value for key, value in result.items() if value}


def _laurent_factor(base, s_delta, t_delta):
    result = {0: base ^ s_delta ^ t_delta}
    if s_delta:
        result[-1] = result.get(-1, 0) ^ s_delta
    if t_delta:
        result[1] = result.get(1, 0) ^ t_delta
    return {key: value for key, value in result.items() if value}


def _expand_tensor_laurent(first, second, third):
    result = {}
    for i, u in first.items():
        for j, v in second.items():
            for k, w in third.items():
                exponent = i + j + k
                result[exponent] = result.get(exponent, 0) ^ outer3(u, v, w)
    return {key: value for key, value in result.items() if value}


def canonical_t3_update_certificate(terms, support, witness, section_variation):
    name = witness["orientation"]
    labels = tuple(witness["labels"])
    a, b, c, d, e = labels
    oriented = oriented_terms(terms)[name]
    zero = (0, 0, 0)
    s_oriented = {
        a: (oriented[d][0], 0, 0),
        d: (oriented[d][0], 0, 0),
        e: (oriented[d][0], 0, 0),
    }
    t_oriented = {
        b: (0, 0, oriented[c][2]),
        c: (oriented[b][0], 0, 0),
        d: (0, 0, oriented[a][2] ^ oriented[d][2]),
        e: (0, 0, oriented[c][2]),
    }
    s_original = {slot: inverse_orient_variation(name, s_oriented.get(slot, zero)) for slot in support}
    t_original = {slot: inverse_orient_variation(name, t_oriented.get(slot, zero)) for slot in support}
    t3_variation = [tuple(x ^ y for x, y in zip(s_original[slot], t_original[slot])) for slot in support]

    polynomial = {}
    base_tensor = 0
    for slot in support:
        base = terms[slot]
        ds = s_original[slot]
        dt = t_original[slot]
        expanded = _expand_tensor_polynomial(
            _poly_factor(base[0], ds[0], dt[0]),
            _poly_factor(base[1], ds[1], dt[1]),
            _poly_factor(base[2], ds[2], dt[2]))
        for monomial, tensor in expanded.items():
            polynomial[monomial] = polynomial.get(monomial, 0) ^ tensor
        base_tensor ^= outer3(*base)
    polynomial[(0, 0)] = polynomial.get((0, 0), 0) ^ base_tensor
    polynomial = {key: value for key, value in polynomial.items() if value}
    unexpected = sorted(key for key in polynomial if key not in ((1, 0), (0, 1), (1, 1)))
    if unexpected:
        raise AssertionError(f"unexpected T3 polynomial monomials {unexpected}")
    coefficient_a = polynomial.get((1, 0), 0)
    coefficient_b = polynomial.get((0, 1), 0)
    coefficient_c = polynomial.get((1, 1), 0)
    if not coefficient_a or coefficient_a != coefficient_b or coefficient_a != coefficient_c:
        raise AssertionError("independent T3 polynomial replay failed")

    laurent = {}
    for slot in support:
        base = terms[slot]
        ds = s_original[slot]
        dt = t_original[slot]
        expanded = _expand_tensor_laurent(
            _laurent_factor(base[0], ds[0], dt[0]),
            _laurent_factor(base[1], ds[1], dt[1]),
            _laurent_factor(base[2], ds[2], dt[2]))
        for exponent, tensor in expanded.items():
            laurent[exponent] = laurent.get(exponent, 0) ^ tensor
    laurent[0] = laurent.get(0, 0) ^ base_tensor
    laurent_residual_weights = {str(key): value.bit_count() for key, value in sorted(laurent.items())}
    if any(laurent.values()):
        raise AssertionError("exact Laurent replay has a nonzero coordinate")

    scaling = []
    representative_matches = True
    for slot, base, section, t3 in zip(support, (terms[slot] for slot in support), section_variation, t3_variation):
        difference = tuple(x ^ y for x, y in zip(section, t3))
        found = None
        for alpha in range(2):
            for beta in range(2):
                candidate = ((alpha ^ beta) * base[0], alpha * base[1], beta * base[2])
                if candidate == difference:
                    found = alpha, beta
                    break
            if found is not None:
                break
        if found is None:
            raise AssertionError("section/T3 difference is not local scaling")
        alpha, beta = found
        representative_matches &= alpha == 0 and beta == 0
        lambda_exponent = alpha ^ beta
        mu_exponent = alpha
        nu_exponent = -(lambda_exponent + mu_exponent)
        if lambda_exponent + mu_exponent + nu_exponent != 0:
            raise AssertionError("local gauge path does not have product one")
        if ((nu_exponent & 1) != beta):
            raise AssertionError("local gauge path has wrong tangent")
        scaling.append({
            "slot": slot,
            "alpha_UV": alpha,
            "beta_UW": beta,
            "integrated_q_exponents": {
                "U_lambda": lambda_exponent,
                "V_mu": mu_exponent,
                "W_nu": nu_exponent,
                "sum": 0,
            },
        })

    def updates_record(values):
        result = []
        for label, slot in zip("abcde", labels):
            delta = values.get(slot, zero)
            for mode, value in zip(("U", "V", "W"), delta):
                if value:
                    result.append({"label": label, "slot": slot, "factor": mode, "add": f"{value:04x}"})
        return result

    def coefficient_record(value):
        return {
            "lsb_hex": bitset_hex(value, 4096),
            "weight": value.bit_count(),
            "sha256": sha256_bytes(value.to_bytes(512, "little")),
        }

    return {
        "canonical_order_rule": "prefer a witness whose tangent equals the deterministic section; then fixed orientation order and lexicographic labels",
        "orientation": name,
        "labels_abcde": list(labels),
        "oriented_source_factors": [
            {"label": label, "slot": slot, "U": f"{oriented[slot][0]:04x}",
             "V": f"{oriented[slot][1]:04x}", "W": f"{oriented[slot][2]:04x}"}
            for label, slot in zip("abcde", labels)
        ],
        "separate_factor_updates_in_oriented_frame": {
            "s": updates_record(s_oriented),
            "t": updates_record(t_oriented),
        },
        "separate_factor_updates_in_original_coordinate_frame": {
            "s": updates_record(s_original),
            "t": updates_record(t_original),
        },
        "coefficients_in_original_4096_coordinate_frame": {
            "A_s": coefficient_record(coefficient_a),
            "B_t": coefficient_record(coefficient_b),
            "C_st": coefficient_record(coefficient_c),
            "A_equals_B_equals_C": True,
        },
        "independent_bivariate_replay": {
            "coordinates_checked": 4096,
            "unaffected_terms_cancelled_identically": 44,
            "difference": "s*A+t*B+s*t*C",
            "nonzero_monomials": [[i, j] for i, j in sorted(polynomial)],
            "status": "exact_polynomial_identity_verified",
        },
        "independent_laurent_formal_replay": {
            "substitution": "b=1+tau, t=1+b=tau, s=1+b^-1=tau/(1+tau)",
            "coefficient_ring": "F2[b,b^-1], embedded in F2[[tau]] because 1+tau is a unit",
            "residual_weights_by_b_exponent": laurent_residual_weights,
            "coordinates_checked_per_coefficient": 4096,
            "formal_relation_numerator": "tau + tau*(1+tau) + tau^2 = 0",
            "status": "exact_all_coordinate_laurent_and_formal_replay_verified",
        },
        "normal_class_integrability": {
            "status": "normal_class_exact_paired_t3_family",
            "relation": "(1+s)(1+t)=1",
            "raw_section_representative_is_t3_tangent": representative_matches,
            "raw_section_relation": (
                "identical_to_canonical_t3_tangent" if representative_matches
                else "differs_by_displayed_local_scaling_tangent; displayed_product_one_gauge_path_integrates_the_correction"),
            "local_scaling_correction_coefficients": scaling,
            "integrated_gauge_path": "q=1+tau; multiply each original U,V,W factor by q^(U_lambda),q^(V_mu),q^(W_nu)",
        },
    }


def coordinates_in_basis(vectors, target):
    basis, _, _ = tagged_elimination(vectors)
    solution = solve_with_basis(basis, target)
    if solution is None:
        raise AssertionError("target is not in supplied basis span")
    return solution


def hasse_residual(terms, coefficients, order):
    out = 0
    for slot, base in enumerate(terms):
        for i in range(order + 1):
            for j in range(order - i + 1):
                k = order - i - j
                if i >= order or j >= order or k >= order:
                    continue
                first = base[0] if i == 0 else coefficients[i - 1][slot][0]
                second = base[1] if j == 0 else coefficients[j - 1][slot][1]
                third = base[2] if k == 0 else coefficients[k - 1][slot][2]
                if first and second and third:
                    out ^= outer3(first, second, third)
    return out


def bounded_hasse_attempt(terms, first_global, columns, basis, kernel_basis,
                          to_global_raw, max_order, branch_cap, enum_kernel_dim):
    histories = [[first_global]]
    exhaustive = True
    trace = hashlib.sha256()
    levels = []
    for order in range(2, max_order + 1):
        next_histories = []
        failed = 0
        omitted = False
        kernel_count = 1 << len(kernel_basis) if len(kernel_basis) <= enum_kernel_dim else 1
        if len(kernel_basis) > enum_kernel_dim:
            exhaustive = False
            omitted = True
        for history in histories:
            residual = hasse_residual(terms, history, order)
            solution = solve_with_basis(basis, residual)
            trace.update(order.to_bytes(2, "little"))
            trace.update(residual.to_bytes(512, "little"))
            if solution is None:
                failed += 1
                trace.update(b"N")
                continue
            trace.update(b"Y")
            trace.update(bitset_hex(solution, len(columns)).encode())
            choices = [solution]
            if kernel_count > 1:
                choices = []
                for mask in range(kernel_count):
                    candidate = solution
                    for index in bits(mask):
                        candidate ^= kernel_basis[index]
                    choices.append(candidate)
            remaining = branch_cap - len(next_histories)
            if len(choices) > remaining:
                choices = choices[:max(0, remaining)]
                exhaustive = False
                omitted = True
            for choice in choices:
                next_histories.append(history + [to_global_raw(choice)])
            if len(next_histories) >= branch_cap:
                exhaustive = False
                omitted = True
                break
        levels.append({
            "order": order,
            "input_branches": len(histories),
            "failed_branches": failed,
            "surviving_branches": len(next_histories),
            "choices_omitted": omitted,
        })
        histories = next_histories
        if not histories:
            return {
                "status": f"no_lift_order_{order}" if exhaustive else f"unknown_no_survivor_in_bounded_branches_order_{order}",
                "exhaustive_over_prior_affine_choices": exhaustive,
                "levels": levels,
                "trace_sha256": trace.hexdigest(),
            }
    return {
        "status": f"lifted_through_order_{max_order}",
        "integrability_claim": False,
        "exhaustive_over_affine_choices_through_bound": exhaustive,
        "surviving_branches": len(histories),
        "levels": levels,
        "trace_sha256": trace.hexdigest(),
    }


def orientation_mask(witnesses):
    result = 0
    for witness in witnesses:
        result |= 1 << ORIENTATION_NAMES.index(witness["orientation"])
    return result


def witness_signature(witnesses):
    if not witnesses:
        return b"\0" * 8
    return hashlib.sha256(canonical_json(witnesses)).digest()[:8]


def tensor_vector_digest(vectors):
    digest = hashlib.sha256()
    for vector in vectors:
        digest.update(vector.to_bytes(512, "little"))
    return digest.hexdigest()


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def fsync_directory(path: Path):
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
    descriptor = os.open(path, flags)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def same_directory_temporary(directory: Path, prefix: str, suffix: str) -> Path:
    directory.mkdir(parents=True, exist_ok=True)
    descriptor, name = tempfile.mkstemp(dir=directory, prefix=prefix, suffix=suffix)
    os.close(descriptor)
    return Path(name)


def durable_atomic_write(path: Path, data: bytes):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = same_directory_temporary(path.parent, f".{path.name}.", ".tmp")
    try:
        with temporary.open("wb") as stream:
            stream.write(data)
            stream.flush()
            os.fchmod(stream.fileno(), 0o644)
            os.fsync(stream.fileno())
        os.replace(temporary, path)
        fsync_directory(path.parent)
    finally:
        temporary.unlink(missing_ok=True)


def content_addressed_orbit_relative(compressed_sha256: str) -> Path:
    if len(compressed_sha256) != 64 or any(c not in "0123456789abcdef" for c in compressed_sha256):
        raise ValueError("invalid singleton orbit compressed SHA-256")
    return ORBIT_DIRECTORY_RELATIVE / f"support5_orbits-{compressed_sha256}.jsonl.gz"


def referenced_orbit_path(metadata) -> Path:
    compressed_sha256 = metadata.get("compressed_sha256", "")
    expected_relative = content_addressed_orbit_relative(compressed_sha256)
    if metadata.get("relative_path") != expected_relative.as_posix():
        raise ValueError("singleton orbit reference is stale or not content-addressed")
    expected_addressing = {
        "algorithm": "sha256",
        "digest_of": "complete deterministic gzip bytes",
        "immutable_filename": True,
    }
    if metadata.get("content_addressing") != expected_addressing:
        raise ValueError("singleton orbit content-addressing metadata mismatch")
    path = REPO_ROOT / expected_relative
    if path.parent != ORBIT_DIRECTORY_DEFAULT:
        raise ValueError("singleton orbit reference escapes the owned artifact directory")
    if not path.is_file():
        raise ValueError("referenced singleton orbit payload is missing")
    return path


def publish_content_addressed_orbit(temporary: Path, metadata):
    relative = content_addressed_orbit_relative(metadata["compressed_sha256"])
    if metadata.get("relative_path") != relative.as_posix():
        raise ValueError("generated singleton orbit reference mismatch")
    target = REPO_ROOT / relative
    if temporary.parent != target.parent:
        raise ValueError("singleton orbit temporary file is not in the publication directory")
    os.chmod(temporary, 0o444)
    with temporary.open("rb") as stream:
        os.fsync(stream.fileno())
    reused = False
    try:
        os.link(temporary, target)
    except FileExistsError:
        if target.stat().st_size != metadata["compressed_byte_count"]:
            raise ValueError("content-addressed singleton orbit filename has the wrong size")
        if file_sha256(target) != metadata["compressed_sha256"]:
            raise ValueError("content-addressed singleton orbit filename has the wrong content")
        reused = True
    else:
        fsync_directory(target.parent)
    temporary.unlink()
    fsync_directory(target.parent)
    return target, reused


def obsolete_orbit_paths(current: Path):
    if not ORBIT_DIRECTORY_DEFAULT.is_dir():
        return []
    return sorted(
        path.relative_to(REPO_ROOT).as_posix()
        for path in ORBIT_DIRECTORY_DEFAULT.glob("support5_orbits*.jsonl.gz")
        if path != current)


def singleton_orbit_body(lex_id, support, factor_signature, positive_record,
                         certificate_content_sha256):
    if positive_record is None:
        rank = 230
        normal_dimension = 0
        derivative_signature = "I:r230"
        f2_status = "no_projective_normal_direction"
        fbar_status = "no_projective_normal_direction"
        same_obstruction = "not_applicable_no_normal_direction"
        full_obstruction = "not_applicable_no_normal_direction"
        same_solver = "not_applicable_no_normal_direction"
        full_solver = "not_applicable_no_normal_direction"
    else:
        rank = positive_record["reduced_rank"]
        normal_dimension = positive_record["normal_dimension"]
        derivative_signature = positive_record["derivative_block_circuit"]["signature"]
        directions = positive_record["projective_directions"]
        direction = directions["F2"]["directions"][0]
        f2_status = "exactly_one_F2_projective_direction"
        fbar_status = directions["Fbar2"]["status"]
        same_obstruction = direction["same_support_quadratic_obstruction"]["status"]
        full_obstruction = direction["full_coordinate_quadratic_obstruction"]["status"]
        same_solver = direction["lifting"]["same_support"]["status"]
        full_solver = direction["lifting"]["full_coordinate"]["status"]
    return {
        "census_certificate_content_sha256": certificate_content_sha256,
        "combinadic_lex_id": lex_id,
        "support0": list(support),
        "orbit_size": 1,
        "orbit_model": "identity_action_no_stabilizer_reduction",
        "reduced_rank": rank,
        "normal_dimension": normal_dimension,
        "factor_circuit_signature_30bit_hex": f"{factor_signature:08x}",
        "derivative_block_circuit_signature": derivative_signature,
        "projective_direction_status": {"F2": f2_status, "Fbar2": fbar_status},
        "quadratic_obstruction_status": {
            "same_support": same_obstruction,
            "full_coordinate": full_obstruction,
            "scope": "deterministic_normal_section_representative",
        },
        "solver_status": {
            "same_support": same_solver,
            "full_coordinate": full_solver,
            "integrability_scope": "normal_class",
        },
    }


def write_singleton_orbits(path: Path, records, triple_code, classification_sha256,
                           certificate_content_sha256):
    positive = {tuple(record["support0"]): record for record in records}
    uncompressed = hashlib.sha256()
    body_stream = hashlib.sha256()
    count = 0
    uncompressed_bytes = 0
    with path.open("wb") as raw:
        with gzip.GzipFile(filename="", mode="wb", fileobj=raw, compresslevel=9, mtime=0) as stream:
            for lex_id, support in enumerate(itertools.combinations(range(49), 5)):
                factor_signature, _ = support_circuit_signature(support, triple_code)
                record = singleton_orbit_body(
                    lex_id, support, factor_signature, positive.get(support),
                    certificate_content_sha256)
                body_bytes = canonical_json(record)
                line = body_bytes + b"\n"
                stream.write(line)
                uncompressed.update(line)
                body_stream.update(len(body_bytes).to_bytes(4, "little"))
                body_stream.update(body_bytes)
                uncompressed_bytes += len(line)
                count += 1
        raw.flush()
        os.fsync(raw.fileno())
    if count != SUPPORT_COUNT:
        raise AssertionError("wrong singleton orbit record count")
    compressed_sha256 = file_sha256(path)
    body_stream_sha256 = body_stream.hexdigest()
    relative_path = content_addressed_orbit_relative(compressed_sha256)
    return {
        "schema": ORBIT_SCHEMA,
        "relative_path": relative_path.as_posix(),
        "content_addressing": {
            "algorithm": "sha256",
            "digest_of": "complete deterministic gzip bytes",
            "immutable_filename": True,
        },
        "format": "canonical JSON Lines, one identity-action singleton support orbit per line",
        "compression": {"algorithm": "gzip", "level": 9, "mtime": 0, "header_filename": ""},
        "row_authentication": {
            "field": "census_certificate_content_sha256",
            "value": certificate_content_sha256,
            "meaning": "non-self-referential digest of the census certificate content manifest; repeated by every row",
            "individual_random_row_hashes": False,
        },
        "integrity_model": "gzip SHA256 plus complete canonical uncompressed and length-prefixed body-stream SHA256; full streaming structure/order validation by combinadic ID",
        "record_count": count,
        "first_combinadic_lex_id": 0,
        "last_combinadic_lex_id": count - 1,
        "first_support0": [0, 1, 2, 3, 4],
        "last_support0": [44, 45, 46, 47, 48],
        "uncompressed_byte_count": uncompressed_bytes,
        "compressed_byte_count": path.stat().st_size,
        "uncompressed_sha256": uncompressed.hexdigest(),
        "compressed_sha256": compressed_sha256,
        "length_prefixed_body_stream_sha256": body_stream_sha256,
        "census_certificate_content_sha256": certificate_content_sha256,
        "census_classification_sha256": classification_sha256,
        "cross_digest_definition": "SHA256(classification || certificate_content || length_prefixed_body_stream), raw digest bytes",
        "cross_digest_sha256": sha256_bytes(
            bytes.fromhex(classification_sha256)
            + bytes.fromhex(certificate_content_sha256)
            + bytes.fromhex(body_stream_sha256)),
    }


def validate_singleton_orbits(path: Path, metadata):
    if file_sha256(path) != metadata["compressed_sha256"]:
        raise ValueError("singleton orbit compressed SHA-256 mismatch")
    if path.stat().st_size != metadata["compressed_byte_count"]:
        raise ValueError("singleton orbit compressed size mismatch")
    certificate_content_sha256 = metadata["census_certificate_content_sha256"]
    uncompressed = hashlib.sha256()
    body_stream = hashlib.sha256()
    expected_supports = itertools.combinations(range(49), 5)
    count = 0
    uncompressed_bytes = 0
    required_keys = {
        "census_certificate_content_sha256", "combinadic_lex_id", "support0",
        "orbit_size", "orbit_model", "reduced_rank", "normal_dimension",
        "factor_circuit_signature_30bit_hex", "derivative_block_circuit_signature",
        "projective_direction_status", "quadratic_obstruction_status", "solver_status",
    }
    with gzip.open(path, "rb") as stream:
        for line in stream:
            uncompressed.update(line)
            uncompressed_bytes += len(line)
            if not line.endswith(b"\n"):
                raise ValueError("unterminated singleton orbit JSON line")
            record = json.loads(line)
            body_bytes = canonical_json(record)
            if line != body_bytes + b"\n":
                raise ValueError("noncanonical singleton orbit JSON line")
            if set(record) != required_keys:
                raise ValueError(f"singleton orbit record schema mismatch at line {count}")
            try:
                expected_support = next(expected_supports)
            except StopIteration as exc:
                raise ValueError("too many singleton orbit records") from exc
            if record["combinadic_lex_id"] != count or tuple(record["support0"]) != expected_support:
                raise ValueError(f"singleton orbit coverage/order mismatch at line {count}")
            if record["orbit_size"] != 1 or record["orbit_model"] != "identity_action_no_stabilizer_reduction":
                raise ValueError(f"singleton orbit structural mismatch at line {count}")
            if record["census_certificate_content_sha256"] != certificate_content_sha256:
                raise ValueError(f"singleton orbit certificate reference mismatch at line {count}")
            rank = record["reduced_rank"]
            normal = record["normal_dimension"]
            derivative = record["derivative_block_circuit_signature"]
            if (rank, normal) == (230, 0):
                if derivative != "I:r230":
                    raise ValueError(f"independent derivative signature mismatch at line {count}")
            elif (rank, normal) == (229, 1):
                if derivative != "C:def1:r229:p184,184,184,184,184:k1f":
                    raise ValueError(f"exceptional derivative signature mismatch at line {count}")
            else:
                raise ValueError(f"rank/normal structural mismatch at line {count}")
            factor_signature = record["factor_circuit_signature_30bit_hex"]
            if len(factor_signature) != 8 or any(c not in "0123456789abcdef" for c in factor_signature):
                raise ValueError(f"factor signature encoding mismatch at line {count}")
            if set(record["projective_direction_status"]) != {"F2", "Fbar2"}:
                raise ValueError(f"projective status schema mismatch at line {count}")
            obstruction = record["quadratic_obstruction_status"]
            if set(obstruction) != {"same_support", "full_coordinate", "scope"}:
                raise ValueError(f"obstruction status schema mismatch at line {count}")
            solver = record["solver_status"]
            if set(solver) != {"same_support", "full_coordinate", "integrability_scope"}:
                raise ValueError(f"solver status schema mismatch at line {count}")
            body_stream.update(len(body_bytes).to_bytes(4, "little"))
            body_stream.update(body_bytes)
            count += 1
    try:
        next(expected_supports)
    except StopIteration:
        pass
    else:
        raise ValueError("too few singleton orbit records")
    observed = {
        "record_count": count,
        "uncompressed_byte_count": uncompressed_bytes,
        "uncompressed_sha256": uncompressed.hexdigest(),
        "length_prefixed_body_stream_sha256": body_stream.hexdigest(),
    }
    for key, value in observed.items():
        if metadata.get(key) != value:
            raise ValueError(f"singleton orbit metadata mismatch for {key}")
    expected_cross = sha256_bytes(
        bytes.fromhex(metadata["census_classification_sha256"])
        + bytes.fromhex(certificate_content_sha256)
        + bytes.fromhex(observed["length_prefixed_body_stream_sha256"]))
    if metadata.get("cross_digest_sha256") != expected_cross:
        raise ValueError("singleton orbit cross-digest mismatch")
    return observed


def support_positive_record(candidate, terms, blocks, kept_indices, coordinate_maps,
                            independent_gauge, motif_by_support, triple_code,
                            full_columns, full_basis, full_kernel,
                            max_hasse_order, branch_cap, enum_kernel_dim):
    support = candidate["support"]
    support_columns = [column for slot in support for column in blocks[slot]]
    support_basis, kernel_basis, pivot_columns = tagged_elimination(support_columns)
    rank = len(support_basis)
    gauge_basis = restricted_gauge_basis(independent_gauge, support)
    for gauge in gauge_basis:
        if multiply_columns(support_columns, gauge):
            raise AssertionError("restricted gauge is not in restricted kernel")
    normal_basis = quotient_complement(kernel_basis, gauge_basis)
    if len(normal_basis) != candidate["normal_dimension"]:
        raise AssertionError("normal dimension changed during reconstruction")
    circuit_signature, readable_circuits = support_circuit_signature(support, triple_code)
    witnesses = motif_by_support.get(support, [])
    motif_direction_masks = set()
    witnesses_by_normal_mask = defaultdict(list)
    witness_records = []
    spanning = gauge_basis + normal_basis
    for witness in witnesses:
        tangent, raw_tangent, common_coefficient = tangent_for_witness(terms, support, witness, coordinate_maps)
        if multiply_columns(support_columns, tangent):
            raise AssertionError("T3 tangent is not in restricted kernel")
        coordinates = coordinates_in_basis(spanning, tangent)
        normal_coordinates = coordinates >> len(gauge_basis)
        if normal_coordinates:
            motif_direction_masks.add(normal_coordinates)
            witnesses_by_normal_mask[normal_coordinates].append(witness)
        witness_records.append({
            **witness,
            "tangent_reduced_lsb_hex": bitset_hex(tangent, 230),
            "normal_coordinate_mask": normal_coordinates,
            "raw_tangent": raw_variation_record(support, raw_tangent),
            "coefficient_A_eq_B_eq_C_weight": common_coefficient.bit_count(),
            "coefficient_A_eq_B_eq_C_sha256": sha256_bytes(common_coefficient.to_bytes(512, "little")),
        })
    pivot_rows = sorted(support_basis)
    pivot_minor_columns = pivot_columns
    minor_columns = []
    for column_index in pivot_minor_columns:
        encoded = 0
        column = support_columns[column_index]
        for row_index, row in enumerate(pivot_rows):
            if (column >> row) & 1:
                encoded |= 1 << row_index
        minor_columns.append(encoded)
    if rank_vectors(minor_columns) != rank:
        raise AssertionError("rank lower-bound minor is singular")
    derivative_circuit = derivative_block_circuit(blocks, support, rank, kernel_basis)
    if not derivative_circuit["is_minimal_dependence"]:
        raise AssertionError("deficient support is not a derivative-block circuit")
    record = {
        "combinadic_lex_id": candidate["id"],
        "support0": list(support),
        "reduced_rank": rank,
        "raw_restricted_kernel_dimension": 240 - rank,
        "reduced_kernel_dimension": len(kernel_basis),
        "restricted_gauge_dimension": 10 + len(gauge_basis),
        "quotient_sandwich_intersection_dimension": len(gauge_basis),
        "normal_dimension": len(normal_basis),
        "rank_certificate": {
            "pivot_rows": pivot_rows,
            "pivot_columns": pivot_minor_columns,
            "kernel_basis_reduced_lsb_hex": [bitset_hex(vector, 230) for vector in kernel_basis],
        },
        "restricted_gauge_basis_reduced_lsb_hex": [bitset_hex(vector, 230) for vector in gauge_basis],
        "normal_section_basis_reduced_lsb_hex": [bitset_hex(vector, 230) for vector in normal_basis],
        "factor_three_circuits_inside_support": readable_circuits,
        "factor_circuit_signature_30bit_hex": f"{circuit_signature:08x}",
        "derivative_block_circuit": derivative_circuit,
        "paired_t3": {
            "orientation_mask": orientation_mask(witnesses),
            "witnesses": witness_records,
            "normal_direction_coordinate_masks": sorted(motif_direction_masks),
        },
    }
    same_rref = None
    canonical_update_certificate = None
    directions = []
    direction_count = (1 << len(normal_basis)) - 1
    for coordinate_mask in range(1, direction_count + 1):
        reduced = 0
        for index in bits(coordinate_mask):
            reduced ^= normal_basis[index]
        variation = reduced_support_to_raw(support, reduced, kept_indices)
        quadratic = quadratic_coefficient(terms, support, variation)
        if multiply_columns(support_columns, reduced):
            raise AssertionError("normal representative is not in kernel")
        same_certificate = obstruction_certificate(support_columns, support_basis, quadratic, 4096)
        full_certificate = obstruction_certificate(full_columns, full_basis, quadratic, 4096)
        is_t3 = coordinate_mask in motif_direction_masks
        if is_t3:
            canonical_witness = min(
                witnesses_by_normal_mask[coordinate_mask],
                key=lambda witness: (
                    tangent_for_witness(terms, support, witness, coordinate_maps)[1] != variation,
                    ORIENTATION_NAMES.index(witness["orientation"]),
                    witness["labels"],
                ))
            update_certificate = canonical_t3_update_certificate(
                terms, support, canonical_witness, variation)
            if canonical_update_certificate is None:
                canonical_update_certificate = update_certificate
            lifting = {
                "statement_scope": "normal class; raw deterministic section is related separately",
                "same_support": {
                    "status": "normal_class_exact_paired_t3_family",
                    "relation": "(1+s)(1+t)=1",
                    "formal_parameterization": "t=tau, s=tau/(1+tau)",
                    "coefficient_domains": "every field of characteristic two",
                },
                "full_coordinate": {
                    "status": "normal_class_exact_paired_t3_family",
                    "reason": "same-support normal-class family is also a full-coordinate family",
                },
            }
        else:
            first_global = [(0, 0, 0) for _ in range(49)]
            for slot, delta in zip(support, variation):
                first_global[slot] = delta
            if hasse_residual(terms, [first_global], 2) != quadratic:
                raise AssertionError("Hasse order-two residual disagrees with quadratic coefficient")
            same_to_global = lambda value, support=support: _support_raw_global(
                support, reduced_support_to_raw(support, value, kept_indices))
            full_to_global = lambda value: reduced_global_to_raw(value, kept_indices)
            same_hasse = bounded_hasse_attempt(
                terms, first_global, support_columns, support_basis, kernel_basis,
                same_to_global, max_hasse_order, branch_cap, enum_kernel_dim)
            full_hasse = bounded_hasse_attempt(
                terms, first_global, full_columns, full_basis, full_kernel,
                full_to_global, max_hasse_order, branch_cap, enum_kernel_dim)
            lifting = {"same_support": same_hasse, "full_coordinate": full_hasse}
        directions.append({
            "normal_coordinate_mask": coordinate_mask,
            "representative_reduced_lsb_hex": bitset_hex(reduced, 230),
            "raw_variation": raw_variation_record(support, variation),
            "quadratic_residual_lsb_hex": bitset_hex(quadratic, 4096),
            "quadratic_residual_weight": quadratic.bit_count(),
            "same_support_quadratic_obstruction": same_certificate,
            "full_coordinate_quadratic_obstruction": full_certificate,
            "paired_t3_exact_normal_class_family": is_t3,
            "normalization_scope": "quadratic data use this displayed deterministic normal-section representative",
            "lifting": lifting,
        })
    if len(normal_basis) == 1:
        fbar = {
            "projective_space": "P^0_over_Fbar2",
            "status": "exactly_one_projective_direction_defined_over_F2",
            "direction_normal_coordinate_mask": 1,
            "quadratic_status_scalar_extends_from_F2": True,
            "integrability_status": "normal_class_exact_paired_t3_family_over_every_characteristic_two_field"
            if 1 in motif_direction_masks else "unknown_beyond_recorded_quadratic_and_bounded_F2_tests",
        }
    elif len(normal_basis) > 1:
        same_rref = rref_vectors_from_basis(support_basis)
        fbar = {
            "projective_space": f"P^{len(normal_basis) - 1}_over_Fbar2",
            "status": "projective_quadratic_ideals_emitted_not_solved",
            "same_support_quadratic_obstruction_ideal": obstruction_ideal(
                terms, support, normal_basis, kept_indices, support_columns, support_basis),
            "full_coordinate_quadratic_obstruction_ideal": obstruction_ideal(
                terms, support, normal_basis, kept_indices, full_columns, full_basis),
        }
    else:
        fbar = {"status": "no_projective_normal_directions"}
    record["paired_t3"]["canonical_oriented_factor_update_witness"] = canonical_update_certificate
    record["projective_directions"] = {
        "F2": {
            "status": "complete",
            "count": direction_count,
            "directions": directions,
        },
        "Fbar2": fbar,
    }
    return record


def _support_raw_global(support, local_variation):
    result = [(0, 0, 0) for _ in range(49)]
    for slot, delta in zip(support, local_variation):
        result[slot] = delta
    return result


def build_result(orbit_output_path: Path, max_hasse_order: int, branch_cap: int,
                 enum_kernel_dim: int, progress: bool = True):
    revision = base_revision()
    script_sha256 = sha256_bytes(Path(__file__).resolve().read_bytes())
    run_limits = {
        "max_hasse_order": max_hasse_order,
        "branch_cap": branch_cap,
        "enumerate_affine_kernel_when_dimension_at_most": enum_kernel_dim,
        "orbit_gzip_compression_level": 9,
        "orbit_gzip_mtime": 0,
        "finite_truncation_is_integrability": False,
    }
    raw, terms = read_scheme(FIXTURE_DEFAULT)
    facts = source_facts(terms)
    local = [local_reduced_block(term) for term in terms]
    blocks = [entry[0] for entry in local]
    kept_indices = [entry[1] for entry in local]
    deleted_indices = [entry[2] for entry in local]
    coordinate_maps = [entry[3] for entry in local]
    full_columns = [column for block in blocks for column in block]
    full_basis, full_kernel, full_pivot_columns = tagged_elimination(full_columns)
    if len(full_basis) != 2155 or len(full_kernel) != 99:
        raise AssertionError(f"unexpected full reduced rank/nullity {len(full_basis)}/{len(full_kernel)}")
    quotient_gauge_generators, independent_gauge = quotient_sandwich_vectors(terms, coordinate_maps)
    factor_circuits, triple_code, motif_by_support, motif_per_orientation = circuit_and_motif_data(terms)
    coverage = hashlib.sha256()
    support_order_digest = hashlib.sha256()
    rank_stream_digest = hashlib.sha256()
    rank_hist = Counter()
    gauge_hist = Counter()
    normal_hist = Counter()
    cross_hist = Counter()
    orientation_hist = Counter()
    circuit_support_counts = Counter()
    circuit_occurrences = Counter()
    derivative_kind_hist = Counter()
    deficient = []
    positive = []
    first_support = None
    last_support = None
    count = 0
    for lex_id, support in enumerate(itertools.combinations(range(49), 5)):
        if first_support is None:
            first_support = support
        last_support = support
        rank = support_rank(blocks, support)
        if rank == 230:
            gauge_dimension = 0
            normal_dimension = 0
            derivative_signature = "I:r230"
            derivative_kind_hist["independent"] += 1
        else:
            gauge_basis = restricted_gauge_basis(independent_gauge, support)
            gauge_dimension = len(gauge_basis)
            normal_dimension = 230 - rank - gauge_dimension
            if normal_dimension < 0:
                raise AssertionError("negative normal dimension")
            derivative = derivative_block_circuit(blocks, support, rank)
            derivative_signature = derivative["signature"]
            derivative_kind_hist[derivative["kind"]] += 1
            item = {
                "id": lex_id,
                "support": support,
                "rank": rank,
                "quotient_sandwich_intersection_dimension": gauge_dimension,
                "normal_dimension": normal_dimension,
                "derivative_block_circuit": derivative,
            }
            deficient.append(item)
            if normal_dimension > 0:
                positive.append(item)
        circuit_signature, readable = support_circuit_signature(support, triple_code)
        for mode in ("U", "V", "W"):
            if readable[mode]:
                circuit_support_counts[mode] += 1
                circuit_occurrences[mode] += len(readable[mode])
        witnesses = motif_by_support.get(support, [])
        omask = orientation_mask(witnesses)
        orientation_hist[omask] += 1
        wsig = witness_signature(witnesses)
        row = (lex_id.to_bytes(8, "little") + bytes(support)
               + bytes((rank, gauge_dimension, normal_dimension, omask))
               + circuit_signature.to_bytes(4, "little")
               + len(derivative_signature).to_bytes(2, "little") + derivative_signature.encode()
               + len(witnesses).to_bytes(2, "little") + wsig)
        coverage.update(row)
        support_order_digest.update(bytes(support))
        rank_stream_digest.update(bytes((rank, gauge_dimension, normal_dimension)))
        rank_hist[rank] += 1
        gauge_hist[gauge_dimension] += 1
        normal_hist[normal_dimension] += 1
        cross_hist[(rank, gauge_dimension, normal_dimension)] += 1
        count += 1
        if progress and count % 250000 == 0:
            print(f"census {count}/{SUPPORT_COUNT}", file=sys.stderr)
    if count != SUPPORT_COUNT or first_support != (0, 1, 2, 3, 4) or last_support != (44, 45, 46, 47, 48):
        raise AssertionError("coverage failure")
    records = []
    for index, candidate in enumerate(positive):
        if progress:
            print(f"positive support {index + 1}/{len(positive)} {candidate['support']}", file=sys.stderr)
        records.append(support_positive_record(
            candidate, terms, blocks, kept_indices, coordinate_maps,
            independent_gauge, motif_by_support, triple_code,
            full_columns, full_basis, full_kernel,
            max_hasse_order, branch_cap, enum_kernel_dim))
    positive_supports = {tuple(record["support0"]) for record in records}
    non_t3_positive = sorted(list(support) for support in positive_supports if support not in motif_by_support)
    representative_mismatches = sum(
        not record["paired_t3"]["canonical_oriented_factor_update_witness"]
        ["normal_class_integrability"]["raw_section_representative_is_t3_tangent"]
        for record in records)
    if representative_mismatches != 39:
        raise AssertionError(f"expected 39 deterministic section/T3 mismatches, found {representative_mismatches}")
    local_split_digest = hashlib.sha256()
    for slot in range(49):
        local_split_digest.update(bytes(kept_indices[slot]))
        for column in blocks[slot]:
            local_split_digest.update(column.to_bytes(512, "little"))
    deficient_content = [
        {
            "combinadic_lex_id": item["id"],
            "support0": list(item["support"]),
            "reduced_rank": item["rank"],
            "quotient_sandwich_intersection_dimension": item["quotient_sandwich_intersection_dimension"],
            "normal_dimension": item["normal_dimension"],
            "derivative_block_circuit": item["derivative_block_circuit"],
        }
        for item in deficient
    ]
    factor_t3_content = {
        "factor_three_circuits": [
            [list(circuit) for circuit in circuits] for circuits in factor_circuits],
        "motif_per_orientation": motif_per_orientation,
        "motif_witnesses_by_support": [
            {"support0": list(support), "witnesses": witnesses}
            for support, witnesses in sorted(motif_by_support.items())
        ],
    }
    certificate_content = {
        "schema": CERTIFICATE_SCHEMA,
        "definition": "non-self-referential manifest of authenticated census mathematical content; excludes census JSON bytes, orbit stream bytes and all hashes of those two files",
        "source_sha256": sha256_bytes(raw),
        "fixture_path": FIXTURE_RELATIVE.as_posix(),
        "base_revision": revision,
        "base_revision_policy": GENERATION_BASE_POLICY,
        "owned_script_sha256": script_sha256,
        "run_limits": run_limits,
        "coverage": {
            "count": count,
            "classification_sha256": coverage.hexdigest(),
            "support_order_sha256": support_order_digest.hexdigest(),
            "rank_gauge_normal_stream_sha256": rank_stream_digest.hexdigest(),
        },
        "global_linear_content": {
            "reduced_columns_sha256": tensor_vector_digest(full_columns),
            "local_split_sha256": local_split_digest.hexdigest(),
            "quotient_sandwich_generators_sha256": tensor_vector_digest(quotient_gauge_generators),
            "quotient_sandwich_independent_basis_sha256": tensor_vector_digest(independent_gauge),
            "full_reduced_kernel_basis_sha256": tensor_vector_digest(full_kernel),
        },
        "factor_and_paired_t3_content_sha256": sha256_bytes(canonical_json(factor_t3_content)),
        "deficient_support_content_sha256": sha256_bytes(canonical_json(deficient_content)),
        "positive_normal_support_content_sha256": sha256_bytes(canonical_json(records)),
    }
    certificate_content_sha256 = sha256_bytes(canonical_json(certificate_content))
    census_content_certificate = {
        "schema": CERTIFICATE_SCHEMA,
        "content": certificate_content,
        "content_sha256": certificate_content_sha256,
        "non_self_referential": True,
        "excluded_from_content_hash": [
            "census artifact file bytes/hash",
            "singleton orbit stream bytes/hash/body-stream digest/cross-digest",
            "dynamic run measurements",
        ],
    }
    orbit_metadata = write_singleton_orbits(
        orbit_output_path, records, triple_code, coverage.hexdigest(),
        certificate_content_sha256)
    result = {
        "schema": SCHEMA,
        "provenance": {
            "base_revision": revision,
            "base_revision_policy": GENERATION_BASE_POLICY,
            "owned_script_path": SCRIPT_RELATIVE.as_posix(),
            "owned_script_sha256": script_sha256,
            "owned_code_sha256": {
                "Programs/BilinearComplexity/rank49_t4/support5_census.py": script_sha256,
            },
            "owned_payload_paths": [
                ARTIFACT_RELATIVE.as_posix(),
                orbit_metadata["relative_path"],
            ],
            "exact_generation_command": "python3 Programs/BilinearComplexity/rank49_t4/support5_census.py",
            "exact_check_command": "python3 Programs/BilinearComplexity/rank49_t4/support5_census.py --check --quiet",
            "status_provenance": {
                "linear_and_circuit": "exact F2 bitset elimination from authenticated source",
                "obstruction": "exact F2 image/preimage or left-null certificate on displayed section",
                "solver": "exact paired-T3 Laurent/formal replay when so labelled; otherwise bounded status retains unknown",
                "geometric": "scalar-extension rank plus complete projective ideal; no sampled points promoted to geometric claims",
                "orbits": "identity action only; every support is a singleton and no stabilizer reduction is claimed",
            },
        },
        "census_content_certificate": census_content_certificate,
        "source": {
            "fixture_path": FIXTURE_RELATIVE.as_posix(),
            "fixture_role": "sole input opened by generator and checker",
            "external_provenance_locator": EXTERNAL_SOURCE_PROVENANCE_LOCATOR,
            "external_provenance_locator_opened": False,
            "sha256": sha256_bytes(raw),
            "byte_count": len(raw),
            "dimensions": [4, 4, 4],
            "ordered_length": 49,
            "field": "F2",
            "factor_layout": "row-major bit 4*row+column; W is indexed [c,a]",
            "facts": facts,
        },
        "conventions": {
            "support_indices": "zero-based",
            "support_order": "itertools.combinations(range(49),5), lexicographic",
            "tensor_bit": "256*U_coordinate+16*V_coordinate+W_coordinate",
            "bitset_hex": "little-endian bytes; bit i is coordinate/column i",
            "normal_section": "deterministic complement of restricted quotient-sandwich intersection inside reduced kernel",
            "obstruction_scope": "computed on the displayed normal-section representative",
            "stabilizer_reduction": False,
        },
        "run_limits": run_limits,
        "global_linear_model": {
            "raw_jacobian_shape": [4096, 2352],
            "raw_jacobian_rank": 2155,
            "raw_kernel_dimension": 197,
            "local_scaling_dimension": 98,
            "reduced_jacobian_shape": [4096, 2254],
            "reduced_jacobian_rank": len(full_basis),
            "reduced_kernel_dimension": len(full_kernel),
            "gauge_plus_sandwich_rank": 143,
            "quotient_sandwich_generator_count": len(quotient_gauge_generators),
            "quotient_sandwich_rank": len(independent_gauge),
            "ambient_normal_dimension": len(full_kernel) - len(independent_gauge),
            "kept_raw_coordinate_indices_by_term": kept_indices,
            "deleted_raw_coordinate_indices_by_term": deleted_indices,
            "reduced_columns_sha256": tensor_vector_digest(full_columns),
            "local_split_sha256": local_split_digest.hexdigest(),
            "quotient_sandwich_generators_lsb_hex": [bitset_hex(v, 49 * 46) for v in quotient_gauge_generators],
            "quotient_sandwich_independent_basis_lsb_hex": [bitset_hex(v, 49 * 46) for v in independent_gauge],
            "full_reduced_kernel_basis_lsb_hex": [bitset_hex(v, 49 * 46) for v in full_kernel],
            "full_pivot_column_count": len(full_pivot_columns),
        },
        "factor_three_circuits": {
            "U": [list(circuit) for circuit in factor_circuits[0]],
            "V": [list(circuit) for circuit in factor_circuits[1]],
            "W": [list(circuit) for circuit in factor_circuits[2]],
            "counts": [len(circuits) for circuits in factor_circuits],
            "definition": "minimal binary three-term factor dependence; all factors are nonzero and pairwise distinct",
        },
        "paired_t3_global": {
            "orientation_order": list(ORIENTATION_NAMES),
            "per_orientation": motif_per_orientation,
            "unique_support_count": len(motif_by_support),
            "witness_count": sum(len(value) for value in motif_by_support.values()),
            "role": "sufficient exact-family motif, not a classification theorem",
        },
        "coverage": {
            "expected_count": SUPPORT_COUNT,
            "actual_count": count,
            "first_support0": list(first_support),
            "last_support0": list(last_support),
            "classification_sha256": coverage.hexdigest(),
            "support_order_sha256": support_order_digest.hexdigest(),
            "rank_gauge_normal_stream_sha256": rank_stream_digest.hexdigest(),
            "complete_without_stabilizer_reduction": True,
            "rank_histogram": {str(k): rank_hist[k] for k in sorted(rank_hist)},
            "quotient_sandwich_intersection_histogram": {str(k): gauge_hist[k] for k in sorted(gauge_hist)},
            "normal_dimension_histogram": {str(k): normal_hist[k] for k in sorted(normal_hist)},
            "rank_gauge_normal_histogram": {
                f"rank={key[0]},g={key[1]},normal={key[2]}": cross_hist[key]
                for key in sorted(cross_hist)
            },
            "paired_t3_orientation_mask_histogram": {str(k): orientation_hist[k] for k in sorted(orientation_hist)},
            "supports_containing_factor_three_circuit": dict(sorted(circuit_support_counts.items())),
            "factor_three_circuit_occurrences": dict(sorted(circuit_occurrences.items())),
            "derivative_block_circuit_kind_histogram": dict(sorted(derivative_kind_hist.items())),
            "derivative_block_circuit_definition": "minimal dependence among the five reduced 46-column derivative term blocks; all five proper four-block restrictions are checked",
            "orbit_length_prefixed_body_stream_sha256": orbit_metadata["length_prefixed_body_stream_sha256"],
            "orbit_census_certificate_content_sha256": orbit_metadata["census_certificate_content_sha256"],
            "orbit_cross_digest_sha256": orbit_metadata["cross_digest_sha256"],
            "deficient_support_count": len(deficient),
            "positive_normal_support_count": len(positive),
        },
        "deficient_supports": deficient_content,
        "positive_normal_supports": records,
        "singleton_orbit_records": orbit_metadata,
        "summary": {
            "all_positive_supports_are_paired_t3_motifs": not non_t3_positive,
            "non_t3_positive_supports": non_t3_positive,
            "F2_projective_direction_count": sum(record["projective_directions"]["F2"]["count"] for record in records),
            "Fbar_direction_classification": "exact for normal dimension one; full quadratic ideals emitted for larger dimensions",
            "same_support_and_full_coordinate_statuses_kept_separate": True,
            "exact_integrability_statement_scope": "normal classes; raw deterministic sections are never identified with canonical T3 tangents without the stored comparison",
            "raw_section_representative_matches_canonical_t3_tangent": len(records) - representative_mismatches,
            "raw_section_representative_local_scaling_mismatches": representative_mismatches,
            "mismatch_local_scaling_corrections_and_integrated_gauge_paths_emitted": representative_mismatches,
            "linear_scalar_extension_scope": "all ranks, kernel dimensions, gauge-intersection dimensions, and normal dimensions are unchanged over every characteristic-two field; projective point sets are not thereby identified",
        },
        "unknowns": [
            "No stabilizer or orbit reduction is claimed or used.",
            "Paired-T3 is sufficient and is not assumed complete before the exhaustive rank result is read.",
            "For normal dimension greater than one, emitted projective quadratic ideals are not declared geometrically solved.",
            "A bounded successful Hasse lift is not an all-order integrability result.",
            "F2 bounded higher lifting does not classify Fbar2 higher lifting unless an exact family or scalar-extended obstruction certificate is present.",
        ],
    }
    return result


def validate_deterministic_artifact(value):
    forbidden_keys = {
        "timing", "elapsed_seconds", "hostname", "pid", "platform", "architecture",
        "machine", "processor", "logical_cpu_count", "cpu_count", "source_path_used",
        "absolute_path",
    }

    def visit(item, location):
        if isinstance(item, dict):
            for key, child in item.items():
                if key.lower() in forbidden_keys:
                    raise ValueError(f"dynamic key in deterministic artifact at {location}.{key}")
                visit(child, f"{location}.{key}")
        elif isinstance(item, list):
            for index, child in enumerate(item):
                visit(child, f"{location}[{index}]")
        elif isinstance(item, str) and item.startswith("/"):
            raise ValueError(f"absolute path in deterministic artifact at {location}")

    visit(value, "artifact")


def write_artifact(path: Path, result):
    script_sha256 = sha256_bytes((REPO_ROOT / SCRIPT_RELATIVE).read_bytes())
    artifact = {
        "artifact_schema": SCHEMA,
        "generator": {
            "script_path": SCRIPT_RELATIVE.as_posix(),
            "script_sha256": script_sha256,
            "fixture_path": FIXTURE_RELATIVE.as_posix(),
            "fixture_sha256": SOURCE_SHA256,
            "generation_command": f"python3 {SCRIPT_RELATIVE.as_posix()}",
            "check_command": f"python3 {SCRIPT_RELATIVE.as_posix()} --check --quiet",
            "deterministic_artifact": True,
            "dynamic_run_data": "stdout only and explicitly unauthenticated",
        },
        "result": result,
    }
    validate_deterministic_artifact(artifact)
    data = json.dumps(artifact, indent=2, sort_keys=True).encode() + b"\n"
    durable_atomic_write(path, data)
    return artifact


def parse_args():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="recompute and validate the census and its referenced content-addressed orbit payload")
    parser.add_argument("--quiet", action="store_true")
    parser.add_argument("--max-hasse-order", type=int, default=DEFAULT_MAX_HASSE_ORDER)
    parser.add_argument("--branch-cap", type=int, default=DEFAULT_BRANCH_CAP)
    parser.add_argument("--enum-kernel-dim", type=int, default=DEFAULT_ENUM_KERNEL_DIM)
    return parser.parse_args()


def default_limits():
    return {
        "max_hasse_order": DEFAULT_MAX_HASSE_ORDER,
        "branch_cap": DEFAULT_BRANCH_CAP,
        "enumerate_affine_kernel_when_dimension_at_most": DEFAULT_ENUM_KERNEL_DIM,
        "orbit_gzip_compression_level": 9,
        "orbit_gzip_mtime": 0,
        "finite_truncation_is_integrability": False,
    }


def check_artifact(progress: bool, started: float):
    artifact = json.loads(ARTIFACT_DEFAULT.read_text())
    validate_deterministic_artifact(artifact)
    if artifact.get("artifact_schema") != SCHEMA or artifact.get("result", {}).get("schema") != SCHEMA:
        raise SystemExit("census artifact schema mismatch")
    actual_script_hash = sha256_bytes((REPO_ROOT / SCRIPT_RELATIVE).read_bytes())
    expected_generator = {
        "script_path": SCRIPT_RELATIVE.as_posix(),
        "script_sha256": actual_script_hash,
        "fixture_path": FIXTURE_RELATIVE.as_posix(),
        "fixture_sha256": SOURCE_SHA256,
        "generation_command": f"python3 {SCRIPT_RELATIVE.as_posix()}",
        "check_command": f"python3 {SCRIPT_RELATIVE.as_posix()} --check --quiet",
        "deterministic_artifact": True,
        "dynamic_run_data": "stdout only and explicitly unauthenticated",
    }
    if artifact.get("generator") != expected_generator:
        raise SystemExit("deterministic generator manifest mismatch")
    if file_sha256(FIXTURE_DEFAULT) != SOURCE_SHA256:
        raise SystemExit("vendored fixture SHA-256 mismatch")
    source = artifact["result"].get("source", {})
    if (source.get("fixture_path") != FIXTURE_RELATIVE.as_posix()
            or source.get("fixture_role") != "sole input opened by generator and checker"
            or source.get("external_provenance_locator") != EXTERNAL_SOURCE_PROVENANCE_LOCATOR
            or source.get("external_provenance_locator_opened") is not False
            or source.get("sha256") != SOURCE_SHA256):
        raise SystemExit("vendored fixture provenance mismatch")
    provenance = artifact["result"]["provenance"]
    if provenance.get("owned_script_path") != SCRIPT_RELATIVE.as_posix():
        raise SystemExit("owned script path mismatch")
    if provenance.get("owned_script_sha256") != actual_script_hash:
        raise SystemExit("owned-code hash mismatch in deterministic provenance")
    if provenance.get("owned_code_sha256") != {SCRIPT_RELATIVE.as_posix(): actual_script_hash}:
        raise SystemExit("owned-code hash map mismatch in deterministic provenance")
    expected_commands = {
        "exact_generation_command": f"python3 {SCRIPT_RELATIVE.as_posix()}",
        "exact_check_command": f"python3 {SCRIPT_RELATIVE.as_posix()} --check --quiet",
    }
    for key, value in expected_commands.items():
        if provenance.get(key) != value:
            raise SystemExit(f"deterministic provenance mismatch for {key}")
    generation_base_revision = base_revision()
    if provenance.get("base_revision") != generation_base_revision:
        raise SystemExit(
            f"fixed generation base mismatch: artifact={provenance.get('base_revision')} expected={generation_base_revision}")
    if provenance.get("base_revision_policy") != GENERATION_BASE_POLICY:
        raise SystemExit("fixed generation base policy mismatch")
    certificate = artifact["result"].get("census_content_certificate", {})
    certificate_content = certificate.get("content")
    if certificate.get("schema") != CERTIFICATE_SCHEMA or not certificate.get("non_self_referential"):
        raise SystemExit("census content certificate schema/scope mismatch")
    if not isinstance(certificate_content, dict):
        raise SystemExit("census content certificate manifest missing")
    certificate_content_sha256 = sha256_bytes(canonical_json(certificate_content))
    if certificate.get("content_sha256") != certificate_content_sha256:
        raise SystemExit("census content certificate digest mismatch")
    if (certificate_content.get("source_sha256") != SOURCE_SHA256
            or certificate_content.get("fixture_path") != FIXTURE_RELATIVE.as_posix()):
        raise SystemExit("census content certificate fixture mismatch")
    if certificate_content.get("base_revision") != generation_base_revision:
        raise SystemExit("census content certificate fixed generation base mismatch")
    if certificate_content.get("base_revision_policy") != GENERATION_BASE_POLICY:
        raise SystemExit("census content certificate generation-base policy mismatch")
    if certificate_content.get("owned_script_sha256") != actual_script_hash:
        raise SystemExit("census content certificate owned-code mismatch")
    orbit_metadata = artifact["result"]["singleton_orbit_records"]
    if orbit_metadata.get("schema") != ORBIT_SCHEMA:
        raise SystemExit("singleton orbit artifact schema mismatch")
    try:
        orbit_path = referenced_orbit_path(orbit_metadata)
    except ValueError as exc:
        raise SystemExit(str(exc)) from exc
    expected_owned_payloads = [ARTIFACT_RELATIVE.as_posix(), orbit_metadata["relative_path"]]
    if provenance.get("owned_payload_paths") != expected_owned_payloads:
        raise SystemExit("owned payload reference mismatch")
    if orbit_metadata.get("census_classification_sha256") != artifact["result"]["coverage"]["classification_sha256"]:
        raise SystemExit("singleton orbit/census classification cross-reference mismatch")
    if orbit_metadata.get("census_certificate_content_sha256") != certificate_content_sha256:
        raise SystemExit("singleton orbit/census certificate cross-reference mismatch")
    row_authentication = orbit_metadata.get("row_authentication", {})
    if (row_authentication.get("field") != "census_certificate_content_sha256"
            or row_authentication.get("value") != certificate_content_sha256
            or row_authentication.get("individual_random_row_hashes") is not False):
        raise SystemExit("singleton orbit row-authentication metadata mismatch")
    if artifact["result"]["coverage"].get("orbit_census_certificate_content_sha256") != certificate_content_sha256:
        raise SystemExit("coverage/certificate cross-reference mismatch")
    if file_sha256(orbit_path) != orbit_metadata["compressed_sha256"]:
        raise SystemExit("referenced singleton orbit compressed payload hash mismatch")
    limits = artifact["result"]["run_limits"]
    if limits != default_limits():
        raise SystemExit("run-limit provenance does not match the exact default command")
    if certificate_content.get("run_limits") != limits:
        raise SystemExit("census content certificate run-limit mismatch")
    certificate_coverage = certificate_content.get("coverage", {})
    result_coverage = artifact["result"]["coverage"]
    if certificate_coverage != {
            "count": result_coverage["actual_count"],
            "classification_sha256": result_coverage["classification_sha256"],
            "support_order_sha256": result_coverage["support_order_sha256"],
            "rank_gauge_normal_stream_sha256": result_coverage["rank_gauge_normal_stream_sha256"]}:
        raise SystemExit("census content certificate coverage mismatch")
    descriptor, temporary_name = tempfile.mkstemp(prefix="support5_orbits.check.", suffix=".jsonl.gz")
    os.close(descriptor)
    temporary_orbits = Path(temporary_name)
    try:
        result = build_result(
            temporary_orbits,
            limits["max_hasse_order"],
            limits["branch_cap"],
            limits["enumerate_affine_kernel_when_dimension_at_most"],
            progress=progress)
        if canonical_json(result) != canonical_json(artifact["result"]):
            raise SystemExit("artifact deterministic result mismatch")
        if file_sha256(temporary_orbits) != file_sha256(orbit_path):
            raise SystemExit("regenerated singleton orbit payload mismatch")
        validated = validate_singleton_orbits(orbit_path, orbit_metadata)
    finally:
        temporary_orbits.unlink(missing_ok=True)
    print(json.dumps({
        "status": "ok",
        "authenticated_outputs": {
            "census_artifact": {
                "path": ARTIFACT_RELATIVE.as_posix(),
                "sha256": sha256_bytes(ARTIFACT_DEFAULT.read_bytes()),
            },
            "singleton_orbits": {
                "path": orbit_metadata["relative_path"],
                "sha256": orbit_metadata["compressed_sha256"],
                "record_count": validated["record_count"],
            },
            "script_sha256": actual_script_hash,
            "fixture_sha256": SOURCE_SHA256,
            "classification_sha256": result["coverage"]["classification_sha256"],
            "certificate_content_sha256": certificate_content_sha256,
            "orbit_cross_digest_sha256": orbit_metadata["cross_digest_sha256"],
        },
        "unauthenticated_run_data": {
            "elapsed_seconds": time.perf_counter() - started,
            "obsolete_unreferenced_orbit_files": obsolete_orbit_paths(orbit_path),
        },
    }, indent=2, sort_keys=True))


def generate_artifact(args, started: float):
    if (args.max_hasse_order, args.branch_cap, args.enum_kernel_dim) != (
            DEFAULT_MAX_HASSE_ORDER, DEFAULT_BRANCH_CAP, DEFAULT_ENUM_KERNEL_DIM):
        raise SystemExit("nondefault run limits cannot produce the deterministic default artifact")
    ORBIT_DIRECTORY_DEFAULT.mkdir(parents=True, exist_ok=True)
    temporary_orbits = same_directory_temporary(
        ORBIT_DIRECTORY_DEFAULT, ".support5_orbits.", ".jsonl.gz.tmp")
    try:
        result = build_result(
            temporary_orbits,
            args.max_hasse_order,
            args.branch_cap,
            args.enum_kernel_dim,
            progress=not args.quiet)
        orbit_metadata = result["singleton_orbit_records"]
        orbit_path, reused = publish_content_addressed_orbit(temporary_orbits, orbit_metadata)
        artifact = write_artifact(ARTIFACT_DEFAULT, result)
    finally:
        temporary_orbits.unlink(missing_ok=True)
    print(json.dumps({
        "status": "written",
        "authenticated_outputs": {
            "census_artifact": {
                "path": ARTIFACT_RELATIVE.as_posix(),
                "sha256": sha256_bytes(ARTIFACT_DEFAULT.read_bytes()),
            },
            "singleton_orbits": {
                "path": orbit_metadata["relative_path"],
                "sha256": orbit_metadata["compressed_sha256"],
                "record_count": orbit_metadata["record_count"],
            },
            "script_sha256": artifact["generator"]["script_sha256"],
            "fixture_sha256": SOURCE_SHA256,
            "classification_sha256": result["coverage"]["classification_sha256"],
            "certificate_content_sha256": result["census_content_certificate"]["content_sha256"],
            "orbit_cross_digest_sha256": orbit_metadata["cross_digest_sha256"],
        },
        "unauthenticated_run_data": {
            "elapsed_seconds": time.perf_counter() - started,
            "content_addressed_payload_reused": reused,
            "obsolete_unreferenced_orbit_files": obsolete_orbit_paths(orbit_path),
        },
    }, indent=2, sort_keys=True))


def main():
    args = parse_args()
    started = time.perf_counter()
    if args.check:
        if (args.max_hasse_order, args.branch_cap, args.enum_kernel_dim) != (
                DEFAULT_MAX_HASSE_ORDER, DEFAULT_BRANCH_CAP, DEFAULT_ENUM_KERNEL_DIM):
            raise SystemExit("--check accepts only deterministic default run limits")
        check_artifact(progress=not args.quiet, started=started)
    else:
        generate_artifact(args, started)


if __name__ == "__main__":
    main()
