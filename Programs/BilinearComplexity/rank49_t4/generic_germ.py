#!/usr/bin/env python3
"""Exact generic-germ certificate for the certified rank-49 family over F_2(b)."""

from __future__ import annotations

import argparse
import collections
import functools
import hashlib
import json
import os
import resource
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Iterable

SCHEMA = "BilinearComplexity.rank49_t4.generic_germ.v3"
REPOSITORY_PATH = "Programs/BilinearComplexity/rank49_t4/generic_germ.py"
FIXTURE_REPOSITORY_PATH = (
    "Programs/BilinearComplexity/rank49_t4/fixtures/"
    "4x4x4_m49_c680_iteration65_Z2.txt"
)
ORIGINAL_EXTERNAL_LOCATOR = (
    "/home/exedev/x/tensor/data/z2/4x4x4_m49_c680_iteration65_Z2.txt"
)
SOURCE_SHA256 = "5fc92a6bf83fc29d9527ab100bad5d72d769178b616b31a36c3c0c0b8ad9d09d"
HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parents[2]
SOURCE = REPO_ROOT / FIXTURE_REPOSITORY_PATH
BASE_GIT_REVISION = "6866f8be63692dc918e26d75db9414325b03b78c"
GENERATION_COMMAND = (
    "python3 Programs/BilinearComplexity/rank49_t4/generic_germ.py --generate-artifact"
)
CHECK_COMMAND = "python3 Programs/BilinearComplexity/rank49_t4/generic_germ.py --check"
ARTIFACT = HERE / "artifacts" / "generic_germ.json"

N = 4
R = 49
FACTOR_DIM = 16
DOMAIN_DIM = 3 * R * FACTOR_DIM
TENSOR_DIM = FACTOR_DIM**3
MOVING_TERMS = (1, 14, 29, 37, 42)
S_UPDATES = {
    1: {0: 0x0500},
    37: {0: 0x0500},
    42: {0: 0x0500},
}
T_UPDATES = {
    14: {2: 0x0070},
    29: {0: 0x9990},
    37: {2: 0x7707},
    42: {2: 0x0070},
}
GF_DEGREE = 9
GF_MODULUS = 0x211
GF_ORDER = 1 << GF_DEGREE
GF_PRIMITIVE = 2

EXPECTED = {
    "fixed_rank": 1958,
    "quotient_rank": 197,
    "jacobian_rank": 2155,
    "kernel_dimension": 197,
    "quotient_minor_exponent": 208,
    "symmetry_rank": 143,
    "symmetry_minor_exponent": 143,
    "sweep_rank": 144,
    "sweep_minor_exponent": 288,
    "normal_tangent_dimension": 54,
}

LIMITS = {
    "finite_field_elements": 512,
    "finite_field_degree": 9,
    "largest_matrix_rows": TENSOR_DIM,
    "largest_matrix_columns": DOMAIN_DIM,
    "quotient_upper_minor_degree": 396,
    "symmetry_upper_minor_degree": 288,
    "selected_sweep_minor_degree": 431,
    "wall_seconds_advisory": 600,
    "peak_rss_mib_advisory": 1024,
}

COEFFICIENT_FIELDS = {
    "source_and_binary_linear_algebra": "F_2",
    "generic_family": "F_2(b) with b invertible",
    "polynomial_identity_ring_after_clearing": "F_2[b]",
    "exhaustive_evaluation_field": {
        "name": "GF(2^9)",
        "modulus": "x^9+x^4+1",
        "modulus_integer": GF_MODULUS,
        "primitive_element_integer": GF_PRIMITIVE,
    },
}

RANDOMNESS = {
    "used": False,
    "seeds": [],
    "statement": "No random choices or probabilistic sampling are used.",
}

COMPLETION = {
    "status": "complete",
    "all_declared_exact_checks_passed": True,
    "deterministic_artifact": True,
    "unauthenticated_run_measurements_in_artifact": False,
}

DISCLAIMERS = [
    "The 197-dimensional Jacobian kernel is a Zariski tangent space, not a component dimension.",
    "The 54-dimensional N is a deterministic linear complement, not a geometric, formal, or normal slice.",
    "The Jacobian cokernel is an obstruction container here, not a certified miniversal obstruction space.",
    "Quadratic obstruction vanishing proves unrestricted second-order lifting only; all third- and higher-order lifting questions remain unknown.",
    "Smoothness, reducedness, local and global component dimensions, and whether the orbit sweep is a component remain unknown.",
    "The Laurent family is defined on G_m; b=0 and b=infinity are not fibers and their compactified behavior remains unknown.",
]

CONVENTIONS = {
    "characteristic": 2,
    "source_term_numbering": "zero-based",
    "factor_order": ["U", "V", "W"],
    "factor_bit_index": "4*row+column, little-endian",
    "domain_column_index": "((leg*49+term)*16+entry)",
    "tensor_bit_index": "256*i+16*j+k",
    "family_parameter": {
        "base_coordinate": "b",
        "t": "b+1",
        "s": "1+b^-1",
        "domain": "Spec(F_2[b,b^-1])",
    },
    "elimination": "left-to-right columns, highest-set-coordinate pivots",
    "extension_field_encoding": "integers 0..511 in the polynomial basis",
    "fixed_moving_order": "fixed terms in source order, then U/V/W entries; moving terms 1,14,29,37,42",
    "determinant_row_order": "descending selected tensor/domain coordinate; signs are immaterial in characteristic two",
}


class CheckFailure(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CheckFailure(message)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def bit_positions(value: int):
    while value:
        low = value & -value
        yield low.bit_length() - 1
        value ^= low


@functools.lru_cache(maxsize=None)
def outer3(first: int, second: int, third: int) -> int:
    result = 0
    for i in bit_positions(first):
        for j in bit_positions(second):
            for k in bit_positions(third):
                result ^= 1 << (256 * i + 16 * j + k)
    return result


def parse_source(path: Path) -> tuple[list[tuple[int, int, int]], dict]:
    raw = path.read_bytes()
    digest = sha256_bytes(raw)
    require(digest == SOURCE_SHA256, f"canonical source hash mismatch: {digest}")
    lines = raw.decode("ascii").splitlines()
    require(len(lines) == 4, f"source must have four lines, got {len(lines)}")
    header = [int(x) for x in lines[0].split()]
    require(header == [4, 4, 4, 49], f"unexpected source header: {header}")
    legs = []
    for line in lines[1:]:
        values = [int(x) for x in line.split()]
        require(len(values) == R * FACTOR_DIM, "source factor row has wrong length")
        require(all(x in (0, 1) for x in values), "source contains a nonbinary entry")
        legs.append(
            [
                sum(values[FACTOR_DIM * term + entry] << entry for entry in range(FACTOR_DIM))
                for term in range(R)
            ]
        )
    terms = list(zip(*legs))
    require(len(terms) == R, "wrong source term count")
    metadata = {
        "repository_path": FIXTURE_REPOSITORY_PATH,
        "sha256": digest,
        "header": header,
        "bytes": len(raw),
    }
    return terms, metadata


def xor_coefficient(target: dict[int, int], exponent: int, value: int) -> None:
    if not value:
        return
    target[exponent] = target.get(exponent, 0) ^ value
    if target[exponent] == 0:
        del target[exponent]


def outer_coefficients(
    first: dict[int, int], second: dict[int, int], third: dict[int, int]
) -> dict[int, int]:
    result: dict[int, int] = {}
    for ea, a in first.items():
        for eb, b in second.items():
            for ec, c in third.items():
                xor_coefficient(result, ea + eb + ec, outer3(a, b, c))
    return result


def add_laurent(target: dict[int, int], source: dict[int, int]) -> None:
    for exponent, value in source.items():
        xor_coefficient(target, exponent, value)


def family_factor(base: int, update: int, mode: str) -> dict[int, int]:
    require(mode in ("s", "t"), "unknown family update mode")
    result = {0: base ^ update} if base ^ update else {}
    if update:
        result[-1 if mode == "s" else 1] = update
    return result


def construct_family(
    terms: list[tuple[int, int, int]],
) -> list[tuple[dict[int, int], dict[int, int], dict[int, int]]]:
    family = []
    for term, triple in enumerate(terms):
        row = []
        for leg, base in enumerate(triple):
            su = S_UPDATES.get(term, {}).get(leg, 0)
            tu = T_UPDATES.get(term, {}).get(leg, 0)
            require(not (su and tu), "one factor cannot have both update modes")
            if su:
                row.append(family_factor(base, su, "s"))
            elif tu:
                row.append(family_factor(base, tu, "t"))
            else:
                row.append({0: base})
        family.append(tuple(row))
    return family


def family_specification(terms: list[tuple[int, int, int]]) -> dict:
    selected_masks = {
        str(term): {"U": f"{terms[term][0]:04x}", "V": f"{terms[term][1]:04x}", "W": f"{terms[term][2]:04x}"}
        for term in MOVING_TERMS
    }
    encode = lambda updates: {
        str(term): {"UVW"[leg]: f"{mask:04x}" for leg, mask in sorted(row.items())}
        for term, row in sorted(updates.items())
    }
    return {
        "moving_terms": list(MOVING_TERMS),
        "selected_source_masks": selected_masks,
        "s_updates": encode(S_UPDATES),
        "t_updates": encode(T_UPDATES),
        "s_laurent_expression": "1+b^-1",
        "t_laurent_expression": "1+b",
    }


def base_tensor(terms: list[tuple[int, int, int]]) -> int:
    value = 0
    for first, second, third in terms:
        value ^= outer3(first, second, third)
    return value


def family_tensor(
    family: list[tuple[dict[int, int], dict[int, int], dict[int, int]]]
) -> dict[int, int]:
    result: dict[int, int] = {}
    for first, second, third in family:
        add_laurent(result, outer_coefficients(first, second, third))
    return result


def binary_derivative_columns(term: tuple[int, int, int]) -> list[int]:
    first, second, third = term
    return (
        [outer3(1 << entry, second, third) for entry in range(FACTOR_DIM)]
        + [outer3(first, 1 << entry, third) for entry in range(FACTOR_DIM)]
        + [outer3(first, second, 1 << entry) for entry in range(FACTOR_DIM)]
    )


def reduce_plain(basis: dict[int, int], value: int) -> int:
    for pivot in sorted(basis, reverse=True):
        if (value >> pivot) & 1:
            value ^= basis[pivot]
    return value


def add_plain(basis: dict[int, int], value: int) -> bool:
    while value:
        pivot = value.bit_length() - 1
        if pivot in basis:
            value ^= basis[pivot]
        else:
            basis[pivot] = value
            return True
    return False


def generic_jacobian_split(
    terms: list[tuple[int, int, int]],
    family: list[tuple[dict[int, int], dict[int, int], dict[int, int]]],
):
    fixed_basis: dict[int, int] = {}
    fixed_pivot_columns = []
    moving = set(MOVING_TERMS)
    for term in range(R):
        if term in moving:
            continue
        for local, column in enumerate(binary_derivative_columns(terms[term])):
            leg, entry = divmod(local, FACTOR_DIM)
            global_column = (leg * R + term) * FACTOR_DIM + entry
            if add_plain(fixed_basis, column):
                fixed_pivot_columns.append(global_column)
    quotient_columns: list[dict[int, int]] = []
    quotient_global_columns = []
    for term in MOVING_TERMS:
        first, second, third = family[term]
        columns = []
        for entry in range(FACTOR_DIM):
            columns.append(outer_coefficients({0: 1 << entry}, second, third))
        for entry in range(FACTOR_DIM):
            columns.append(outer_coefficients(first, {0: 1 << entry}, third))
        for entry in range(FACTOR_DIM):
            columns.append(outer_coefficients(first, second, {0: 1 << entry}))
        for local, column in enumerate(columns):
            reduced = {}
            for exponent, value in column.items():
                remainder = reduce_plain(fixed_basis, value)
                if remainder:
                    reduced[exponent] = remainder
            quotient_columns.append(reduced)
            leg, entry = divmod(local, FACTOR_DIM)
            quotient_global_columns.append((leg * R + term) * FACTOR_DIM + entry)
    return fixed_basis, fixed_pivot_columns, quotient_columns, quotient_global_columns


def gf_mul(first: int, second: int) -> int:
    result = 0
    while second:
        if second & 1:
            result ^= first
        second >>= 1
        first <<= 1
        if first >> GF_DEGREE:
            first ^= GF_MODULUS
    return result


def gf_pow(value: int, exponent: int) -> int:
    if exponent < 0:
        return gf_pow(gf_inv(value), -exponent)
    result = 1
    while exponent:
        if exponent & 1:
            result = gf_mul(result, value)
        value = gf_mul(value, value)
        exponent >>= 1
    return result


def gf_inv(value: int) -> int:
    if value == 0:
        raise ZeroDivisionError("zero has no inverse")
    return gf_pow(value, GF_ORDER - 2)


def verify_extension_field() -> dict[int, int]:
    logs = {1: 0}
    value = 1
    for exponent in range(1, GF_ORDER - 1):
        value = gf_mul(value, GF_PRIMITIVE)
        require(value not in logs, "primitive-element cycle repeated early")
        logs[value] = exponent
    require(gf_mul(value, GF_PRIMITIVE) == 1, "primitive-element cycle does not close")
    require(len(logs) == GF_ORDER - 1, "modulus does not produce the claimed field cycle")
    return logs


def vector_scale(vector: tuple[int, ...], scalar: int) -> tuple[int, ...]:
    result = [0] * GF_DEGREE
    for input_bit, plane in enumerate(vector):
        if not plane:
            continue
        product = gf_mul(1 << input_bit, scalar)
        for output_bit in bit_positions(product):
            result[output_bit] ^= plane
    return tuple(result)


def vector_xor_multiple(
    vector: tuple[int, ...], basis_vector: tuple[int, ...], scalar: int
) -> tuple[int, ...]:
    multiple = vector_scale(basis_vector, scalar)
    return tuple(a ^ b for a, b in zip(vector, multiple))


def vector_coefficient(vector: tuple[int, ...], coordinate: int) -> int:
    return sum(((plane >> coordinate) & 1) << bit for bit, plane in enumerate(vector))


def vector_pivot(vector: tuple[int, ...]) -> int:
    union = 0
    for plane in vector:
        union |= plane
    return union.bit_length() - 1


def evaluate_laurent_column(column: dict[int, int], value: int) -> tuple[int, ...]:
    result = [0] * GF_DEGREE
    for exponent, plane in column.items():
        scalar = gf_pow(value, exponent)
        for bit in bit_positions(scalar):
            result[bit] ^= plane
    return tuple(result)


def extension_rank(
    columns: list[dict[int, int]], value: int, profile: bool = False
):
    basis: dict[int, tuple[tuple[int, ...], int]] = {}
    pivot_columns = []
    for column_index, column in enumerate(columns):
        vector = evaluate_laurent_column(column, value)
        while any(vector):
            pivot = vector_pivot(vector)
            coefficient = vector_coefficient(vector, pivot)
            if pivot in basis:
                basis_vector, _ = basis[pivot]
                scalar = gf_mul(coefficient, gf_inv(vector_coefficient(basis_vector, pivot)))
                vector = vector_xor_multiple(vector, basis_vector, scalar)
            else:
                vector = vector_scale(vector, gf_inv(coefficient))
                basis[pivot] = (vector, column_index)
                pivot_columns.append(column_index)
                break
    if profile:
        return len(basis), pivot_columns, sorted(basis, reverse=True)
    return len(basis)


def determinant_on_selected_minor(
    columns: list[dict[int, int]], selected_columns: list[int], row_mask: int, value: int
) -> int:
    basis: dict[int, tuple[int, ...]] = {}
    determinant = 1
    for column_index in selected_columns:
        restricted = {
            exponent: plane & row_mask for exponent, plane in columns[column_index].items()
        }
        vector = evaluate_laurent_column(restricted, value)
        while any(vector):
            pivot = vector_pivot(vector)
            coefficient = vector_coefficient(vector, pivot)
            if pivot in basis:
                vector = vector_xor_multiple(vector, basis[pivot], coefficient)
            else:
                determinant = gf_mul(determinant, coefficient)
                vector = vector_scale(vector, gf_inv(coefficient))
                basis[pivot] = vector
                break
        else:
            return 0
    return determinant if len(basis) == len(selected_columns) else 0


def pack_u16(values: Iterable[int]) -> bytes:
    return b"".join(int(value).to_bytes(2, "little") for value in values)


def rank_record(ranks: list[int]) -> dict:
    histogram = collections.Counter(ranks)
    return {
        "by_field_element": ranks,
        "histogram": {str(rank): count for rank, count in sorted(histogram.items())},
        "sha256_u8": sha256_bytes(bytes(ranks)),
    }


def determinant_record(values: list[int], exponent: int, degree_bound: int) -> dict:
    require(
        all(value == gf_pow(field_element, exponent) for field_element, value in enumerate(values)),
        f"selected determinant is not b^{exponent}",
    )
    require(max(degree_bound, exponent) < GF_ORDER, "determinant identity lacks enough roots")
    return {
        "identity": f"b^{exponent}",
        "monomial_exponent": exponent,
        "degree_bound": degree_bound,
        "evaluation_count": len(values),
        "zero_count": sum(value == 0 for value in values),
        "values_sha256_u16le": sha256_bytes(pack_u16(values)),
        "identity_proof": f"equality at {len(values)} elements and degree < {GF_ORDER}",
    }


def add_domain_block(
    target: dict[int, int], factor: dict[int, int], leg: int, term: int
) -> None:
    shift = (leg * R + term) * FACTOR_DIM
    for exponent, mask in factor.items():
        xor_coefficient(target, exponent, mask << shift)


def left_matrix_unit(mask: int, row: int, column: int) -> int:
    source_row = (mask >> (N * column)) & 0xF
    return source_row << (N * row)


def right_matrix_unit(mask: int, row: int, column: int) -> int:
    result = 0
    for i in range(N):
        result |= ((mask >> (N * i + row)) & 1) << (N * i + column)
    return result


def connected_symmetry_columns(
    family: list[tuple[dict[int, int], dict[int, int], dict[int, int]]]
) -> list[dict[int, int]]:
    columns = []
    for term, (first, second, third) in enumerate(family):
        column: dict[int, int] = {}
        add_domain_block(column, first, 0, term)
        add_domain_block(column, second, 1, term)
        columns.append(column)
        column = {}
        add_domain_block(column, first, 0, term)
        add_domain_block(column, third, 2, term)
        columns.append(column)
    for vertex in range(3):
        for row in range(N):
            for column_index in range(N):
                column = {}
                for term, (first, second, third) in enumerate(family):
                    if vertex == 0:
                        add_domain_block(
                            column,
                            {e: left_matrix_unit(x, row, column_index) for e, x in first.items()},
                            0,
                            term,
                        )
                        add_domain_block(
                            column,
                            {e: right_matrix_unit(x, row, column_index) for e, x in third.items()},
                            2,
                            term,
                        )
                    elif vertex == 1:
                        add_domain_block(
                            column,
                            {e: right_matrix_unit(x, row, column_index) for e, x in first.items()},
                            0,
                            term,
                        )
                        add_domain_block(
                            column,
                            {e: left_matrix_unit(x, row, column_index) for e, x in second.items()},
                            1,
                            term,
                        )
                    else:
                        add_domain_block(
                            column,
                            {e: right_matrix_unit(x, row, column_index) for e, x in second.items()},
                            1,
                            term,
                        )
                        add_domain_block(
                            column,
                            {e: left_matrix_unit(x, row, column_index) for e, x in third.items()},
                            2,
                            term,
                        )
                columns.append(column)
    require(len(columns) == 146, "wrong connected-symmetry column count")
    return columns


def family_tangent_column() -> dict[int, int]:
    column: dict[int, int] = {}
    for term, row in S_UPDATES.items():
        for leg, mask in row.items():
            add_domain_block(column, {-2: mask}, leg, term)
    for term, row in T_UPDATES.items():
        for leg, mask in row.items():
            add_domain_block(column, {0: mask}, leg, term)
    return column


def decode_laurent_variation(
    variation: dict[int, int],
) -> list[tuple[dict[int, int], dict[int, int], dict[int, int]]]:
    blocks = [[{} for _ in range(3)] for _ in range(R)]
    for exponent, vector in variation.items():
        for leg in range(3):
            for term in range(R):
                shift = (leg * R + term) * FACTOR_DIM
                mask = (vector >> shift) & 0xFFFF
                if mask:
                    blocks[term][leg][exponent] = mask
    return [tuple(row) for row in blocks]


def jacobian_apply_laurent(
    family: list[tuple[dict[int, int], dict[int, int], dict[int, int]]],
    variation: dict[int, int],
) -> dict[int, int]:
    decoded = decode_laurent_variation(variation)
    result: dict[int, int] = {}
    for (first, second, third), (dfirst, dsecond, dthird) in zip(family, decoded):
        add_laurent(result, outer_coefficients(dfirst, second, third))
        add_laurent(result, outer_coefficients(first, dsecond, third))
        add_laurent(result, outer_coefficients(first, second, dthird))
    return result


def hash_fixed_width(values: Iterable[int], byte_width: int) -> str:
    digest = hashlib.sha256()
    for value in values:
        digest.update(value.to_bytes(byte_width, "little"))
    return digest.hexdigest()


def generic_claims(
    terms: list[tuple[int, int, int]],
    family: list[tuple[dict[int, int], dict[int, int], dict[int, int]]],
) -> tuple[dict, list[dict[int, int]], dict[int, int]]:
    fixed_basis, fixed_columns, quotient, quotient_global = generic_jacobian_split(terms, family)
    require(len(fixed_basis) == EXPECTED["fixed_rank"], "fixed Jacobian rank changed")
    require(len(quotient) == 240, "wrong moving-column count")
    cleared_quotient = [{exponent + 1: value for exponent, value in col.items()} for col in quotient]
    selected_rank, selected_columns, selected_rows = extension_rank(quotient, 1, profile=True)
    require(selected_rank == EXPECTED["quotient_rank"], "quotient rank at b=1 changed")
    row_mask = sum(1 << row for row in selected_rows)
    ranks = [extension_rank(cleared_quotient, value) for value in range(GF_ORDER)]
    require(ranks[0] == 46, "cleared quotient rank at zero changed")
    require(all(rank == EXPECTED["quotient_rank"] for rank in ranks[1:]), "quotient G_m rank changed")
    determinant_values = [
        determinant_on_selected_minor(cleared_quotient, selected_columns, row_mask, value)
        for value in range(GF_ORDER)
    ]
    determinant = determinant_record(
        determinant_values,
        EXPECTED["quotient_minor_exponent"],
        2 * EXPECTED["quotient_rank"],
    )
    upper_degree = 2 * (EXPECTED["quotient_rank"] + 1)
    require(upper_degree < GF_ORDER, "quotient upper-minor root bound failed")
    require(max(ranks) < EXPECTED["quotient_rank"] + 1, "a quotient upper minor may be nonzero")
    return {
        "fixed_block": {
            "columns": 44 * 48,
            "rank": len(fixed_basis),
            "pivot_columns": fixed_columns,
            "pivot_rows_descending": sorted(fixed_basis, reverse=True),
            "echelon_basis_sha256_512le": hash_fixed_width(
                (fixed_basis[pivot] for pivot in sorted(fixed_basis, reverse=True)), 512
            ),
        },
        "moving_quotient": {
            "rows_before_zero_suppression": TENSOR_DIM - len(fixed_basis),
            "columns": len(quotient),
            "global_columns": quotient_global,
            "laurent_exponents": [-1, 0, 1],
            "clearing_power_per_column": 1,
            "cleared_entry_degree": 2,
            "rank_evaluations": rank_record(ranks),
            "selected_minor": {
                "size": selected_rank,
                "columns_within_moving_quotient": selected_columns,
                "global_columns": [quotient_global[index] for index in selected_columns],
                "rows_descending": selected_rows,
                "determinant": determinant,
                "unscaled_determinant": "b^11",
            },
            "upper_rank_certificate": {
                "minor_size": EXPECTED["quotient_rank"] + 1,
                "degree_bound": upper_degree,
                "roots": GF_ORDER,
                "all_evaluated_ranks_at_most": max(ranks),
                "conclusion": "all 198-minors vanish identically over F_2[b]",
            },
            "rank_on_Gm": EXPECTED["quotient_rank"],
        },
        "full_jacobian": {
            "rows": TENSOR_DIM,
            "columns": DOMAIN_DIM,
            "rank_on_Gm": EXPECTED["jacobian_rank"],
            "kernel_dimension_on_Gm": EXPECTED["kernel_dimension"],
            "rank_jump_locus_on_Gm": [],
            "proof": "fixed rank 1958 plus quotient rank 197",
        },
    }, quotient, fixed_basis


def symmetry_and_sweep_claims(
    family: list[tuple[dict[int, int], dict[int, int], dict[int, int]]]
) -> tuple[dict, list[dict[int, int]], dict[int, int]]:
    symmetry = connected_symmetry_columns(family)
    symmetry_kernel_residuals = [jacobian_apply_laurent(family, column) for column in symmetry]
    require(all(not residual for residual in symmetry_kernel_residuals), "a dH column is not in ker J")
    cleared = [{exponent + 1: value for exponent, value in column.items()} for column in symmetry]
    rank_at_one, selected_columns, selected_rows = extension_rank(symmetry, 1, profile=True)
    require(rank_at_one == EXPECTED["symmetry_rank"], "connected dH rank at b=1 changed")
    ranks = [extension_rank(cleared, value) for value in range(GF_ORDER)]
    require(ranks[0] == 9, "cleared dH rank at zero changed")
    require(all(rank == EXPECTED["symmetry_rank"] for rank in ranks[1:]), "dH rank jumps on G_m")
    row_mask = sum(1 << row for row in selected_rows)
    determinant_values = [
        determinant_on_selected_minor(cleared, selected_columns, row_mask, value)
        for value in range(GF_ORDER)
    ]
    determinant = determinant_record(
        determinant_values,
        EXPECTED["symmetry_minor_exponent"],
        2 * EXPECTED["symmetry_rank"],
    )
    upper_degree = 2 * (EXPECTED["symmetry_rank"] + 1)
    require(upper_degree < GF_ORDER, "dH upper-minor root bound failed")
    require(max(ranks) < EXPECTED["symmetry_rank"] + 1, "a dH upper minor may be nonzero")

    tangent = family_tangent_column()
    require(not jacobian_apply_laurent(family, tangent), "family tangent is not in ker J")
    sweep = symmetry + [tangent]
    cleared_sweep = [{exponent + 2: value for exponent, value in column.items()} for column in sweep]
    sweep_rank_at_one, sweep_columns, sweep_rows = extension_rank(sweep, 1, profile=True)
    require(sweep_rank_at_one == EXPECTED["sweep_rank"], "orbit-sweep rank at b=1 changed")
    require(sweep_columns[-1] == len(symmetry), "selected sweep minor does not use family tangent")
    sweep_ranks = [extension_rank(cleared_sweep, value) for value in range(GF_ORDER)]
    require(sweep_ranks[0] == 1, "cleared sweep rank at zero changed")
    require(all(rank == EXPECTED["sweep_rank"] for rank in sweep_ranks[1:]), "sweep rank jumps on G_m")
    sweep_row_mask = sum(1 << row for row in sweep_rows)
    sweep_determinants = [
        determinant_on_selected_minor(cleared_sweep, sweep_columns, sweep_row_mask, value)
        for value in range(GF_ORDER)
    ]
    sweep_degree = 3 * EXPECTED["symmetry_rank"] + 2
    sweep_determinant = determinant_record(
        sweep_determinants,
        EXPECTED["sweep_minor_exponent"],
        sweep_degree,
    )
    require(sweep_degree < GF_ORDER, "sweep selected-minor root bound failed")
    return {
        "connected_dH": {
            "raw_columns": len(symmetry),
            "term_scaling_columns": 98,
            "sandwich_columns": 48,
            "laurent_exponents": [-1, 0, 1],
            "all_columns_in_generic_jacobian_kernel": True,
            "clearing_power_per_column": 1,
            "rank_evaluations": rank_record(ranks),
            "selected_minor": {
                "size": rank_at_one,
                "columns": selected_columns,
                "rows_descending": selected_rows,
                "determinant": determinant,
                "unscaled_determinant": "1",
            },
            "upper_rank_certificate": {
                "minor_size": EXPECTED["symmetry_rank"] + 1,
                "degree_bound": upper_degree,
                "roots": GF_ORDER,
                "all_evaluated_ranks_at_most": max(ranks),
                "conclusion": "all 144-minors vanish identically over F_2[b]",
            },
            "rank_on_Gm": EXPECTED["symmetry_rank"],
            "rank_jump_locus_on_Gm": [],
        },
        "family_tangent": {
            "ds_db": "b^-2",
            "dt_db": "1",
            "in_generic_jacobian_kernel": True,
        },
        "orbit_sweep_differential": {
            "raw_columns": len(sweep),
            "clearing_power_per_column": 2,
            "rank_evaluations": rank_record(sweep_ranks),
            "selected_minor": {
                "size": sweep_rank_at_one,
                "columns": sweep_columns,
                "rows_descending": sweep_rows,
                "uses_family_tangent": True,
                "determinant": sweep_determinant,
                "unscaled_determinant": "1",
            },
            "rank_on_Gm": EXPECTED["sweep_rank"],
            "family_tangent_outside_connected_orbit": True,
            "rank_jump_locus_on_Gm": [],
        },
        "tangent_dimensions": {
            "jacobian_kernel": EXPECTED["kernel_dimension"],
            "connected_orbit": EXPECTED["symmetry_rank"],
            "normal_tangent_quotient": EXPECTED["normal_tangent_dimension"],
            "orbit_plus_family": EXPECTED["sweep_rank"],
            "tangent_excess_over_orbit_sweep": 53,
            "component_dimension_conclusion": None,
        },
    }, symmetry, tangent


def full_binary_jacobian(terms: list[tuple[int, int, int]]) -> list[int]:
    columns = []
    for leg in range(3):
        for term, (first, second, third) in enumerate(terms):
            if leg == 0:
                columns.extend(outer3(1 << entry, second, third) for entry in range(FACTOR_DIM))
            elif leg == 1:
                columns.extend(outer3(first, 1 << entry, third) for entry in range(FACTOR_DIM))
            else:
                columns.extend(outer3(first, second, 1 << entry) for entry in range(FACTOR_DIM))
    require(len(columns) == DOMAIN_DIM, "wrong full binary Jacobian column count")
    return columns


def echelon_with_dependencies(columns: list[int]):
    basis: dict[int, tuple[int, int]] = {}
    kernel = []
    pivot_columns = []
    for column_index, column in enumerate(columns):
        vector = column
        combination = 1 << column_index
        while vector:
            pivot = vector.bit_length() - 1
            if pivot in basis:
                basis_vector, basis_combination = basis[pivot]
                vector ^= basis_vector
                combination ^= basis_combination
            else:
                basis[pivot] = (vector, combination)
                pivot_columns.append(column_index)
                break
        else:
            kernel.append(combination)
    return basis, kernel, pivot_columns


def image_remainder(basis: dict[int, tuple[int, int]], value: int) -> int:
    for pivot in sorted(basis, reverse=True):
        if (value >> pivot) & 1:
            value ^= basis[pivot][0]
    return value


def apply_column_matrix(columns: list[int], vector: int) -> int:
    result = 0
    for column in bit_positions(vector):
        result ^= columns[column]
    return result


def evaluate_binary_domain_column(column: dict[int, int]) -> int:
    result = 0
    for value in column.values():
        result ^= value
    return result


def decode_binary_variation(variation: int) -> tuple[tuple[int, int, int], ...]:
    result = []
    for term in range(R):
        result.append(
            tuple(
                (variation >> ((leg * R + term) * FACTOR_DIM)) & 0xFFFF
                for leg in range(3)
            )
        )
    return tuple(result)


def quadratic_coefficient(
    terms: list[tuple[int, int, int]], decoded: tuple[tuple[int, int, int], ...]
) -> int:
    result = 0
    for (first, second, third), (dfirst, dsecond, dthird) in zip(terms, decoded):
        result ^= outer3(dfirst, dsecond, third)
        result ^= outer3(dfirst, second, dthird)
        result ^= outer3(first, dsecond, dthird)
    return result


def mixed_coefficient(
    terms: list[tuple[int, int, int]],
    first_decoded: tuple[tuple[int, int, int], ...],
    second_decoded: tuple[tuple[int, int, int], ...],
) -> int:
    result = 0
    for (u, v, w), (du, dv, dw), (eu, ev, ew) in zip(
        terms, first_decoded, second_decoded
    ):
        result ^= outer3(du, ev, w) ^ outer3(eu, dv, w)
        result ^= outer3(du, v, ew) ^ outer3(eu, v, dw)
        result ^= outer3(u, dv, ew) ^ outer3(u, ev, dw)
    return result


def residual_audit(residuals: Iterable[int], expected_count: int) -> dict:
    digest = hashlib.sha256()
    count = 0
    nonzero = 0
    weight_sum = 0
    for residual in residuals:
        count += 1
        digest.update(residual.to_bytes(512, "little"))
        if residual:
            nonzero += 1
            weight_sum += residual.bit_count()
    require(count == expected_count, f"residual audit count {count} != {expected_count}")
    require(nonzero == 0, f"{nonzero} obstruction coefficients survive in coker J")
    return {
        "count": count,
        "nonzero_remainders": nonzero,
        "nonzero_weight_sum": weight_sum,
        "remainders_sha256_512le": digest.hexdigest(),
    }


def binary_obstruction_claims(
    terms: list[tuple[int, int, int]], symmetry: list[dict[int, int]]
) -> dict:
    jacobian = full_binary_jacobian(terms)
    image_basis, kernel_basis, pivot_columns = echelon_with_dependencies(jacobian)
    require(len(image_basis) == EXPECTED["jacobian_rank"], "binary Jacobian rank changed")
    require(len(kernel_basis) == EXPECTED["kernel_dimension"], "binary kernel dimension changed")
    require(all(apply_column_matrix(jacobian, vector) == 0 for vector in kernel_basis), "bad kernel dependency")

    raw_gauge = [evaluate_binary_domain_column(column) for column in symmetry]
    require(all(apply_column_matrix(jacobian, vector) == 0 for vector in raw_gauge), "raw gauge is not in ker J")
    gauge_echelon, _, gauge_pivot_columns = echelon_with_dependencies(raw_gauge)
    require(len(gauge_echelon) == EXPECTED["symmetry_rank"], "binary gauge rank changed")
    gauge_basis = [gauge_echelon[pivot][0] for pivot in sorted(gauge_echelon, reverse=True)]

    combined_basis: dict[int, int] = {}
    for vector in gauge_basis:
        require(add_plain(combined_basis, vector), "gauge echelon basis is dependent")
    complement = []
    for vector in kernel_basis:
        if add_plain(combined_basis, vector):
            complement.append(vector)
    require(len(complement) == EXPECTED["normal_tangent_dimension"], "complement dimension changed")
    require(len(combined_basis) == EXPECTED["kernel_dimension"], "gauge plus complement does not span kernel")
    require(all(apply_column_matrix(jacobian, vector) == 0 for vector in complement), "complement left ker J")

    gauge_decoded = [decode_binary_variation(vector) for vector in gauge_basis]
    complement_decoded = [decode_binary_variation(vector) for vector in complement]
    kernel_decoded = [decode_binary_variation(vector) for vector in kernel_basis]

    qg = residual_audit(
        (
            image_remainder(image_basis, quadratic_coefficient(terms, decoded))
            for decoded in gauge_decoded
        ),
        len(gauge_decoded),
    )
    bgg_count = len(gauge_decoded) * (len(gauge_decoded) - 1) // 2
    bgg = residual_audit(
        (
            image_remainder(
                image_basis, mixed_coefficient(terms, gauge_decoded[i], gauge_decoded[j])
            )
            for i in range(len(gauge_decoded))
            for j in range(i + 1, len(gauge_decoded))
        ),
        bgg_count,
    )
    bng_count = len(complement_decoded) * len(gauge_decoded)
    bng = residual_audit(
        (
            image_remainder(
                image_basis, mixed_coefficient(terms, complement_decoded[i], gauge_decoded[j])
            )
            for i in range(len(complement_decoded))
            for j in range(len(gauge_decoded))
        ),
        bng_count,
    )
    qn = residual_audit(
        (
            image_remainder(image_basis, quadratic_coefficient(terms, decoded))
            for decoded in complement_decoded
        ),
        len(complement_decoded),
    )
    bnn_count = len(complement_decoded) * (len(complement_decoded) - 1) // 2
    bnn = residual_audit(
        (
            image_remainder(
                image_basis,
                mixed_coefficient(terms, complement_decoded[i], complement_decoded[j]),
            )
            for i in range(len(complement_decoded))
            for j in range(i + 1, len(complement_decoded))
        ),
        bnn_count,
    )

    qk = residual_audit(
        (
            image_remainder(image_basis, quadratic_coefficient(terms, decoded))
            for decoded in kernel_decoded
        ),
        len(kernel_decoded),
    )
    bkk_count = len(kernel_decoded) * (len(kernel_decoded) - 1) // 2
    bkk = residual_audit(
        (
            image_remainder(
                image_basis, mixed_coefficient(terms, kernel_decoded[i], kernel_decoded[j])
            )
            for i in range(len(kernel_decoded))
            for j in range(i + 1, len(kernel_decoded))
        ),
        bkk_count,
    )

    return {
        "binary_linear_algebra": {
            "jacobian_rows": TENSOR_DIM,
            "jacobian_columns": DOMAIN_DIM,
            "jacobian_rank": len(image_basis),
            "kernel_dimension": len(kernel_basis),
            "cokernel_dimension": TENSOR_DIM - len(image_basis),
            "jacobian_columns_sha256_512le": hash_fixed_width(jacobian, 512),
            "jacobian_pivot_columns": pivot_columns,
            "jacobian_pivot_rows_descending": sorted(image_basis, reverse=True),
            "kernel_basis_sha256_294le": hash_fixed_width(kernel_basis, 294),
            "raw_gauge_columns": len(raw_gauge),
            "raw_gauge_rank": len(gauge_echelon),
            "raw_gauge_pivot_columns": gauge_pivot_columns,
            "gauge_basis_sha256_294le": hash_fixed_width(gauge_basis, 294),
            "complement_dimension": len(complement),
            "complement_basis_sha256_294le": hash_fixed_width(complement, 294),
            "direct_sum_rank": len(combined_basis),
            "decomposition": "ker(J) = image(dH) direct_sum N as vector spaces",
            "slice_claim": False,
        },
        "quadratic_cokernel_reductions": {
            "gauge_diagonal_Q": qg,
            "gauge_gauge_mixed_B": bgg,
            "complement_gauge_mixed_B": bng,
            "complement_diagonal_Q": qn,
            "complement_complement_mixed_B": bnn,
            "deterministic_kernel_diagonal_Q": qk,
            "deterministic_kernel_mixed_B": bkk,
            "total_decomposition_coefficients": sum(
                record["count"] for record in (qg, bgg, bng, qn, bnn)
            ),
            "total_kernel_basis_coefficients": qk["count"] + bkk["count"],
            "quadratic_obstruction_map_is_zero": True,
            "valid_after_every_scalar_extension_of_F2": True,
            "gauge_independent": True,
            "all_first_order_tangents_have_unrestricted_second_order_lifts": True,
            "miniversal_obstruction_claim": False,
            "higher_order_claim": False,
        },
    }


def compute_claims(source_path: Path) -> tuple[dict, dict, dict]:
    verify_extension_field()
    terms, source_metadata = parse_source(source_path)
    family = construct_family(terms)
    source_tensor = base_tensor(terms)
    represented = family_tensor(family)
    require(represented == {0: source_tensor}, "the Laurent family does not preserve the source tensor")
    family_claim = {
        **family_specification(terms),
        "tensor_identity": {
            "verified": True,
            "nonzero_laurent_exponents": sorted(represented),
            "source_tensor_sha256_512le": hash_fixed_width([source_tensor], 512),
        },
    }
    generic, _, _ = generic_claims(terms, family)
    symmetry_claim, symmetry, _ = symmetry_and_sweep_claims(family)
    obstruction = binary_obstruction_claims(terms, symmetry)
    claims = {
        "family": family_claim,
        "generic_jacobian": generic,
        "connected_symmetry_and_sweep": symmetry_claim,
        "binary_obstruction": obstruction,
        "logical_conclusions": {
            "jacobian_rank_on_Gm": EXPECTED["jacobian_rank"],
            "jacobian_rank_jump_locus_on_Gm": [],
            "connected_dH_rank_on_Gm": EXPECTED["symmetry_rank"],
            "connected_dH_rank_jump_locus_on_Gm": [],
            "orbit_sweep_differential_rank_on_Gm": EXPECTED["sweep_rank"],
            "normal_tangent_dimension": EXPECTED["normal_tangent_dimension"],
            "binary_quadratic_obstruction_is_zero": True,
            "binary_quadratic_obstruction_is_gauge_independent": True,
            "component_dimension": None,
            "higher_obstructions": None,
        },
    }
    field = {
        "name": "GF(2^9)",
        "degree": GF_DEGREE,
        "order": GF_ORDER,
        "modulus_integer": GF_MODULUS,
        "modulus_polynomial": "x^9+x^4+1",
        "primitive_element_integer": GF_PRIMITIVE,
        "enumeration": "integers 0 through 511 in polynomial-basis encoding",
        "all_elements_evaluated": True,
        "primitive_cycle_length": GF_ORDER - 1,
    }
    return source_metadata, field, claims


def checker_metadata() -> dict:
    path = Path(__file__).resolve()
    return {
        "repository_path": REPOSITORY_PATH,
        "sha256": sha256_file(path),
        "implementation": "Python standard library; exact integer, bitset, and GF(512) arithmetic",
    }


def validated_generation_base() -> str:
    existence = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "cat-file", "-e", f"{BASE_GIT_REVISION}^{{commit}}"],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    require(existence.returncode == 0, f"generation base does not exist: {BASE_GIT_REVISION}")
    ancestry = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "merge-base", "--is-ancestor", BASE_GIT_REVISION, "HEAD"],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    require(
        ancestry.returncode == 0,
        f"generation base is not an ancestor of current HEAD: {BASE_GIT_REVISION}",
    )
    return BASE_GIT_REVISION


def deterministic_provenance(source: dict) -> dict:
    return {
        "source_fixture": source,
        "original_external_locator": {
            "path": ORIGINAL_EXTERNAL_LOCATOR,
            "accessed": False,
            "role": "historical provenance only",
        },
        "owned_script": checker_metadata(),
        "repository": {
            "base_git_revision": validated_generation_base(),
            "base_validation": "must exist and be an ancestor of current HEAD",
            "git_mutation_performed": False,
        },
        "commands": {
            "working_directory": "repository root",
            "generate": GENERATION_COMMAND,
            "check": CHECK_COMMAND,
        },
    }


def canonical_payload_bytes(payload: dict) -> bytes:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def encode_artifact(artifact: dict) -> bytes:
    return (json.dumps(artifact, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode("utf-8")


def authenticate_payload(payload: dict) -> dict:
    result = dict(payload)
    result["authentication"] = {
        "algorithm": "SHA-256",
        "canonicalization": "UTF-8 JSON, sort_keys=True, separators=(',', ':'), ensure_ascii=True",
        "scope": "all top-level fields except authentication",
        "payload_sha256": sha256_bytes(canonical_payload_bytes(payload)),
    }
    return result


def verify_artifact_authentication(artifact: dict, artifact_bytes: bytes) -> None:
    authentication = artifact.get("authentication")
    require(isinstance(authentication, dict), "artifact authentication is missing")
    payload = {key: value for key, value in artifact.items() if key != "authentication"}
    expected = authenticate_payload(payload)["authentication"]
    compare_exact("payload authentication", expected, authentication)
    require(encode_artifact(artifact) == artifact_bytes, "artifact bytes are not in deterministic encoding")


def build_artifact(source_path: Path) -> dict:
    require(source_path.resolve() == SOURCE.resolve(), "generation requires the default canonical source")
    source, field, claims = compute_claims(source_path)
    payload = {
        "schema": SCHEMA,
        "provenance": deterministic_provenance(source),
        "coefficient_fields": COEFFICIENT_FIELDS,
        "randomness": RANDOMNESS,
        "limits": LIMITS,
        "completion": COMPLETION,
        "conventions": CONVENTIONS,
        "field": field,
        "claims": claims,
        "disclaimers": DISCLAIMERS,
    }
    return authenticate_payload(payload)


def atomic_write(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
        directory_descriptor = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(directory_descriptor)
        finally:
            os.close(directory_descriptor)
    except BaseException:
        temporary.unlink(missing_ok=True)
        raise


def compare_exact(label: str, actual, expected) -> None:
    if actual != expected:
        raise CheckFailure(f"artifact mismatch in {label}")


def check_artifact(artifact_path: Path, source_path: Path, start: float) -> None:
    require(source_path.resolve() == SOURCE.resolve(), "checking requires the default canonical source")
    artifact_bytes = artifact_path.read_bytes()
    artifact = json.loads(artifact_bytes)
    verify_artifact_authentication(artifact, artifact_bytes)
    require(artifact.get("schema") == SCHEMA, "artifact schema mismatch")
    compare_exact("limits", LIMITS, artifact.get("limits"))
    compare_exact("completion", COMPLETION, artifact.get("completion"))
    compare_exact("coefficient fields", COEFFICIENT_FIELDS, artifact.get("coefficient_fields"))
    compare_exact("randomness", RANDOMNESS, artifact.get("randomness"))
    compare_exact("conventions", CONVENTIONS, artifact.get("conventions"))
    compare_exact("disclaimers", DISCLAIMERS, artifact.get("disclaimers"))

    source, field, claims = compute_claims(source_path)
    compare_exact("deterministic provenance", deterministic_provenance(source), artifact["provenance"])
    compare_exact("finite field", field, artifact["field"])
    compare_exact("all exact claims", claims, artifact["claims"])

    elapsed = time.monotonic() - start
    usage = resource.getrusage(resource.RUSAGE_SELF)
    require(elapsed <= LIMITS["wall_seconds_advisory"], "checker exceeded recorded wall limit")
    require(usage.ru_maxrss <= LIMITS["peak_rss_mib_advisory"] * 1024, "checker exceeded recorded RSS limit")

    print(f"PASS schema={SCHEMA}")
    print(f"base_git_revision={BASE_GIT_REVISION}")
    print(f"source_fixture={source['repository_path']}")
    print(f"source_sha256={source['sha256']}")
    print(f"checker_sha256={checker_metadata()['sha256']}")
    print(f"artifact={artifact_path.resolve()}")
    print(f"artifact_payload_sha256={artifact['authentication']['payload_sha256']}")
    print(f"artifact_sha256={sha256_bytes(artifact_bytes)}")
    print("randomness=none seeds=none completion=complete")
    print("family_tensor_identity=PASS over F_2[b,b^-1]")
    print("generic_jacobian=fixed_rank:1958 quotient_rank_Gm:197 rank_Gm:2155 kernel_Gm:197 jump_locus_Gm:empty")
    print("generic_jacobian_selected_cleared_minor=det:b^208 unscaled:b^11")
    print("connected_dH=raw_columns:146 rank_Gm:143 jump_locus_Gm:empty selected_unscaled_minor:1")
    print("orbit_sweep=raw_columns:147 differential_rank_Gm:144 family_tangent_outside_dH:true selected_unscaled_minor:1")
    print("normal_tangent_dimension=54 tangent_excess_over_orbit_sweep=53")
    reductions = claims["binary_obstruction"]["quadratic_cokernel_reductions"]
    print(
        "binary_obstruction=J_rank:2155 kernel:197 gauge_rank:143 complement:54 "
        f"decomposition_coefficients:{reductions['total_decomposition_coefficients']} "
        f"kernel_coefficients:{reductions['total_kernel_basis_coefficients']} "
        "nonzero_coker_remainders:0 quadratic_map_zero:true gauge_independent:true"
    )
    print("NONCLAIM tangent_rank_is_not_component_dimension=true")
    print("NONCLAIM complement_is_not_slice=true")
    print("NONCLAIM jacobian_cokernel_is_not_certified_miniversal=true")
    print("UNKNOWN higher_obstructions_smoothness_reducedness_component_dimensions_and_incidence=true")
    print(
        f"UNAUTHENTICATED_RUN elapsed_seconds={elapsed:.6f} peak_rss_kib={int(usage.ru_maxrss)} "
        f"wall_limit_seconds={LIMITS['wall_seconds_advisory']} rss_limit_mib={LIMITS['peak_rss_mib_advisory']}"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true", help="reconstruct and replay the checked-in artifact")
    mode.add_argument("--generate-artifact", action="store_true", help="regenerate the owned artifact from the canonical source")
    parser.add_argument("--source", type=Path, default=SOURCE)
    parser.add_argument("--artifact", type=Path, default=ARTIFACT)
    args = parser.parse_args()
    start = time.monotonic()
    try:
        if args.generate_artifact:
            artifact = build_artifact(args.source)
            encoded = encode_artifact(artifact)
            atomic_write(args.artifact, encoded)
            elapsed = time.monotonic() - start
            usage = resource.getrusage(resource.RUSAGE_SELF)
            print(f"WROTE {args.artifact.resolve()}")
            print(f"artifact_payload_sha256={artifact['authentication']['payload_sha256']}")
            print(f"artifact_sha256={sha256_bytes(encoded)}")
            print(f"checker_sha256={checker_metadata()['sha256']}")
            print(f"UNAUTHENTICATED_RUN elapsed_seconds={elapsed:.6f} peak_rss_kib={int(usage.ru_maxrss)}")
        else:
            check_artifact(args.artifact, args.source, start)
    except (CheckFailure, FileNotFoundError, ValueError, json.JSONDecodeError, subprocess.CalledProcessError) as error:
        print(f"FAIL {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
