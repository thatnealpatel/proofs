#!/usr/bin/env sage
"""Exact bounded census of binary rank-48 Arai--Ichikawa--Hukushima Plus gateways.

The input is one explicit native 4x4x4 rank-47 scheme.  No directory or archive
is searched.  ``scan`` enumerates a declared finite descriptor domain, replays
every two-term to three-term tensor identity over GF(2), collapses exact
term-order duplicates, and emits certificates and SHA-256 digests as one JSON
document on stdout.  ``replay`` checks an emitted output record from the input
bytes and its representative and alias descriptors.

The six orientation names are permutations (i,j,k) of the three tensor legs.
The three variants are the production-compatible placements of the same Plus
identity.  For oriented source terms

    (a1,b1,c1), (a2,b2,c2)

they are

    0: (a1,b1+b2,c1), (a1+a2,b2,c2), (a1,b2,c1+c2)
    1: (a1,b1,c1+c2), (a2,b1+b2,c2), (a1+a2,b1,c2)
    2: (a1+a2,b1,c1), (a2,b2,c1+c2), (a2,b1+b2,c1).

All sums are XOR.  The paper's displayed Plus is variant 0; permutations,
source order, and the three placements deliberately contain exact descriptor
aliases, which the census records without repeating complete output schemes.

The reduction screen is intentionally cheap and bounded.  In every equal-factor
class and every selected subset I of size at most ``--screen-max-subset-size``,
it forms the exact 16 by 16 complementary matrix

    M_I = sum_(r in I) b_r c_r^T

and computes its GF(2) rank.  A positive defect |I|-rank(M_I) is accompanied by
a deterministic rank factorization and a replayable reduced output.  Defect at
least two is reported separately as a characteristic-two defect-two
opportunity.  A negative screen statement is only about the subsets explicitly
counted in the JSON coverage record.

Typical commands from the repository root are

  sage Programs/BilinearComplexity/rank48_plus_gateway.sage scan /path/to/4x4x4_m47_..._Z2.txt
  sage Programs/BilinearComplexity/rank48_plus_gateway.sage replay /path/to/input.txt scan.json --output-sha256 HASH

Sage may require ``sage -- script ...`` when dashed options are present.
"""

import argparse
import collections
import hashlib
import itertools
import json
import math
import operator
import os
import re
import struct
import sys
import time


bxor = operator.xor
N = 4
N2 = 16
SOURCE_RANK = 47
TARGET_RANK = 48
ZERO = 0
ONE = 1
SCHEMA = "rank48-plus-gateway-v1"
CERTIFICATE_SCHEMA = SCHEMA + "-output-certificate"
REDUCTION_SCHEMA = SCHEMA + "-shared-factor-reduction"
CLI_DESCRIPTION = (
    "Exact bounded census and replay of binary rank-48 "
    "Arai--Ichikawa--Hukushima Plus gateway certificates."
)
ORIENTATIONS = collections.OrderedDict([
    ("ijk", (0, 1, 2)),
    ("ikj", (0, 2, 1)),
    ("jik", (1, 0, 2)),
    ("jki", (1, 2, 0)),
    ("kij", (2, 0, 1)),
    ("kji", (2, 1, 0)),
])
ORIENTATION_NAMES = tuple(ORIENTATIONS)
VARIANTS = (0, 1, 2)
FORMULAS = collections.OrderedDict([
    ("0", "(a1,b1+b2,c1);(a1+a2,b2,c2);(a1,b2,c1+c2)"),
    ("1", "(a1,b1,c1+c2);(a2,b1+b2,c2);(a1+a2,b1,c2)"),
    ("2", "(a1+a2,b1,c1);(a2,b2,c1+c2);(a2,b1+b2,c1)"),
])


class GatewayError(Exception):
    pass


class Scheme(object):
    def __init__(self, path, raw, terms):
        self.path = os.path.realpath(path)
        self.raw = raw
        self.terms = tuple(tuple(int(value) for value in term) for term in terms)
        self.raw_sha256 = sha256_bytes(raw)
        self.canonical_payload = canonical_payload_bytes(self.terms)
        self.canonical_payload_sha256 = sha256_bytes(self.canonical_payload)


def sha256_bytes(data):
    return hashlib.sha256(data).hexdigest()


def canonical_json_bytes(value):
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        default=json_default,
    ).encode("ascii")


def json_equal(left, right):
    return canonical_json_bytes(left) == canonical_json_bytes(right)


def payload_digest(value):
    return sha256_bytes(canonical_json_bytes(value))


def validate_scan_authentication(document):
    semantic = {
        key: value for key, value in document.items() if key not in ("authentication", "runtime")
    }
    expected = {
        "algorithm": "SHA-256",
        "canonicalization": "ASCII JSON with sort_keys=True and compact separators",
        "scope": "all top-level fields except authentication and runtime",
        "semantic_payload_sha256": payload_digest(semantic),
    }
    if not json_equal(document.get("authentication"), expected):
        raise GatewayError("scan authentication envelope or semantic payload digest mismatch")
    return semantic, expected


def with_certificate_digest(value):
    result = dict(value)
    result["certificate_sha256"] = payload_digest(value)
    return result


def canonical_payload_bytes(terms):
    output = bytearray(struct.pack("<4H", N, N, N, len(terms)))
    for factor in range(3):
        for term in terms:
            output.extend(struct.pack("<H", int(term[factor])))
    return bytes(output)


def canonical_scheme_bytes(terms):
    ordered = sorted(tuple(tuple(int(value) for value in term) for term in terms))
    output = bytearray(struct.pack("<4H", N, N, N, len(ordered)))
    for term in ordered:
        output.extend(struct.pack("<HHH", *term))
    return bytes(output)


def term_hex(term):
    return ["%04x" % int(value) for value in term]


def parse_hex_term(value):
    if not isinstance(value, list) or len(value) != 3:
        raise GatewayError("replacement term must be a three-element hexadecimal list")
    output = []
    for token in value:
        if not isinstance(token, str) or re.fullmatch(r"[0-9a-fA-F]{1,4}", token) is None:
            raise GatewayError("malformed hexadecimal factor in replacement term")
        output.append(int(token, 16))
    return tuple(output)


def parse_scheme(path):
    real = os.path.realpath(path)
    if not os.path.isfile(real):
        raise GatewayError("input is not a file: %s" % path)
    with open(real, "rb") as source:
        raw = source.read()
    try:
        lines = raw.splitlines()
        if len(lines) != 4:
            raise GatewayError("expected exactly four input lines, found %d" % len(lines))
        header = lines[0].decode("ascii").split()
        if header != ["4", "4", "4", "47"]:
            raise GatewayError("header must be exactly '4 4 4 47'")
        factors = []
        for line_index, line in enumerate(lines[1:]):
            tokens = line.decode("ascii").split()
            if len(tokens) != SOURCE_RANK * N2:
                raise GatewayError(
                    "factor line %d has %d tokens, expected %d"
                    % (line_index + 1, len(tokens), SOURCE_RANK * N2)
                )
            if any(token not in ("0", "1") for token in tokens):
                raise GatewayError("factor line %d contains a non-binary token" % (line_index + 1))
            packed = []
            for term_index in range(SOURCE_RANK):
                value = ZERO
                for coordinate in range(N2):
                    if tokens[term_index * N2 + coordinate] == "1":
                        value |= ONE << coordinate
                packed.append(value)
            factors.append(packed)
    except UnicodeDecodeError as error:
        raise GatewayError("input is not ASCII: %s" % error)
    terms = [tuple(factors[mode][index] for mode in range(3)) for index in range(SOURCE_RANK)]
    return Scheme(real, raw, terms)


def bit_indices(value):
    value = int(value)
    while value:
        low = value & -value
        yield low.bit_length() - 1
        value -= low


_OUTER_CACHE = {}


def outer_tensor(term):
    term = tuple(int(value) for value in term)
    cached = _OUTER_CACHE.get(term)
    if cached is not None:
        return cached
    a, b, c = term
    output = ZERO
    for ai in bit_indices(a):
        for bi in bit_indices(b):
            base = (ai * N2 + bi) * N2
            for ci in bit_indices(c):
                output |= ONE << (base + ci)
    _OUTER_CACHE[term] = output
    return output


def tensor_of_terms(terms):
    output = ZERO
    for term in terms:
        output = bxor(output, outer_tensor(term))
    return output


def expected_multiplication_tensor():
    output = ZERO
    for i in range(N):
        for j in range(N):
            for k in range(N):
                u = i * N + j
                v = j * N + k
                w = k * N + i
                output |= ONE << ((u * N2 + v) * N2 + w)
    return output


EXPECTED_TENSOR = expected_multiplication_tensor()
EXPECTED_TENSOR_SHA256 = sha256_bytes(EXPECTED_TENSOR.to_bytes(512, "little"))


def tensor_sha256(value):
    return sha256_bytes(int(value).to_bytes(512, "little"))


def validate_source(scheme):
    reconstructed = tensor_of_terms(scheme.terms)
    mismatch = bxor(reconstructed, EXPECTED_TENSOR)
    zero_factors = [
        [index, mode]
        for index, term in enumerate(scheme.terms)
        for mode in range(3)
        if term[mode] == ZERO
    ]
    duplicate_terms = len(scheme.terms) - len(set(scheme.terms))
    if mismatch:
        raise GatewayError(
            "input does not reconstruct native 4x4 multiplication: %d mismatched tensor coordinates"
            % int(mismatch).bit_count()
        )
    if zero_factors:
        raise GatewayError("input has zero factors: %s" % zero_factors)
    factor_distinct = [len(set(term[mode] for term in scheme.terms)) for mode in range(3)]
    factor_ones = [sum(term[mode].bit_count() for term in scheme.terms) for mode in range(3)]
    return {
        "path": scheme.path,
        "bytes": len(scheme.raw),
        "dimensions": [N, N, N],
        "rank": SOURCE_RANK,
        "raw_sha256": scheme.raw_sha256,
        "canonical_payload_sha256": scheme.canonical_payload_sha256,
        "canonical_unordered_scheme_sha256": sha256_bytes(canonical_scheme_bytes(scheme.terms)),
        "tensor_sha256": tensor_sha256(reconstructed),
        "expected_tensor_sha256": EXPECTED_TENSOR_SHA256,
        "tensor_valid": True,
        "zero_factors": zero_factors,
        "duplicate_complete_terms": duplicate_terms,
        "distinct_factor_counts": factor_distinct,
        "factor_ones": factor_ones,
    }


def plus_local(first, second, orientation, variant):
    positions = tuple(int(value) for value in orientation)
    i, j, k = positions
    a1, b1, c1 = first[i], first[j], first[k]
    a2, b2, c2 = second[i], second[j], second[k]
    if variant == 0:
        oriented = (
            (a1, bxor(b1, b2), c1),
            (bxor(a1, a2), b2, c2),
            (a1, b2, bxor(c1, c2)),
        )
    elif variant == 1:
        oriented = (
            (a1, b1, bxor(c1, c2)),
            (a2, bxor(b1, b2), c2),
            (bxor(a1, a2), b1, c2),
        )
    elif variant == 2:
        oriented = (
            (bxor(a1, a2), b1, c1),
            (a2, b2, bxor(c1, c2)),
            (a2, bxor(b1, b2), c1),
        )
    else:
        raise GatewayError("Plus variant must be 0, 1, or 2")
    output = []
    for values in oriented:
        term = [ZERO, ZERO, ZERO]
        term[i], term[j], term[k] = values
        output.append(tuple(term))
    return tuple(output)


def descriptor_object(p, q, orientation_name, variant):
    return {
        "source_terms": [int(p), int(q)],
        "orientation": orientation_name,
        "positions": list(ORIENTATIONS[orientation_name]),
        "variant": int(variant),
        "index_base": 0,
    }


def descriptor_compact(p, q, orientation_index, variant):
    return [int(p), int(q), int(orientation_index), int(variant)]


def is_json_int(value):
    return type(value) is int


def decode_compact_descriptor(value, orientation_names):
    if not isinstance(value, list) or len(value) != 4 or any(not is_json_int(x) for x in value):
        raise GatewayError("compact descriptor must be [p,q,orientation_index,variant]")
    p, q, orientation_index, variant = value
    if orientation_index < 0 or orientation_index >= len(orientation_names):
        raise GatewayError("compact descriptor orientation index is outside emitted orientation table")
    return descriptor_object(p, q, orientation_names[orientation_index], variant)


def apply_descriptor(terms, descriptor):
    if not isinstance(descriptor, dict):
        raise GatewayError("descriptor is not an object")
    source_terms = descriptor.get("source_terms")
    if not isinstance(source_terms, list) or len(source_terms) != 2:
        raise GatewayError("descriptor source_terms must contain two indices")
    p, q = source_terms
    if not is_json_int(p) or not is_json_int(q) or p == q or not (0 <= p < len(terms)) or not (0 <= q < len(terms)):
        raise GatewayError("descriptor source term indices are invalid")
    orientation_name = descriptor.get("orientation")
    if orientation_name not in ORIENTATIONS:
        raise GatewayError("descriptor orientation is unknown")
    variant = descriptor.get("variant")
    if not is_json_int(variant) or variant not in VARIANTS:
        raise GatewayError("descriptor variant is invalid")
    expected_descriptor = descriptor_object(p, q, orientation_name, variant)
    if not json_equal(descriptor, expected_descriptor):
        raise GatewayError("descriptor fields do not match its source terms, orientation, and variant")
    local = plus_local(terms[p], terms[q], ORIENTATIONS[orientation_name], variant)
    output = list(terms)
    output[p] = local[0]
    output[q] = local[1]
    output.append(local[2])
    return tuple(output), local


def parity_normalization(terms):
    counts = collections.Counter(tuple(term) for term in terms)
    effective = []
    zero_factor_indices = []
    for index, term in enumerate(terms):
        if any(value == ZERO for value in term):
            zero_factor_indices.append(int(index))
    cancellation_groups = []
    for term, multiplicity in sorted(counts.items()):
        if any(value == ZERO for value in term):
            continue
        retained = int(multiplicity & 1)
        cancelled = int(multiplicity - retained)
        if retained:
            effective.append(term)
        if cancelled:
            cancellation_groups.append({
                "term_hex": term_hex(term),
                "multiplicity": int(multiplicity),
                "cancelled_copies": cancelled,
                "retained_copies": retained,
            })
    effective = tuple(sorted(effective))
    effective_canonical = canonical_scheme_bytes(effective)
    ledger = {
        "semantics": "discard zero-factor summands and cancel equal complete triples by parity over GF(2)",
        "formal_term_count": len(terms),
        "zero_factor_term_indices_removed": zero_factor_indices,
        "complete_term_parity_groups": cancellation_groups,
        "effective_term_count": len(effective),
        "effective_canonical_bytes": len(effective_canonical),
        "effective_unordered_scheme_sha256": sha256_bytes(effective_canonical),
        "normalization_defect": len(terms) - len(effective),
    }
    return effective, ledger


def duplicate_groups(terms):
    groups = collections.defaultdict(list)
    for index, term in enumerate(terms):
        groups[tuple(term)].append(index)
    return [indices for _, indices in sorted(groups.items()) if len(indices) > 1]


def classify_candidate(source_terms, p, q, candidate, local):
    source_collision_modes = [mode for mode in range(3) if source_terms[p][mode] == source_terms[q][mode]]
    zero_factor_terms = [
        {"term": int(index), "modes": [mode for mode in range(3) if term[mode] == ZERO]}
        for index, term in enumerate(candidate)
        if any(value == ZERO for value in term)
    ]
    duplicates = duplicate_groups(candidate)
    changed = {int(p), int(q), TARGET_RANK - 1}
    collisions_with_untouched = [
        group
        for group in duplicates
        if any(index in changed for index in group) and any(index not in changed for index in group)
    ]
    local_duplicates = duplicate_groups(local)
    legal = not source_collision_modes
    nonzero = not zero_factor_terms
    distinct = not duplicates
    reasons = []
    if source_collision_modes:
        reasons.append("source_factor_collision")
    if zero_factor_terms:
        reasons.append("zero_output_factor")
    if local_duplicates:
        reasons.append("local_output_collision")
    if collisions_with_untouched:
        reasons.append("collision_with_untouched_term")
    if duplicates and not local_duplicates and not collisions_with_untouched:
        reasons.append("preexisting_or_other_complete_term_collision")
    effective, normalization = parity_normalization(candidate)
    direct_defect = TARGET_RANK - len(effective)
    if tensor_of_terms(effective) != EXPECTED_TENSOR:
        raise AssertionError("characteristic-two normalized Plus output failed full tensor replay")
    gateway = legal and nonzero and distinct and direct_defect == 0
    if direct_defect >= 2:
        reasons.append("characteristic_two_defect_two")
    return {
        "tensor_identity_replayed": True,
        "full_tensor_replayed_after_characteristic_two_normalization": True,
        "legal_plus_precondition": bool(legal),
        "source_factor_collision_modes": source_collision_modes,
        "all_48_terms_nonzero": bool(nonzero),
        "zero_factor_terms": zero_factor_terms,
        "all_48_complete_terms_distinct": bool(distinct),
        "duplicate_term_index_groups": duplicates,
        "local_duplicate_index_groups": local_duplicates,
        "collisions_with_untouched_index_groups": collisions_with_untouched,
        "direct_plus_formal_rank": TARGET_RANK,
        "effective_term_count": len(effective),
        "certified_rank_upper_bound": len(effective),
        "direct_plus_defect": int(direct_defect),
        "direct_characteristic_two_defect_two": bool(direct_defect >= 2),
        "characteristic_two_normalization": normalization,
        "rank48_gateway": bool(gateway),
        "formal_length48_gateway": bool(gateway),
        "non_gateway_descriptor": not gateway,
        "boundary_collision": bool(not nonzero or not distinct),
        "boundary_reasons": reasons,
    }


def classification_output_invariants(classification):
    normalization = classification["characteristic_two_normalization"]
    return {
        "all_48_terms_nonzero": classification["all_48_terms_nonzero"],
        "all_48_complete_terms_distinct": classification["all_48_complete_terms_distinct"],
        "effective_term_count": classification["effective_term_count"],
        "direct_plus_defect": classification["direct_plus_defect"],
        "direct_characteristic_two_defect_two": classification["direct_characteristic_two_defect_two"],
        "effective_unordered_scheme_sha256": normalization["effective_unordered_scheme_sha256"],
    }


def update_classification_aggregate(aggregate, classification):
    aggregate["descriptor_count"] += 1
    key = "rank48_gateway_descriptor_count" if classification["rank48_gateway"] else "non_gateway_descriptor_count"
    aggregate[key] += 1
    for reason in classification["boundary_reasons"]:
        aggregate["boundary_reason_counts"][reason] = aggregate["boundary_reason_counts"].get(reason, 0) + 1


def new_classification_aggregate(classification):
    aggregate = {
        "descriptor_count": 0,
        "rank48_gateway_descriptor_count": 0,
        "non_gateway_descriptor_count": 0,
        "any_formal_length48_gateway": False,
        "all_descriptors_formal_length48_gateways": False,
        "boundary_reason_counts": {},
        "output_invariants": classification_output_invariants(classification),
    }
    update_classification_aggregate(aggregate, classification)
    return aggregate


def finalize_classification_aggregate(aggregate):
    aggregate["any_formal_length48_gateway"] = aggregate["rank48_gateway_descriptor_count"] > 0
    aggregate["all_descriptors_formal_length48_gateways"] = (
        aggregate["rank48_gateway_descriptor_count"] == aggregate["descriptor_count"]
    )
    aggregate["boundary_reason_counts"] = dict(sorted(aggregate["boundary_reason_counts"].items()))


def matrix_rows_for_subset(terms, shared_mode, indices):
    complementary = tuple(mode for mode in range(3) if mode != shared_mode)
    left_mode, right_mode = complementary
    rows = [ZERO] * N2
    for index in indices:
        left = terms[index][left_mode]
        right = terms[index][right_mode]
        for row in bit_indices(left):
            rows[row] = bxor(rows[row], right)
    return tuple(rows), complementary


def gf2_row_rank(rows):
    pivots = {}
    for original in rows:
        value = int(original)
        while value:
            pivot = value.bit_length() - 1
            if pivot in pivots:
                value = bxor(value, pivots[pivot])
            else:
                pivots[pivot] = value
                break
    return len(pivots)


def rank_factorization(rows):
    selected = []
    independent = {}
    for row in rows:
        value = int(row)
        reduced = value
        while reduced:
            pivot = reduced.bit_length() - 1
            if pivot in independent:
                reduced = bxor(reduced, independent[pivot])
            else:
                independent[pivot] = reduced
                selected.append(value)
                break
    pivots = {}
    for index, row in enumerate(selected):
        value = int(row)
        coefficients = ONE << index
        while value:
            pivot = value.bit_length() - 1
            if pivot in pivots:
                pivot_value, pivot_coefficients = pivots[pivot]
                value = bxor(value, pivot_value)
                coefficients = bxor(coefficients, pivot_coefficients)
            else:
                pivots[pivot] = (value, coefficients)
                break
        if value == ZERO:
            raise AssertionError("selected matrix rows were not independent")
    row_coefficients = []
    for row in rows:
        value = int(row)
        coefficients = ZERO
        while value:
            pivot = value.bit_length() - 1
            if pivot not in pivots:
                raise AssertionError("matrix row is outside selected row span")
            pivot_value, pivot_coefficients = pivots[pivot]
            value = bxor(value, pivot_value)
            coefficients = bxor(coefficients, pivot_coefficients)
        row_coefficients.append(coefficients)
    left_factors = []
    for basis_index in range(len(selected)):
        factor = ZERO
        for row_index, coefficients in enumerate(row_coefficients):
            if (coefficients >> basis_index) & ONE:
                factor |= ONE << row_index
        if factor == ZERO or selected[basis_index] == ZERO:
            raise AssertionError("rank factorization produced a zero factor")
        left_factors.append(factor)
    check = [ZERO] * N2
    for left, right in zip(left_factors, selected):
        for row in bit_indices(left):
            check[row] = bxor(check[row], right)
    if tuple(check) != tuple(rows):
        raise AssertionError("rank factorization replay failed")
    return tuple(left_factors), tuple(selected)


def rows_bytes(rows):
    return b"".join(struct.pack("<H", int(row)) for row in rows)


def reduce_shared_subset(terms, shared_mode, indices):
    indices = tuple(sorted(int(index) for index in indices))
    if len(indices) < 2 or len(set(indices)) != len(indices) or any(index < 0 or index >= len(terms) for index in indices):
        raise GatewayError("reduction subset indices are invalid")
    shared = terms[indices[0]][shared_mode]
    if shared == ZERO or any(terms[index][shared_mode] != shared for index in indices):
        raise GatewayError("reduction subset does not share one nonzero factor")
    rows, complementary = matrix_rows_for_subset(terms, shared_mode, indices)
    rank = gf2_row_rank(rows)
    left_factors, right_factors = rank_factorization(rows)
    if rank != len(left_factors):
        raise AssertionError("matrix rank and factorization length disagree")
    replacements = []
    for left, right in zip(left_factors, right_factors):
        term = [ZERO, ZERO, ZERO]
        term[shared_mode] = shared
        term[complementary[0]] = left
        term[complementary[1]] = right
        replacements.append(tuple(term))
    before_tensor = tensor_of_terms(terms[index] for index in indices)
    after_tensor = tensor_of_terms(replacements)
    if before_tensor != after_tensor:
        raise AssertionError("shared-factor reduction failed local tensor replay")
    removed = set(indices)
    reduced = tuple(term for index, term in enumerate(terms) if index not in removed) + tuple(replacements)
    defect = len(indices) - rank
    matrix_record = {
        "row_order": "first complementary factor coordinate 0..15",
        "rows_hex": ["%04x" % row for row in rows],
        "sha256": sha256_bytes(rows_bytes(rows)),
        "rank_gf2": int(rank),
    }
    record = {
        "schema": REDUCTION_SCHEMA,
        "shared_mode": int(shared_mode),
        "shared_factor_hex": "%04x" % shared,
        "subset_indices": list(indices),
        "index_base": 0,
        "complementary_modes": list(complementary),
        "matrix": matrix_record,
        "subset_size": len(indices),
        "defect": int(defect),
        "characteristic_two_defect_two": bool(defect >= 2),
        "replacement_terms_hex": [term_hex(term) for term in replacements],
        "result_term_count": len(reduced),
        "certified_rank_upper_bound": len(reduced),
        "result_unordered_scheme_sha256": sha256_bytes(canonical_scheme_bytes(reduced)),
        "local_tensor_before_sha256": tensor_sha256(before_tensor),
        "local_tensor_after_sha256": tensor_sha256(after_tensor),
    }
    return reduced, with_certificate_digest(record)


def equal_factor_groups(terms):
    result = []
    for mode in range(3):
        groups = collections.defaultdict(list)
        for index, term in enumerate(terms):
            if term[mode] != ZERO:
                groups[term[mode]].append(index)
        for shared, indices in sorted(groups.items()):
            if len(indices) >= 2:
                result.append((mode, shared, tuple(indices)))
    return result


def screen_reductions(terms, max_subset_size, max_subsets):
    examined = 0
    skipped_by_size = 0
    skipped_by_budget = 0
    witnesses = []
    groups = equal_factor_groups(terms)
    total_descriptors = 0
    for mode, shared, group in groups:
        top = min(len(group), max_subset_size)
        total_descriptors += sum(math.comb(len(group), size) for size in range(2, top + 1))
        if top < len(group):
            skipped_by_size += sum(math.comb(len(group), size) for size in range(top + 1, len(group) + 1))
    skipped_by_budget = max(0, total_descriptors - max_subsets)
    budget_exhausted = False
    for mode, shared, group in groups:
        top = min(len(group), max_subset_size)
        for size in range(2, top + 1):
            for subset in itertools.combinations(group, size):
                if examined >= max_subsets:
                    budget_exhausted = True
                    break
                examined += 1
                rows, ignored = matrix_rows_for_subset(terms, mode, subset)
                defect = len(subset) - gf2_row_rank(rows)
                if defect > 0:
                    reduced, witness = reduce_shared_subset(terms, mode, subset)
                    if tensor_of_terms(reduced) != EXPECTED_TENSOR:
                        raise AssertionError("positive reduction output failed full tensor replay")
                    witnesses.append(witness)
            if budget_exhausted:
                break
        if budget_exhausted:
            break
    return {
        "definition": (
            "equal nonzero factor in shared_mode; defect = subset_size - GF(2)-rank of the "
            "16x16 sum of complementary outer products"
        ),
        "max_subset_size": int(max_subset_size),
        "max_subsets_per_output": int(max_subsets),
        "equal_factor_groups": len(groups),
        "subsets_examined": int(examined),
        "subsets_skipped_by_size": int(skipped_by_size),
        "subsets_skipped_by_budget": int(skipped_by_budget),
        "complete_for_all_equal_factor_subsets": skipped_by_size == 0 and skipped_by_budget == 0,
        "positive_reduction_witnesses": witnesses,
        "positive_reduction_count": len(witnesses),
        "defect_two_witness_count": sum(witness["defect"] >= 2 for witness in witnesses),
    }


def parse_name_subset(value, allowed, label):
    if value == "all":
        return tuple(allowed)
    requested = tuple(token.strip() for token in value.split(",") if token.strip())
    unknown = [token for token in requested if token not in allowed]
    if not requested or unknown or len(set(requested)) != len(requested):
        raise argparse.ArgumentTypeError(
            "%s must be 'all' or a duplicate-free comma-separated subset of %s"
            % (label, ",".join(str(item) for item in allowed))
        )
    return requested


def parse_orientations(value):
    return parse_name_subset(value, ORIENTATION_NAMES, "orientations")


def parse_variants(value):
    names = parse_name_subset(value, ("0", "1", "2"), "variants")
    return tuple(int(name) for name in names)


def pair_domain(rank, pair_start, max_pairs):
    all_pairs = list(itertools.combinations(range(rank), 2))
    if pair_start < 0 or pair_start > len(all_pairs):
        raise GatewayError("pair-start is outside 0..%d" % len(all_pairs))
    if max_pairs < 0:
        raise GatewayError("max-pairs must be nonnegative")
    stop = len(all_pairs) if max_pairs == 0 else min(len(all_pairs), pair_start + max_pairs)
    return all_pairs, all_pairs[pair_start:stop], stop


def script_metadata():
    path = os.path.realpath(__file__)
    try:
        with open(path, "rb") as source:
            raw = source.read()
        return {"path": path, "bytes": len(raw), "sha256": sha256_bytes(raw)}
    except OSError:
        return {"path": path, "bytes": None, "sha256": None}


def scan(args):
    started = time.monotonic()
    scheme = parse_scheme(args.input)
    source_record = validate_source(scheme)
    all_pairs, selected_pairs, pair_stop = pair_domain(SOURCE_RANK, args.pair_start, args.max_pairs)
    orientation_names = tuple(args.orientations)
    variants = tuple(args.variants)
    orientation_index = {name: index for index, name in enumerate(orientation_names)}
    descriptor_hasher = hashlib.sha256()
    classification_counts = collections.Counter()
    output_by_hash = collections.OrderedDict()
    canonical_by_hash = {}
    local_replays = 0
    legal_descriptors = 0
    gateway_descriptors = 0

    for first_index, second_index in selected_pairs:
        for p, q in ((first_index, second_index), (second_index, first_index)):
            for orientation_name in orientation_names:
                for variant in variants:
                    descriptor = descriptor_object(p, q, orientation_name, variant)
                    compact = descriptor_compact(p, q, orientation_index[orientation_name], variant)
                    candidate, local = apply_descriptor(scheme.terms, descriptor)
                    before = bxor(outer_tensor(scheme.terms[p]), outer_tensor(scheme.terms[q]))
                    after = tensor_of_terms(local)
                    if before != after:
                        raise AssertionError("Plus local tensor identity failed for %s" % descriptor)
                    local_replays += 1
                    classification = classify_candidate(scheme.terms, p, q, candidate, local)
                    if classification["legal_plus_precondition"]:
                        legal_descriptors += 1
                    if classification["rank48_gateway"]:
                        gateway_descriptors += 1
                    classification_counts[
                        "formal_length48_gateway" if classification["rank48_gateway"] else "non_gateway_descriptor"
                    ] += 1
                    for reason in classification["boundary_reasons"]:
                        classification_counts["boundary_reason:" + reason] += 1
                    canonical = canonical_scheme_bytes(candidate)
                    output_hash = sha256_bytes(canonical)
                    descriptor_hasher.update(canonical_json_bytes(compact))
                    descriptor_hasher.update(bytes.fromhex(output_hash))
                    if output_hash in canonical_by_hash and canonical_by_hash[output_hash] != canonical:
                        raise AssertionError("SHA-256 collision between unequal canonical output schemes")
                    if output_hash not in output_by_hash:
                        canonical_by_hash[output_hash] = canonical
                        record = {
                            "schema": CERTIFICATE_SCHEMA,
                            "output_unordered_scheme_sha256": output_hash,
                            "output_canonical_bytes": len(canonical),
                            "source": {
                                "raw_sha256": scheme.raw_sha256,
                                "canonical_payload_sha256": scheme.canonical_payload_sha256,
                            },
                            "compact_descriptor_orientation_names": list(orientation_names),
                            "representative_descriptor": descriptor,
                            "descriptor_aliases": [],
                            "descriptor_classification_sha256": [],
                            "descriptor_multiplicity": 0,
                            "local_source_terms_hex": [term_hex(scheme.terms[p]), term_hex(scheme.terms[q])],
                            "local_output_terms_hex": [term_hex(term) for term in local],
                            "local_tensor_before_sha256": tensor_sha256(before),
                            "local_tensor_after_sha256": tensor_sha256(after),
                            "classification": classification,
                            "classification_aggregate": new_classification_aggregate(classification),
                            "screens": None,
                        }
                        output_by_hash[output_hash] = record
                    record = output_by_hash[output_hash]
                    if record["classification_aggregate"]["output_invariants"] != classification_output_invariants(classification):
                        raise AssertionError("exact duplicate output acquired inconsistent output invariants")
                    if record["descriptor_multiplicity"] > 0:
                        update_classification_aggregate(record["classification_aggregate"], classification)
                    record["descriptor_aliases"].append(compact)
                    record["descriptor_classification_sha256"].append(payload_digest(classification))
                    record["descriptor_multiplicity"] += 1

    total_screen_subsets = 0
    total_screen_skipped_size = 0
    total_screen_skipped_budget = 0
    positive_reduction_witnesses = 0
    defect_two_witnesses = 0
    outputs_with_reduction = 0
    outputs_with_defect_two = 0
    direct_defect_two_outputs = 0
    gateway_outputs = 0
    outputs_without_gateway = 0
    actual_boundary_outputs = 0
    for record in output_by_hash.values():
        aggregate = record["classification_aggregate"]
        finalize_classification_aggregate(aggregate)
        if aggregate["output_invariants"]["direct_characteristic_two_defect_two"]:
            direct_defect_two_outputs += 1
        if (
            not aggregate["output_invariants"]["all_48_terms_nonzero"]
            or not aggregate["output_invariants"]["all_48_complete_terms_distinct"]
        ):
            actual_boundary_outputs += 1
        if aggregate["any_formal_length48_gateway"]:
            gateway_outputs += 1
            candidate, local = apply_descriptor(scheme.terms, record["representative_descriptor"])
            screen = screen_reductions(candidate, args.screen_max_subset_size, args.screen_max_subsets)
            record["screens"] = screen
            total_screen_subsets += screen["subsets_examined"]
            total_screen_skipped_size += screen["subsets_skipped_by_size"]
            total_screen_skipped_budget += screen["subsets_skipped_by_budget"]
            positive_reduction_witnesses += screen["positive_reduction_count"]
            defect_two_witnesses += screen["defect_two_witness_count"]
            if screen["positive_reduction_count"]:
                outputs_with_reduction += 1
            if screen["defect_two_witness_count"]:
                outputs_with_defect_two += 1
        else:
            outputs_without_gateway += 1
            record["screens"] = {
                "not_run": True,
                "reason": "output has no enumerated legal nonzero distinct formal length-48 gateway descriptor",
            }
        certificate_body = dict(record)
        record["certificate_sha256"] = payload_digest(certificate_body)

    selected_descriptor_count = len(selected_pairs) * 2 * len(orientation_names) * len(variants)
    if selected_descriptor_count != local_replays:
        raise AssertionError("descriptor coverage arithmetic disagrees with replay count")
    pair_orientation_complete = (
        args.pair_start == 0
        and pair_stop == len(all_pairs)
        and set(orientation_names) == set(ORIENTATION_NAMES)
    )
    full_paper_domain = pair_orientation_complete and 0 in variants
    exactly_paper_domain = pair_orientation_complete and variants == (0,)
    full_production_alias_domain = pair_orientation_complete and set(variants) == set(VARIANTS)
    all_screens_complete = total_screen_skipped_size == 0 and total_screen_skipped_budget == 0
    coverage = {
        "bounded_domain_statement": (
            "All counts and negative summaries concern only the explicit input and descriptor/subset "
            "bounds recorded in this object; they make no claim about other schemes, equivalence-orbit "
            "representatives, later flip walks, or an external archive."
        ),
        "archive_scan_performed": False,
        "input_file_count": 1,
        "source_rank": SOURCE_RANK,
        "unordered_term_pairs_total": len(all_pairs),
        "pair_index_order": "lexicographic combinations of zero-based source indices",
        "pair_start": int(args.pair_start),
        "pair_stop_exclusive": int(pair_stop),
        "unordered_term_pairs_enumerated": len(selected_pairs),
        "ordered_source_orders_per_pair": 2,
        "orientation_names": list(orientation_names),
        "orientation_positions": [list(ORIENTATIONS[name]) for name in orientation_names],
        "variant_values": list(variants),
        "descriptors_expected": int(selected_descriptor_count),
        "descriptors_replayed": int(local_replays),
        "legal_plus_descriptors": int(legal_descriptors),
        "rank48_gateway_descriptors": int(gateway_descriptors),
        "descriptor_result_stream_sha256": descriptor_hasher.hexdigest(),
        "full_arai_paper_descriptor_domain": bool(full_paper_domain),
        "exactly_arai_paper_descriptor_domain": bool(exactly_paper_domain),
        "full_production_alias_descriptor_domain": bool(full_production_alias_domain),
        "screen_max_subset_size": int(args.screen_max_subset_size),
        "screen_max_subsets_per_output": int(args.screen_max_subsets),
        "screen_subsets_examined_across_unique_gateways": int(total_screen_subsets),
        "screen_subsets_skipped_by_size": int(total_screen_skipped_size),
        "screen_subsets_skipped_by_budget": int(total_screen_skipped_budget),
        "all_gateway_equal_factor_subsets_screened": bool(all_screens_complete),
    }
    summary = {
        "descriptor_classification_counts": dict(sorted(classification_counts.items())),
        "exact_unique_outputs": len(output_by_hash),
        "exact_duplicate_descriptors_collapsed": selected_descriptor_count - len(output_by_hash),
        "unique_rank48_gateways": int(gateway_outputs),
        "unique_formal_length48_gateways": int(gateway_outputs),
        "unique_outputs_without_gateway_descriptor": int(outputs_without_gateway),
        "unique_boundary_collision_outputs": int(actual_boundary_outputs),
        "unique_direct_characteristic_two_defect_two_outputs": int(direct_defect_two_outputs),
        "gateway_outputs_with_positive_reduction_screen": int(outputs_with_reduction),
        "positive_reduction_witnesses": int(positive_reduction_witnesses),
        "gateway_outputs_with_characteristic_two_defect_two": int(outputs_with_defect_two),
        "characteristic_two_defect_two_witnesses": int(defect_two_witnesses),
        "negative_reduction_summary_scope": (
            "A gateway without an emitted reduction witness is negative only for its examined equal-factor "
            "subsets under the size and per-output budgets in coverage."
        ),
    }
    document = {
        "schema": SCHEMA,
        "command": "scan",
        "status": "complete" if full_paper_domain and all_screens_complete else "bounded_complete",
        "source": source_record,
        "implementation": script_metadata(),
        "field": {"name": "GF(2)", "characteristic": 2, "nonzero_scalars": [1]},
        "hash_encodings": {
            "source_canonical_payload": (
                "little-endian <4H header (4,4,4,47), followed by factor-major values "
                "for modes 0,1,2 and source terms 0..46; each factor is uint16 little-endian"
            ),
            "unordered_scheme": (
                "little-endian <4H header (4,4,4,term_count), followed by lexicographically "
                "sorted term-major triples; each factor is uint16 little-endian"
            ),
            "tensor": (
                "fixed 512-byte little-endian bitset; tensor coordinate (u,v,w) is bit "
                "((u*16+v)*16+w), and each factor coordinate is row-major row*4+column"
            ),
            "json_authentication": "ASCII JSON with sort_keys=True and compact separators",
        },
        "plus": {
            "source": "Arai--Ichikawa--Hukushima Plus identity",
            "arxiv": "2312.16960",
            "paper_displayed_variant": 0,
            "gateway_definition": (
                "formal_length48_gateway means a legal Plus descriptor whose emitted length-48 "
                "decomposition has nonzero factors and pairwise-distinct complete terms; it is not "
                "a claim that the multiplication tensor has minimum tensor rank 48"
            ),
            "formulas": dict(FORMULAS),
            "orientation_semantics": "positions (i,j,k) permute the three tensor factors",
            "descriptor_alias_semantics": (
                "all compact aliases were enumerated and replay to the same exact term-order canonical output; "
                "compact encoding is [p,q,orientation_index,variant] using each output certificate's "
                "compact_descriptor_orientation_names table (equal to coverage.orientation_names)"
            ),
        },
        "coverage": coverage,
        "summary": summary,
        "outputs": list(output_by_hash.values()),
    }
    semantic_payload = dict(document)
    document["authentication"] = {
        "algorithm": "SHA-256",
        "canonicalization": "ASCII JSON with sort_keys=True and compact separators",
        "scope": "all top-level fields except authentication and runtime",
        "semantic_payload_sha256": payload_digest(semantic_payload),
    }
    document["runtime"] = {
        "elapsed_seconds": float(time.monotonic() - started),
        "outer_tensor_cache_entries": len(_OUTER_CACHE),
    }
    return document


def extract_output_record(document, output_hash):
    if not isinstance(document, dict):
        raise GatewayError("certificate JSON must be an object")
    if document.get("schema") == CERTIFICATE_SCHEMA:
        if output_hash and document.get("output_unordered_scheme_sha256") != output_hash:
            raise GatewayError("standalone output certificate hash does not match --output-sha256")
        return document, None
    if document.get("schema") != SCHEMA or document.get("command") != "scan":
        raise GatewayError("certificate is neither an output certificate nor a scan document")
    outputs = document.get("outputs")
    if not isinstance(outputs, list) or not outputs:
        raise GatewayError("scan document contains no output certificates")
    if output_hash is None:
        if len(outputs) != 1:
            raise GatewayError("--output-sha256 is required when a scan document has multiple outputs")
        return outputs[0], document
    matches = [record for record in outputs if record.get("output_unordered_scheme_sha256") == output_hash]
    if len(matches) != 1:
        raise GatewayError("requested output hash occurs %d times in scan document" % len(matches))
    return matches[0], document


def verify_reduction_witness(candidate, witness):
    if not isinstance(witness, dict) or witness.get("schema") != REDUCTION_SCHEMA:
        raise GatewayError("malformed reduction witness")
    recorded_digest = witness.get("certificate_sha256")
    body = dict(witness)
    body.pop("certificate_sha256", None)
    if recorded_digest != payload_digest(body):
        raise GatewayError("reduction witness certificate digest mismatch")
    mode = witness.get("shared_mode")
    indices = witness.get("subset_indices")
    if not is_json_int(mode) or mode not in range(3) or not isinstance(indices, list) or any(not is_json_int(index) for index in indices):
        raise GatewayError("reduction witness mode or subset indices are malformed")
    if witness.get("index_base") != 0 or type(witness.get("index_base")) is not int:
        raise GatewayError("reduction witness index_base must be integer zero")
    reduced, replayed = reduce_shared_subset(candidate, mode, indices)
    if not json_equal(replayed, witness):
        raise GatewayError("recomputed reduction witness differs from emitted witness")
    if tensor_of_terms(reduced) != EXPECTED_TENSOR:
        raise GatewayError("replayed reduced scheme does not reconstruct multiplication")
    return witness["result_unordered_scheme_sha256"]


def replay_scan_document(args, document, scheme, source_record, started):
    if not isinstance(document, dict) or document.get("schema") != SCHEMA or document.get("command") != "scan":
        raise GatewayError("--recompute-scan requires a complete scan document")
    parent_source = document.get("source", {})
    if parent_source.get("raw_sha256") != scheme.raw_sha256 or parent_source.get("canonical_payload_sha256") != scheme.canonical_payload_sha256:
        raise GatewayError("input bytes do not match scan document source hashes")
    recorded_semantic, authentication = validate_scan_authentication(document)
    coverage = document.get("coverage", {})
    pair_start = coverage.get("pair_start")
    pair_stop = coverage.get("pair_stop_exclusive")
    orientations = coverage.get("orientation_names")
    variants = coverage.get("variant_values")
    max_subset_size = coverage.get("screen_max_subset_size")
    max_subsets = coverage.get("screen_max_subsets_per_output")
    if (
        not is_json_int(pair_start)
        or not is_json_int(pair_stop)
        or pair_stop < pair_start
        or not isinstance(orientations, list)
        or not orientations
        or any(type(name) is not str or name not in ORIENTATIONS for name in orientations)
        or len(set(orientations)) != len(orientations)
        or not isinstance(variants, list)
        or not variants
        or any(not is_json_int(value) or value not in VARIANTS for value in variants)
        or len(set(variants)) != len(variants)
        or not is_json_int(max_subset_size)
        or max_subset_size < 2
        or not is_json_int(max_subsets)
        or max_subsets < 1
    ):
        raise GatewayError("scan coverage bounds are malformed")
    recompute_args = argparse.Namespace(
        input=args.input,
        pair_start=pair_start,
        max_pairs=pair_stop - pair_start,
        orientations=tuple(orientations),
        variants=tuple(variants),
        screen_max_subset_size=max_subset_size,
        screen_max_subsets=max_subsets,
    )
    recomputed = scan(recompute_args)
    recomputed_semantic = {
        key: value for key, value in recomputed.items() if key not in ("authentication", "runtime")
    }
    if canonical_json_bytes(recomputed_semantic) != canonical_json_bytes(recorded_semantic):
        raise GatewayError("independently recomputed scan semantics differ from certificate")
    return {
        "schema": SCHEMA + "-scan-replay-v1",
        "command": "replay",
        "status": "valid",
        "valid": True,
        "source": source_record,
        "semantic_payload_sha256": authentication["semantic_payload_sha256"],
        "descriptor_result_stream_sha256": coverage.get("descriptor_result_stream_sha256"),
        "unordered_term_pairs_recomputed": coverage.get("unordered_term_pairs_enumerated"),
        "descriptors_recomputed": coverage.get("descriptors_replayed"),
        "exact_unique_outputs_recomputed": document.get("summary", {}).get("exact_unique_outputs"),
        "output_certificates_recomputed": len(document.get("outputs", [])),
        "descriptor_classifications_recomputed": coverage.get("descriptors_replayed"),
        "bounded_reduction_screens_recomputed": document.get("summary", {}).get("unique_formal_length48_gateways"),
        "screen_subsets_reexamined": coverage.get("screen_subsets_examined_across_unique_gateways"),
        "positive_reduction_witnesses_recomputed": document.get("summary", {}).get("positive_reduction_witnesses"),
        "direct_characteristic_two_defect_two_outputs_recomputed": document.get("summary", {}).get("unique_direct_characteristic_two_defect_two_outputs"),
        "negative_screen_aggregate_recomputed": True,
        "elapsed_seconds": float(time.monotonic() - started),
    }


def replay(args):
    started = time.monotonic()
    scheme = parse_scheme(args.input)
    source_record = validate_source(scheme)
    if args.certificate == "-":
        raw = sys.stdin.read()
    else:
        with open(args.certificate, "r", encoding="utf-8") as source:
            raw = source.read()
    try:
        document = json.loads(
            raw,
            object_pairs_hook=reject_duplicate_json_keys,
            parse_constant=reject_nonfinite_json_constant,
        )
    except json.JSONDecodeError as error:
        raise GatewayError("certificate is not valid JSON: %s" % error)
    if args.recompute_scan:
        if args.output_sha256:
            raise GatewayError("--recompute-scan and --output-sha256 are mutually exclusive")
        return replay_scan_document(args, document, scheme, source_record, started)
    record, parent = extract_output_record(document, args.output_sha256)
    if parent is not None:
        parent_source = parent.get("source", {})
        if parent_source.get("raw_sha256") != scheme.raw_sha256 or parent_source.get("canonical_payload_sha256") != scheme.canonical_payload_sha256:
            raise GatewayError("input bytes do not match scan document source hashes")
        authentication = validate_scan_authentication(parent)[1]
        orientation_names = parent.get("coverage", {}).get("orientation_names")
    else:
        orientation_names = record.get("compact_descriptor_orientation_names")
    expected_record_keys = {
        "schema", "output_unordered_scheme_sha256", "output_canonical_bytes", "source",
        "compact_descriptor_orientation_names", "representative_descriptor", "descriptor_aliases",
        "descriptor_classification_sha256", "descriptor_multiplicity", "local_source_terms_hex",
        "local_output_terms_hex", "local_tensor_before_sha256", "local_tensor_after_sha256",
        "classification", "classification_aggregate", "screens", "certificate_sha256",
    }
    if not isinstance(record, dict) or set(record) != expected_record_keys or record.get("schema") != CERTIFICATE_SCHEMA:
        raise GatewayError("output certificate fields or schema are malformed")
    expected_record_source = {
        "raw_sha256": scheme.raw_sha256,
        "canonical_payload_sha256": scheme.canonical_payload_sha256,
    }
    if not json_equal(record.get("source"), expected_record_source):
        raise GatewayError("input bytes do not match output certificate source hashes")
    if (
        not isinstance(orientation_names, list)
        or not orientation_names
        or any(type(name) is not str or name not in ORIENTATIONS for name in orientation_names)
        or len(set(orientation_names)) != len(orientation_names)
        or not json_equal(record.get("compact_descriptor_orientation_names"), orientation_names)
    ):
        raise GatewayError("certificate orientation table is malformed")
    recorded_certificate_digest = record.get("certificate_sha256")
    certificate_body = dict(record)
    certificate_body.pop("certificate_sha256", None)
    if recorded_certificate_digest != payload_digest(certificate_body):
        raise GatewayError("output certificate digest mismatch")
    representative = record.get("representative_descriptor")
    candidate, local = apply_descriptor(scheme.terms, representative)
    p, q = representative["source_terms"]
    before = bxor(outer_tensor(scheme.terms[p]), outer_tensor(scheme.terms[q]))
    after = tensor_of_terms(local)
    if before != after:
        raise GatewayError("representative descriptor failed local tensor replay")
    canonical = canonical_scheme_bytes(candidate)
    output_hash = sha256_bytes(canonical)
    if output_hash != record.get("output_unordered_scheme_sha256"):
        raise GatewayError("representative descriptor output hash mismatch")
    deterministic_local_fields = {
        "output_canonical_bytes": len(canonical),
        "local_source_terms_hex": [term_hex(scheme.terms[p]), term_hex(scheme.terms[q])],
        "local_output_terms_hex": [term_hex(term) for term in local],
        "local_tensor_before_sha256": tensor_sha256(before),
        "local_tensor_after_sha256": tensor_sha256(after),
    }
    for key, value in deterministic_local_fields.items():
        if not json_equal(record.get(key), value):
            raise GatewayError("output certificate field %s failed deterministic replay" % key)
    representative_classification = classify_candidate(scheme.terms, p, q, candidate, local)
    if not json_equal(representative_classification, record.get("classification")):
        raise GatewayError("representative descriptor classification mismatch")
    aliases = record.get("descriptor_aliases")
    classification_digests = record.get("descriptor_classification_sha256")
    multiplicity = record.get("descriptor_multiplicity")
    if (
        not is_json_int(multiplicity)
        or multiplicity < 1
        or not isinstance(aliases, list)
        or not isinstance(classification_digests, list)
        or len(aliases) != multiplicity
        or len(classification_digests) != multiplicity
    ):
        raise GatewayError("descriptor aliases, classification digests, or multiplicity are malformed")
    alias_keys = [canonical_json_bytes(compact) for compact in aliases]
    if len(set(alias_keys)) != len(alias_keys):
        raise GatewayError("descriptor alias list contains duplicates")
    representative_compact = descriptor_compact(
        p,
        q,
        orientation_names.index(representative["orientation"]),
        representative["variant"],
    )
    if sum(compact == representative_compact for compact in aliases) != 1:
        raise GatewayError("representative descriptor must occur exactly once in descriptor aliases")
    replayed_aggregate = None
    for alias_index, compact in enumerate(aliases):
        alias_descriptor = decode_compact_descriptor(compact, orientation_names)
        alias_candidate, alias_local = apply_descriptor(scheme.terms, alias_descriptor)
        alias_p, alias_q = alias_descriptor["source_terms"]
        alias_before = bxor(outer_tensor(scheme.terms[alias_p]), outer_tensor(scheme.terms[alias_q]))
        if alias_before != tensor_of_terms(alias_local):
            raise GatewayError("descriptor alias failed local tensor replay")
        if sha256_bytes(canonical_scheme_bytes(alias_candidate)) != output_hash:
            raise GatewayError("descriptor alias does not replay to certified output")
        alias_classification = classify_candidate(
            scheme.terms, alias_p, alias_q, alias_candidate, alias_local
        )
        if payload_digest(alias_classification) != classification_digests[alias_index]:
            raise GatewayError("descriptor alias classification digest mismatch")
        if replayed_aggregate is None:
            replayed_aggregate = new_classification_aggregate(alias_classification)
        else:
            if not json_equal(replayed_aggregate["output_invariants"], classification_output_invariants(alias_classification)):
                raise GatewayError("descriptor aliases disagree on output-invariant classification")
            update_classification_aggregate(replayed_aggregate, alias_classification)
    finalize_classification_aggregate(replayed_aggregate)
    if not json_equal(replayed_aggregate, record.get("classification_aggregate")):
        raise GatewayError("classification aggregate mismatch")
    screens = record.get("screens")
    reduction_hashes = []
    if replayed_aggregate["any_formal_length48_gateway"]:
        if not isinstance(screens, dict) or screens.get("not_run"):
            raise GatewayError("gateway output lacks a complete reduction screen")
        max_subset_size = screens.get("max_subset_size")
        max_subsets = screens.get("max_subsets_per_output")
        if (
            not is_json_int(max_subset_size)
            or max_subset_size < 2
            or not is_json_int(max_subsets)
            or max_subsets < 1
        ):
            raise GatewayError("reduction screen bounds are malformed")
        replayed_screen = screen_reductions(candidate, max_subset_size, max_subsets)
        if not json_equal(replayed_screen, screens):
            raise GatewayError("recomputed bounded reduction screen differs from certificate")
        for witness in screens["positive_reduction_witnesses"]:
            reduction_hashes.append(verify_reduction_witness(candidate, witness))
    else:
        expected_not_run = {
            "not_run": True,
            "reason": "output has no enumerated legal nonzero distinct formal length-48 gateway descriptor",
        }
        if not json_equal(screens, expected_not_run):
            raise GatewayError("non-gateway output has malformed screen status")
    return {
        "schema": SCHEMA + "-replay-v1",
        "command": "replay",
        "status": "valid",
        "valid": True,
        "source": source_record,
        "output_unordered_scheme_sha256": output_hash,
        "output_certificate_sha256": recorded_certificate_digest,
        "representative_descriptor_replayed": True,
        "descriptor_aliases_replayed": len(aliases),
        "local_tensor_identity_replays": len(aliases) + 1,
        "descriptor_classifications_replayed": len(aliases),
        "classification_aggregate_replayed": True,
        "bounded_reduction_screen_recomputed": True,
        "screen_subsets_reexamined": 0 if screens.get("not_run") else screens["subsets_examined"],
        "positive_reduction_witnesses_replayed": len(reduction_hashes),
        "reduced_output_hashes": reduction_hashes,
        "direct_characteristic_two_defect_two_replayed": replayed_aggregate["output_invariants"]["direct_characteristic_two_defect_two"],
        "elapsed_seconds": float(time.monotonic() - started),
    }


def reject_duplicate_json_keys(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise GatewayError("certificate JSON contains duplicate key: %s" % key)
        result[key] = value
    return result


def reject_nonfinite_json_constant(value):
    raise GatewayError("certificate JSON contains nonfinite number: %s" % value)


class CertificateArgumentParser(argparse.ArgumentParser):
    def error(self, message):
        raise GatewayError("argument error: %s" % message)


def build_parser():
    parser = CertificateArgumentParser(description=CLI_DESCRIPTION, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--pretty", action="store_true", help="indent the one JSON document written to stdout")
    subparsers = parser.add_subparsers(dest="command", required=True)

    scan_parser = subparsers.add_parser("scan", help="enumerate a bounded Plus descriptor domain")
    scan_parser.add_argument("input", help="one explicit native 4x4x4 rank-47 binary scheme")
    scan_parser.add_argument("--pair-start", type=int, default=0, help="first lexicographic unordered pair index")
    scan_parser.add_argument("--max-pairs", type=int, default=0, help="number of unordered pairs; 0 means all remaining pairs")
    scan_parser.add_argument("--orientations", type=parse_orientations, default=ORIENTATION_NAMES, help="all or a comma-separated subset of ijk,ikj,jik,jki,kij,kji")
    scan_parser.add_argument("--variants", type=parse_variants, default=(0,), help="comma-separated subset of 0,1,2; default 0 is the paper identity, 'all' audits production placement aliases")
    scan_parser.add_argument("--screen-max-subset-size", type=int, default=4, help="largest equal-factor subset screened for rank defect")
    scan_parser.add_argument("--screen-max-subsets", type=int, default=20000, help="deterministic per-output subset screen budget")

    replay_parser = subparsers.add_parser("replay", help="replay one emitted output certificate and all of its positive screens")
    replay_parser.add_argument("input", help="the exact input scheme used by scan")
    replay_parser.add_argument("certificate", help="scan JSON or standalone output certificate; '-' reads stdin")
    replay_parser.add_argument("--output-sha256", help="select one output from a scan JSON document")
    replay_parser.add_argument("--recompute-scan", action="store_true", help="independently rerun and compare the entire recorded bounded scan")
    return parser


def json_default(value):
    try:
        return int(value)
    except Exception:
        return str(value)


def emit(document, pretty=False):
    if pretty:
        text = json.dumps(document, sort_keys=True, indent=2, ensure_ascii=True, default=json_default)
    else:
        text = json.dumps(document, sort_keys=True, separators=(",", ":"), ensure_ascii=True, default=json_default)
    sys.stdout.write(text + "\n")


def normalize_sage_argv():
    if len(sys.argv) >= 2 and sys.argv[0] == "--":
        sys.argv[:] = [sys.argv[1]] + sys.argv[2:]


def main(argv=None):
    parser = build_parser()
    args = None
    try:
        args = parser.parse_args(argv)
        if args.command == "scan":
            if args.screen_max_subset_size < 2:
                raise GatewayError("screen-max-subset-size must be at least 2")
            if args.screen_max_subsets < 1:
                raise GatewayError("screen-max-subsets must be positive")
            document = scan(args)
        elif args.command == "replay":
            document = replay(args)
        else:
            raise GatewayError("unknown command")
        emit(document, args.pretty)
        return 0
    except (GatewayError, OSError, ValueError, KeyError, TypeError, AssertionError) as error:
        emit({
            "schema": SCHEMA,
            "command": getattr(args, "command", None),
            "status": "error",
            "complete": False,
            "error": ("internal consistency failure: " if isinstance(error, AssertionError) else "") + str(error),
        }, getattr(args, "pretty", False))
        return 2


if __name__ in ("__main__", "sage.all"):
    normalize_sage_argv()
    exit_code = main()
    if __name__ == "sage.all":
        sys.stdout.flush()
        sys.stderr.flush()
        os._exit(int(exit_code))
    sys.exit(exit_code)
