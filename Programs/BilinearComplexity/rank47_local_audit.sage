#!/usr/bin/env sage
"""Deterministic exact local audit for binary 4x4x4 length-47 schemes.

No input path, catalog alias, environment variable, or lineage is built in.
Pass every ordinary input explicitly:

  sage -- Programs/BilinearComplexity/rank47_local_audit.sage audit FILE...
  sage -- Programs/BilinearComplexity/rank47_local_audit.sage audit --format exp FILE.exp

The native format is a ``4 4 4 47`` header and three factor-major rows of
47 row-major 4x4 binary matrices.  The strict ``exp`` format is the 47-line
Kauers--Moosbauer form ``(a...)*(b...)*(c...)``.  In both formats the third
factor has trace coordinate W[k,i].

The 99,101-file expression archive is never searched by ``audit``.  Its scan
is available only through the explicit ``archive ROOT`` command.  Archive
mode is structural by default; ``--checks brent`` or ``--checks full`` opts
into the more expensive tensor or tensor-plus-Jacobian computations.

The program uses exact bit-packed arithmetic over GF(2), uses no randomness,
and writes no files or caches.  Its only normal output is one JSON document on
stdout.
"""

import argparse
import collections
import fnmatch
import functools
import hashlib
import json
import operator
import os
import re
import struct
import sys


N = 4
FACTOR_DIM = 16
TERM_COUNT = 47
TENSOR_DIM = 4096
DOMAIN_DIM = 3 * TERM_COUNT * FACTOR_DIM
MAX_INPUT_BYTES = 1 << 20
SCHEMA = "BilinearComplexity.rank47_local_audit.v1"
LEG_NAMES = ("U", "V", "W")
bxor = operator.xor
EXP_LINE = re.compile(r"^\(([^()]*)\)\*\(([^()]*)\)\*\(([^()]*)\)$")
EXP_TOKEN = re.compile(r"^([abc])([1-4])([1-4])$")


class AuditError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise AuditError(message)


def sha256_bytes(value):
    return hashlib.sha256(value).hexdigest()


def stable_json(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), default=int).encode("utf-8")


def bit_positions(value):
    value = int(value)
    while value:
        low = value & -value
        yield low.bit_length() - 1
        value = bxor(value, low)


@functools.lru_cache(maxsize=None)
def outer3(first, second, third):
    result = 0
    for i in bit_positions(first):
        for j in bit_positions(second):
            base = (i * FACTOR_DIM + j) * FACTOR_DIM
            for k in bit_positions(third):
                result |= 1 << (base + k)
    return result


def tensor_from_terms(terms):
    result = 0
    for first, second, third in terms:
        result = bxor(result, outer3(first, second, third))
    return result


def expected_tensor():
    result = 0
    for a in range(N):
        for b in range(N):
            for c in range(N):
                u = N * a + b
                v = N * b + c
                w = N * c + a
                result |= 1 << ((u * FACTOR_DIM + v) * FACTOR_DIM + w)
    return result


EXPECTED_TENSOR = expected_tensor()
EXPECTED_TENSOR_BYTES = int(EXPECTED_TENSOR).to_bytes(TENSOR_DIM // 8, "little")
EXPECTED_TENSOR_SHA256 = sha256_bytes(EXPECTED_TENSOR_BYTES)

ORIENTATION_FORMULAS = collections.OrderedDict((
    ("id", "(U,V,W)"),
    ("cyc", "(V,W,U)"),
    ("cyc2", "(W,U,V)"),
    ("rev", "(transpose(W),transpose(V),transpose(U))"),
    ("rev_cyc", "(transpose(U),transpose(W),transpose(V))"),
    ("rev_cyc2", "(transpose(V),transpose(U),transpose(W))"),
))


def matrix_transpose(value):
    result = 0
    for row in range(N):
        for column in range(N):
            if (value >> (N * row + column)) & 1:
                result |= 1 << (N * column + row)
    return result


def orient_terms(terms, orientation):
    if orientation == "id":
        return tuple(terms)
    if orientation == "cyc":
        return tuple((second, third, first) for first, second, third in terms)
    if orientation == "cyc2":
        return tuple((third, first, second) for first, second, third in terms)
    if orientation == "rev":
        return tuple((matrix_transpose(third), matrix_transpose(second), matrix_transpose(first)) for first, second, third in terms)
    if orientation == "rev_cyc":
        return tuple((matrix_transpose(first), matrix_transpose(third), matrix_transpose(second)) for first, second, third in terms)
    if orientation == "rev_cyc2":
        return tuple((matrix_transpose(second), matrix_transpose(first), matrix_transpose(third)) for first, second, third in terms)
    raise AuditError("unknown orientation %r" % orientation)


def canonical_bytes(terms):
    payload = bytearray(struct.pack("<4H", N, N, N, len(terms)))
    for leg in range(3):
        for term in terms:
            payload.extend(struct.pack("<H", int(term[leg])))
    return bytes(payload)


def parse_native(raw, path):
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AuditError("%s: native input is not ASCII: %s" % (path, error))
    lines = text.splitlines()
    require(len(lines) == 4, "%s: native input must have exactly four lines, found %d" % (path, len(lines)))
    header = lines[0].split()
    require(header == ["4", "4", "4", "47"], "%s: native header tokens must be '4 4 4 47'" % path)
    factors = []
    for leg, line in enumerate(lines[1:]):
        tokens = line.split()
        require(
            len(tokens) == TERM_COUNT * FACTOR_DIM,
            "%s: factor line %d has %d coefficients, expected %d"
            % (path, leg + 1, len(tokens), TERM_COUNT * FACTOR_DIM),
        )
        require(all(token in ("0", "1") for token in tokens), "%s: factor line %d is not binary" % (path, leg + 1))
        factors.append([
            sum((tokens[FACTOR_DIM * term + entry] == "1") << entry for entry in range(FACTOR_DIM))
            for term in range(TERM_COUNT)
        ])
    return tuple(tuple(int(factors[leg][term]) for leg in range(3)) for term in range(TERM_COUNT))


def parse_exp_factor(expression, expected_prefix, path, line_number):
    require(expression != "", "%s:%d: empty %s factor" % (path, line_number, expected_prefix))
    packed = 0
    seen = set()
    for token in expression.split("+"):
        match = EXP_TOKEN.fullmatch(token)
        require(match is not None, "%s:%d: malformed expression token %r" % (path, line_number, token))
        prefix, row, column = match.groups()
        require(prefix == expected_prefix, "%s:%d: expected %s token, found %s" % (path, line_number, expected_prefix, prefix))
        coordinate = N * (int(row) - 1) + int(column) - 1
        require(coordinate not in seen, "%s:%d: repeated token %s" % (path, line_number, token))
        seen.add(coordinate)
        packed |= 1 << coordinate
    return packed


def parse_exp(raw, path):
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AuditError("%s: exp input is not ASCII: %s" % (path, error))
    lines = text.splitlines()
    require(len(lines) == TERM_COUNT, "%s: exp input must have exactly 47 lines, found %d" % (path, len(lines)))
    terms = []
    for line_number, line in enumerate(lines, 1):
        match = EXP_LINE.fullmatch(line)
        require(match is not None, "%s:%d: expected strict '(a...)*(b...)*(c...)' syntax" % (path, line_number))
        terms.append(tuple(
            parse_exp_factor(expression, prefix, path, line_number)
            for expression, prefix in zip(match.groups(), "abc")
        ))
    return tuple(terms)


def split_input_spec(specification, default_format):
    for prefix in ("native:", "exp:", "auto:"):
        if specification.startswith(prefix):
            return prefix[:-1], specification[len(prefix):]
    return default_format, specification


def read_bounded_file(path):
    size = os.stat(path).st_size
    require(size <= MAX_INPUT_BYTES, "%s: input exceeds the 1 MiB safety limit" % path)
    with open(path, "rb") as source:
        raw = source.read(MAX_INPUT_BYTES + 1)
    require(len(raw) <= MAX_INPUT_BYTES, "%s: input exceeds the 1 MiB safety limit" % path)
    return raw


def read_input(specification, default_format="auto", supplied_raw=None):
    requested_format, path_text = split_input_spec(specification, default_format)
    require(path_text != "", "empty input path")
    path = os.path.realpath(path_text)
    require(os.path.isfile(path), "input is not a regular file: %s" % path)
    raw = read_bounded_file(path) if supplied_raw is None else supplied_raw
    require(len(raw) <= MAX_INPUT_BYTES, "%s: input exceeds the 1 MiB safety limit" % path)
    if requested_format == "auto":
        first_line = raw.splitlines()[0].split() if raw.splitlines() else []
        detected_format = "native" if first_line == [b"4", b"4", b"4", b"47"] else "exp"
    else:
        detected_format = requested_format
    if detected_format == "native":
        terms = parse_native(raw, path)
    elif detected_format == "exp":
        terms = parse_exp(raw, path)
    else:
        raise AuditError("unsupported format %r" % detected_format)
    canonical = canonical_bytes(terms)
    return {
        "requested_input": specification,
        "path": path,
        "requested_format": requested_format,
        "format": detected_format,
        "raw": raw,
        "raw_sha256": sha256_bytes(raw),
        "raw_bytes": len(raw),
        "canonical": canonical,
        "canonical_payload_sha256": sha256_bytes(canonical),
        "terms": terms,
    }


def xor_elimination(columns, vector_bytes=None):
    basis = {}
    pivot_columns = []
    digest = hashlib.sha256()
    column_digest = hashlib.sha256()
    for column_index, original in enumerate(columns):
        value = int(original)
        if vector_bytes is not None:
            column_digest.update(int(value).to_bytes(vector_bytes, "little"))
        while value:
            pivot = value.bit_length() - 1
            if pivot in basis:
                value = bxor(value, basis[pivot])
            else:
                basis[pivot] = value
                pivot_columns.append(column_index)
                break
    for pivot in sorted(basis, reverse=True):
        digest.update(struct.pack("<H", pivot))
        if vector_bytes is None:
            width = max(1, (basis[pivot].bit_length() + 7) // 8)
            digest.update(struct.pack("<H", width))
            digest.update(int(basis[pivot]).to_bytes(width, "little"))
        else:
            digest.update(int(basis[pivot]).to_bytes(vector_bytes, "little"))
    return {
        "rank": len(basis),
        "pivot_rows": tuple(sorted(basis, reverse=True)),
        "pivot_columns": tuple(pivot_columns),
        "elimination_basis_sha256": digest.hexdigest(),
        "ordered_columns_sha256": column_digest.hexdigest() if vector_bytes is not None else None,
    }


def xor_rank(columns):
    return xor_elimination(columns)["rank"]


def matrix_rank4(packed):
    rows = [(packed >> (N * row)) & 0xF for row in range(N)]
    return xor_rank(rows)


def kron(first, second):
    result = 0
    for coordinate in bit_positions(first):
        result |= int(second) << (FACTOR_DIM * coordinate)
    return result


def factor_report(terms):
    reports = []
    for leg, name in enumerate(LEG_NAMES):
        values = [term[leg] for term in terms]
        grouped = collections.defaultdict(list)
        for term_index, value in enumerate(values):
            grouped[value].append(term_index)
        repeated = [
            {"factor_hex": "%04x" % value, "terms": indices, "multiplicity": len(indices)}
            for value, indices in sorted(grouped.items()) if len(indices) > 1
        ]
        rank_counts = collections.Counter(matrix_rank4(value) for value in values)
        reports.append({
            "leg": name,
            "nonzero_count": sum(value != 0 for value in values),
            "distinct_count": len(grouped),
            "all_nonzero": all(value != 0 for value in values),
            "all_distinct": len(grouped) == len(values),
            "repeated_equal_factor_groups": repeated,
            "linear_span_rank": xor_rank(values),
            "matrix_rank_counts": {str(rank): rank_counts[rank] for rank in sorted(rank_counts)},
            "ordered_factors_sha256_16le": sha256_bytes(b"".join(struct.pack("<H", value) for value in values)),
        })
    return reports


def evaluated_term_report(terms):
    values = [outer3(*term) for term in terms]
    grouped = collections.defaultdict(list)
    for term_index, value in enumerate(values):
        grouped[value].append(term_index)
    duplicates = [
        {"evaluated_tensor_sha256_512le": sha256_bytes(int(value).to_bytes(512, "little")), "terms": indices, "multiplicity": len(indices)}
        for value, indices in sorted(grouped.items()) if len(indices) > 1
    ]
    ordered = b"".join(int(value).to_bytes(512, "little") for value in values)
    unordered = b"".join(int(value).to_bytes(512, "little") for value in sorted(values))
    return {
        "meaning": "the 47 evaluated rank-one tensors U_l tensor V_l tensor W_l in (GF(2)^16)^{tensor 3}",
        "nonzero_count": sum(value != 0 for value in values),
        "distinct_count": len(grouped),
        "all_nonzero": all(value != 0 for value in values),
        "all_distinct": len(grouped) == len(values),
        "duplicate_groups": duplicates,
        "ordered_sha256_47x512le": sha256_bytes(ordered),
        "unordered_sha256_47x512le": sha256_bytes(unordered),
    }


def complementary_pair_report(terms):
    pair_legs = ((1, 2), (2, 0), (0, 1))
    reports = []
    for first_leg, second_leg in pair_legs:
        values = [kron(term[first_leg], term[second_leg]) for term in terms]
        elimination = xor_elimination(values, 32)
        reports.append({
            "omitted_leg": LEG_NAMES[3 - first_leg - second_leg],
            "evaluated_pair_legs": [LEG_NAMES[first_leg], LEG_NAMES[second_leg]],
            "rows": 256,
            "columns": len(values),
            "rank": elimination["rank"],
            "nullity": len(values) - elimination["rank"],
            "full_column_rank": elimination["rank"] == len(values),
            "ordered_columns_sha256_256le": elimination["ordered_columns_sha256"],
            "elimination_basis_sha256": elimination["elimination_basis_sha256"],
        })
    return reports


def pair_move_report(terms):
    compressions = []
    ordinary = []
    zero_factor_terms = [
        {"term": term_index, "zero_legs": [LEG_NAMES[leg] for leg, factor in enumerate(term) if factor == 0]}
        for term_index, term in enumerate(terms)
        if any(factor == 0 for factor in term)
    ]
    eligible_term = [all(factor != 0 for factor in term) for term in terms]
    skipped_zero_source_pairs = 0
    all_flip_identities = True
    for first in range(len(terms)):
        for second in range(first + 1, len(terms)):
            if not eligible_term[first] or not eligible_term[second]:
                skipped_zero_source_pairs += 1
                continue
            shared = [leg for leg in range(3) if terms[first][leg] == terms[second][leg]]
            if len(shared) >= 2:
                unshared = next((leg for leg in range(3) if leg not in shared), None)
                replacement = 0 if unshared is None else bxor(terms[first][unshared], terms[second][unshared])
                if unshared is None:
                    compressed_value = 0
                else:
                    compressed = list(terms[first])
                    compressed[unshared] = replacement
                    compressed_value = outer3(*compressed) if replacement else 0
                verified = bxor(outer3(*terms[first]), outer3(*terms[second])) == compressed_value
                output_all_nonzero = replacement == 0 or all(factor != 0 for factor in compressed)
                compressions.append({
                    "terms": [first, second],
                    "source_factors_all_nonzero": True,
                    "shared_legs": [LEG_NAMES[leg] for leg in shared],
                    "merged_leg": None if unshared is None else LEG_NAMES[unshared],
                    "merged_factor_hex": None if unshared is None else "%04x" % replacement,
                    "output_summand_count": 0 if replacement == 0 else 1,
                    "output_summands_all_factors_nonzero": bool(output_all_nonzero),
                    "rank_decrease": 2 if replacement == 0 else 1,
                    "exact_pair_tensor_identity_verified": bool(verified),
                })
            elif len(shared) == 1:
                shared_leg = shared[0]
                variants_verified = True
                distinct_replacements = set()
                remaining_base = [leg for leg in range(3) if leg != shared_leg]
                for swap_positions in range(2):
                    remaining = list(remaining_base)
                    if swap_positions:
                        remaining.reverse()
                    for swap_terms in range(2):
                        p, q = (second, first) if swap_terms else (first, second)
                        changed_p = list(terms[p])
                        changed_q = list(terms[q])
                        j, k = remaining
                        changed_p[j] = bxor(changed_p[j], terms[q][j])
                        changed_q[k] = bxor(changed_q[k], terms[p][k])
                        output_all_nonzero = all(factor != 0 for factor in changed_p + changed_q)
                        same = bxor(outer3(*changed_p), outer3(*changed_q)) == bxor(outer3(*terms[first]), outer3(*terms[second]))
                        variants_verified = variants_verified and output_all_nonzero and same
                        distinct_replacements.add(tuple(sorted((tuple(changed_p), tuple(changed_q)))))
                all_flip_identities = all_flip_identities and variants_verified
                ordinary.append({
                    "terms": [first, second],
                    "source_factors_all_nonzero": True,
                    "shared_leg": LEG_NAMES[shared_leg],
                    "oriented_operation_descriptors": 4,
                    "distinct_unordered_replacements": len(distinct_replacements),
                    "distinct_replacement_sha256": sha256_bytes(stable_json(sorted(distinct_replacements))),
                    "all_descriptor_outputs_have_nonzero_factors": bool(variants_verified),
                    "all_descriptors_nonzero_and_tensor_preserving": bool(variants_verified),
                })
    pairwise_compression_free = len(compressions) == 0
    return {
        "source_nonzero_precondition": {
            "criterion": "both source rank-one summands must have all three factors nonzero",
            "eligible_term_count": sum(eligible_term),
            "zero_factor_term_count": len(zero_factor_terms),
            "zero_factor_terms": zero_factor_terms,
            "diagnosed_pair_count": len(terms) * (len(terms) - 1) // 2 - skipped_zero_source_pairs,
            "skipped_pair_count_due_to_zero_source_factor": skipped_zero_source_pairs,
        },
        "two_term_pair_compression": {
            "criterion": "for two nonzero source rank-one summands, two or three exactly equal factors over GF(2); XOR-merge the remaining factor",
            "candidate_count": len(compressions),
            "candidates": compressions,
            "all_candidate_outputs_have_nonzero_factors": all(item["output_summands_all_factors_nonzero"] for item in compressions),
            "all_candidate_identities_verified": all(item["exact_pair_tensor_identity_verified"] for item in compressions),
        },
        "ordinary_fixed_rank_flips": {
            "criterion": "for two nonzero source rank-one summands, a pair sharing exactly one factor gives four oriented native operation descriptors and two distinct unordered replacements over GF(2)",
            "raw_base_count": len(ordinary),
            "raw_bases": ordinary,
            "no_direct_two_term_compression": pairwise_compression_free,
            "native_reduction_first_policy_allows_flips": pairwise_compression_free,
            "native_policy_eligible_base_count": len(ordinary) if pairwise_compression_free else 0,
            "native_policy_eligible_oriented_descriptor_count": 4 * len(ordinary) if pairwise_compression_free else 0,
            "native_policy_eligible_distinct_unordered_replacement_count": 2 * len(ordinary) if pairwise_compression_free else 0,
            "all_oriented_descriptor_outputs_have_nonzero_factors": bool(all_flip_identities),
            "all_oriented_descriptor_identities_verified": bool(all_flip_identities),
            "scope_limitation": "Pairs containing a zero-factor summand are reported as skipped, not as compression or flip diagnostics. No direct two-term compression is not a claim of global rank irreducibility and does not exclude larger-support recombinations.",
        },
    }


def brent_coordinate(index):
    w = index % FACTOR_DIM
    index //= FACTOR_DIM
    v = index % FACTOR_DIM
    u = index // FACTOR_DIM
    a, b = divmod(u, N)
    b_prime, c = divmod(v, N)
    c_prime, a_prime = divmod(w, N)
    return [a, b, b_prime, c, c_prime, a_prime]


def brent_report(terms):
    represented = tensor_from_terms(terms)
    difference = bxor(represented, EXPECTED_TENSOR)
    mismatches = []
    for index in bit_positions(difference):
        rhs = (EXPECTED_TENSOR >> index) & 1
        mismatches.append({
            "coordinate_a_b_bprime_c_cprime_aprime": brent_coordinate(index),
            "lhs": int(bxor(rhs, 1)),
            "rhs": int(rhs),
        })
    represented_bytes = int(represented).to_bytes(TENSOR_DIM // 8, "little")
    orientation_checks = collections.OrderedDict()
    for orientation in ORIENTATION_FORMULAS:
        oriented_tensor = tensor_from_terms(orient_terms(terms, orientation))
        oriented_difference = bxor(oriented_tensor, EXPECTED_TENSOR)
        orientation_checks[orientation] = {
            "coordinates_checked": TENSOR_DIM,
            "mismatch_count": int(oriented_difference).bit_count(),
            "all_coordinates_satisfied": oriented_difference == 0,
            "represented_tensor_sha256_512le": sha256_bytes(int(oriented_tensor).to_bytes(TENSOR_DIM // 8, "little")),
            "residual_sha256_512le": sha256_bytes(int(oriented_difference).to_bytes(TENSOR_DIM // 8, "little")),
        }
    return {
        "field": "GF(2)",
        "equation": "sum_l U_l[a,b] V_l[b',c] W_l[c',a'] = delta(b,b') delta(c,c') delta(a,a')",
        "coordinates_checked": TENSOR_DIM,
        "expected_nonzero_coordinates": 64,
        "represented_nonzero_coordinates": int(represented).bit_count(),
        "mismatch_count": int(difference).bit_count(),
        "all_coordinates_satisfied": difference == 0,
        "mismatches": mismatches,
        "represented_tensor_sha256_512le": sha256_bytes(represented_bytes),
        "expected_tensor_sha256_512le": EXPECTED_TENSOR_SHA256,
        "residual_sha256_512le": sha256_bytes(int(difference).to_bytes(TENSOR_DIM // 8, "little")),
        "orientation_formulas": dict(ORIENTATION_FORMULAS),
        "orientation_checks": orientation_checks,
        "all_orientations_satisfied": all(item["all_coordinates_satisfied"] for item in orientation_checks.values()),
        "orientation_derivation": "Trace cyclicity gives id/cyc/cyc2; tr(U V W)=tr(transpose(W) transpose(V) transpose(U)) gives the three reversals.",
    }


def jacobian_columns(terms):
    columns = []
    for leg in range(3):
        for first, second, third in terms:
            for entry in range(FACTOR_DIM):
                unit = 1 << entry
                if leg == 0:
                    columns.append(outer3(unit, second, third))
                elif leg == 1:
                    columns.append(outer3(first, unit, third))
                else:
                    columns.append(outer3(first, second, unit))
    return columns


def matrix_multiply(first, second):
    result = 0
    for row in range(N):
        for column in range(N):
            value = 0
            for middle in range(N):
                value = bxor(value, ((first >> (N * row + middle)) & 1) & ((second >> (N * middle + column)) & 1))
            result |= value << (N * row + column)
    return result


def pack_variation(blocks, term_count):
    result = 0
    for leg in range(3):
        for term_index, value in enumerate(blocks[leg]):
            result |= int(value) << (FACTOR_DIM * (leg * term_count + term_index))
    return result


def variation_image(blocks, terms):
    result = 0
    for term_index, (first, second, third) in enumerate(terms):
        result = bxor(result, outer3(blocks[0][term_index], second, third))
        result = bxor(result, outer3(first, blocks[1][term_index], third))
        result = bxor(result, outer3(first, second, blocks[2][term_index]))
    return result


def connected_generators(terms):
    rank = len(terms)
    gauges = []
    sandwiches = []
    images = []
    for term_index, (first, second, third) in enumerate(terms):
        blocks = [[0] * rank for _ in range(3)]
        blocks[0][term_index], blocks[1][term_index] = first, second
        gauges.append(pack_variation(blocks, rank))
        images.append(variation_image(blocks, terms))
        blocks = [[0] * rank for _ in range(3)]
        blocks[0][term_index], blocks[2][term_index] = first, third
        gauges.append(pack_variation(blocks, rank))
        images.append(variation_image(blocks, terms))
    for kind in range(3):
        for row in range(N):
            for column in range(N):
                elementary = 1 << (N * row + column)
                blocks = [[0] * rank for _ in range(3)]
                if kind == 0:
                    blocks[0] = [matrix_multiply(elementary, term[0]) for term in terms]
                    blocks[2] = [matrix_multiply(term[2], elementary) for term in terms]
                elif kind == 1:
                    blocks[0] = [matrix_multiply(term[0], elementary) for term in terms]
                    blocks[1] = [matrix_multiply(elementary, term[1]) for term in terms]
                else:
                    blocks[1] = [matrix_multiply(term[1], elementary) for term in terms]
                    blocks[2] = [matrix_multiply(elementary, term[2]) for term in terms]
                sandwiches.append(pack_variation(blocks, rank))
                images.append(variation_image(blocks, terms))
    return gauges, sandwiches, images


def jacobian_report(terms):
    columns = jacobian_columns(terms)
    jacobian = xor_elimination(columns, TENSOR_DIM // 8)
    gauges, sandwiches, generator_images = connected_generators(terms)
    domain_bytes = (3 * len(terms) * FACTOR_DIM + 7) // 8
    gauge_elimination = xor_elimination(gauges, domain_bytes)
    sandwich_elimination = xor_elimination(sandwiches, domain_bytes)
    combined_elimination = xor_elimination(gauges + sandwiches, domain_bytes)
    kernel_dimension = len(columns) - jacobian["rank"]
    inclusion = all(image == 0 for image in generator_images)
    equality = inclusion and combined_elimination["rank"] == kernel_dimension
    return {
        "coefficient_field": "GF(2)",
        "arithmetic": "exact bit-packed XOR Gaussian elimination; highest-set-coordinate pivots",
        "jacobian": {
            "rows": TENSOR_DIM,
            "columns": len(columns),
            "rank": jacobian["rank"],
            "kernel_dimension": kernel_dimension,
            "ordered_columns_sha256_512le": jacobian["ordered_columns_sha256"],
            "elimination_basis_sha256": jacobian["elimination_basis_sha256"],
            "pivot_rows_sha256": sha256_bytes(stable_json(jacobian["pivot_rows"])),
            "pivot_columns_sha256": sha256_bytes(stable_json(jacobian["pivot_columns"])),
        },
        "connected_gauge_sandwich_derivative": {
            "term_scaling_parameters": len(gauges),
            "sandwich_parameters": len(sandwiches),
            "combined_parameters": len(gauges) + len(sandwiches),
            "term_scaling_image_rank": gauge_elimination["rank"],
            "sandwich_image_rank": sandwich_elimination["rank"],
            "term_scaling_sandwich_image_intersection_dimension": (
                gauge_elimination["rank"] + sandwich_elimination["rank"] - combined_elimination["rank"]
            ),
            "combined_image_rank": combined_elimination["rank"],
            "expected_full_span_combined_rank_formula": "2*47 + 3*16 - 3 = 139",
            "expected_full_span_combined_rank": 139,
            "combined_parameter_kernel_dimension": len(gauges) + len(sandwiches) - combined_elimination["rank"],
            "all_generator_images_under_jacobian_zero": inclusion,
            "nonzero_generator_image_count": sum(image != 0 for image in generator_images),
            "ordered_generators_sha256": combined_elimination["ordered_columns_sha256"],
            "elimination_basis_sha256": combined_elimination["elimination_basis_sha256"],
        },
        "raw_derivative_kernel_equals_connected_image": equality,
        "local_tangent_equality": None,
        "local_statement": "Tangent-space language is assigned only after the Brent identity confirms that the input is a point of the target fiber.",
        "global_rigidity_established": False,
        "global_rigidity_limitation": (
            "Tangent-space equality at one enumerated point does not prove reducedness, smoothness, formal or higher-order rigidity, "
            "isolation in a quotient, classification of components, or a statement about every length-47 decomposition."
        ),
    }


def structural_report(terms):
    factors = factor_report(terms)
    evaluated = evaluated_term_report(terms)
    complementary = complementary_pair_report(terms)
    moves = pair_move_report(terms)
    valid = (
        len(terms) == TERM_COUNT
        and all(report["all_nonzero"] for report in factors)
        and evaluated["all_nonzero"]
    )
    return {
        "valid_representation": valid,
        "dimensions": [N, N, N],
        "length": len(terms),
        "factor_checks": factors,
        "evaluated_terms": evaluated,
        "complementary_pair_evaluations": {
            "meaning": "Khatri--Rao columns in the two legs complementary to the named omitted leg",
            "families": complementary,
            "all_full_column_rank": all(report["full_column_rank"] for report in complementary),
        },
        "pair_moves": moves,
    }


def claim_scope(valid_tensor, tangent):
    tangent_equality = None if tangent is None else tangent["local_tangent_equality"]
    return {
        "length_47_presentation_established": bool(valid_tensor),
        "upper_bound_if_valid": "tensor rank over GF(2) is at most 47" if valid_tensor else None,
        "minimal_rank_47_theorem_established": False,
        "minimal_rank_limitation": (
            "A valid 47-summand identity is an upper-bound presentation. This audit supplies no lower bound excluding length 46 or less."
        ),
        "local_tangent_equality_established": tangent_equality,
        "global_rigidity_established": False,
        "global_rigidity_limitation": (
            "First-order tangent equality, when computed, is local linear information and is not a global, formal, or higher-order rigidity theorem."
        ),
    }


def audit_parsed(parsed, checks):
    terms = parsed["terms"]
    structural = structural_report(terms)
    brent = brent_report(terms) if checks in ("brent", "full") else None
    tangent = jacobian_report(terms) if checks == "full" else None
    tensor_valid = bool(
        brent is not None
        and brent["all_coordinates_satisfied"]
        and brent["all_orientations_satisfied"]
        and structural["valid_representation"]
    )
    if tangent is not None:
        raw_equality = tangent["raw_derivative_kernel_equals_connected_image"]
        tangent["local_tangent_equality"] = raw_equality if tensor_valid else None
        tangent["local_statement"] = (
            "At this valid GF(2) Brent point, the kernel of the derivative of the ordered length-47 Brent map equals the image of term rescalings and infinitesimal sandwich transformations."
            if tensor_valid and raw_equality else
            "At this valid GF(2) Brent point, the computed connected derivative image does not equal the computed Brent-Jacobian kernel."
            if tensor_valid else
            "The input is not a valid point of the target Brent fiber, so no local tangent-space equality claim is made; only the raw derivative ranks are reported."
        )
    result = {
        "requested_input": parsed["requested_input"],
        "path": parsed["path"],
        "format": parsed["format"],
        "requested_format": parsed["requested_format"],
        "raw_bytes": parsed["raw_bytes"],
        "raw_sha256": parsed["raw_sha256"],
        "canonical_payload_sha256": parsed["canonical_payload_sha256"],
        "canonical_payload_encoding": "uint16le dimensions and length; factor-major 47 uint16le masks for U,V,W",
        "structural": structural,
        "brent": brent,
        "jacobian_and_connected_derivative": tangent,
        "checks_performed": checks,
        "valid_length_47_scheme": tensor_valid if brent is not None else None,
        "claim_scope": claim_scope(tensor_valid, tangent),
    }
    return result


def compact_archive_result(result):
    structural = result["structural"]
    moves = structural["pair_moves"]
    brent = result["brent"]
    tangent = result["jacobian_and_connected_derivative"]
    return {
        "relative_path": result["relative_path"],
        "raw_bytes": result["raw_bytes"],
        "raw_sha256": result["raw_sha256"],
        "canonical_payload_sha256": result["canonical_payload_sha256"],
        "format": result["format"],
        "all_factors_nonzero": all(item["all_nonzero"] for item in structural["factor_checks"]),
        "factor_distinct_counts": [item["distinct_count"] for item in structural["factor_checks"]],
        "evaluated_terms_distinct": structural["evaluated_terms"]["all_distinct"],
        "complementary_pair_ranks": [item["rank"] for item in structural["complementary_pair_evaluations"]["families"]],
        "pair_compression_candidates": moves["two_term_pair_compression"]["candidate_count"],
        "ordinary_flip_bases": moves["ordinary_fixed_rank_flips"]["native_policy_eligible_base_count"],
        "brent_valid": None if brent is None else brent["all_coordinates_satisfied"],
        "jacobian_rank": None if tangent is None else tangent["jacobian"]["rank"],
        "jacobian_kernel_dimension": None if tangent is None else tangent["jacobian"]["kernel_dimension"],
        "connected_derivative_rank": None if tangent is None else tangent["connected_gauge_sandwich_derivative"]["combined_image_rank"],
        "local_tangent_equality": None if tangent is None else tangent["local_tangent_equality"],
    }


def ordered_record_digest(records):
    digest = hashlib.sha256()
    for record in records:
        encoded = stable_json(record)
        digest.update(struct.pack("<I", len(encoded)) + encoded)
    return digest.hexdigest()


def archive_paths(root, pattern):
    paths = []
    walk_failures = []
    matched_entry_errors = []

    def record_walk_error(error):
        filename = getattr(error, "filename", None) or root
        walk_failures.append({
            "scope": "archive_walk_failure",
            "relative_path": os.path.relpath(filename, root).replace(os.sep, "/"),
            "error": str(error),
            "error_type": type(error).__name__,
        })

    for directory, directory_names, filenames in os.walk(root, followlinks=False, onerror=record_walk_error):
        directory_names.sort()
        filenames.sort()
        for filename in filenames:
            path = os.path.join(directory, filename)
            relative = os.path.relpath(path, root).replace(os.sep, "/")
            if not fnmatch.fnmatch(relative, pattern):
                continue
            try:
                if os.path.islink(path):
                    raise AuditError("archive entry is a symbolic link")
                if not os.path.isfile(path):
                    raise AuditError("archive entry is not a regular file")
                resolved = os.path.realpath(path)
                if os.path.commonpath((root, resolved)) != root:
                    raise AuditError("archive entry resolves outside the explicit root")
                paths.append((relative, resolved))
            except (AuditError, OSError, ValueError) as error:
                matched_entry_errors.append({
                    "scope": "pattern_matched_entry_error",
                    "relative_path": relative,
                    "error": str(error),
                    "error_type": type(error).__name__,
                })
    record_key = lambda item: (item["relative_path"], item["error_type"], item["error"])
    paths.sort(key=lambda item: item[0])
    walk_failures.sort(key=record_key)
    matched_entry_errors.sort(key=record_key)
    return paths, walk_failures, matched_entry_errors


def run_archive(args):
    root = os.path.realpath(args.root)
    require(os.path.isdir(root), "archive root is not a directory: %s" % root)
    discovered, walk_failures, matched_entry_errors = archive_paths(root, args.pattern)
    discovery_errors = sorted(
        walk_failures + matched_entry_errors,
        key=lambda item: (item["relative_path"], item["scope"], item["error_type"], item["error"]),
    )
    selected = discovered if args.limit == 0 else discovered[:args.limit]
    inventory_digest = hashlib.sha256()
    result_digest = hashlib.sha256()
    compact_results = []
    anomalies = []
    errors = list(discovery_errors[:args.max_anomalies])
    canonical_counts = collections.Counter()
    counters = collections.Counter()
    for relative, path in selected:
        inventory_recorded = False
        try:
            raw = read_bounded_file(path)
            raw_sha256 = sha256_bytes(raw)
            inventory_digest.update(relative.encode("utf-8") + b"\x00")
            inventory_digest.update(raw_sha256.encode("ascii") + b"\x00")
            inventory_digest.update(str(len(raw)).encode("ascii") + b"\n")
            inventory_recorded = True
            counters["inventory_readable"] += 1
            parsed = read_input("exp:" + path, "exp", supplied_raw=raw)
            full = audit_parsed(parsed, args.checks)
            full["relative_path"] = relative
            compact = compact_archive_result(full)
            canonical_counts[compact["canonical_payload_sha256"]] += 1
            encoded = stable_json(compact)
            result_digest.update(struct.pack("<I", len(encoded)) + encoded)
            counters["parsed"] += 1
            counters["all_factors_nonzero"] += int(compact["all_factors_nonzero"])
            counters["all_factors_distinct"] += int(compact["factor_distinct_counts"] == [47, 47, 47])
            counters["evaluated_terms_distinct"] += int(compact["evaluated_terms_distinct"])
            counters["all_complementary_pair_ranks_full"] += int(compact["complementary_pair_ranks"] == [47, 47, 47])
            counters["has_pair_compression"] += int(compact["pair_compression_candidates"] != 0)
            counters["has_ordinary_flip"] += int(compact["ordinary_flip_bases"] != 0)
            if compact["brent_valid"] is not None:
                counters["brent_valid"] += int(compact["brent_valid"])
            if compact["local_tangent_equality"] is not None:
                counters["local_tangent_equality"] += int(compact["local_tangent_equality"])
            anomalous = (
                not compact["all_factors_nonzero"]
                or compact["factor_distinct_counts"] != [47, 47, 47]
                or not compact["evaluated_terms_distinct"]
                or compact["complementary_pair_ranks"] != [47, 47, 47]
                or compact["pair_compression_candidates"] != 0
                or compact["brent_valid"] is False
                or compact["local_tangent_equality"] is False
            )
            if anomalous:
                counters["anomalous_occurrences"] += 1
                if len(anomalies) < args.max_anomalies:
                    anomalies.append(compact)
            if args.include_results:
                compact_results.append(compact)
        except Exception as error:
            counters["errors"] += 1
            error_record = {"scope": "archive_file", "relative_path": relative, "error": str(error), "error_type": type(error).__name__}
            if not inventory_recorded:
                inventory_digest.update(relative.encode("utf-8") + b"\x00UNREADABLE\x00")
                inventory_digest.update(stable_json(error_record) + b"\n")
            encoded = stable_json(error_record)
            result_digest.update(struct.pack("<I", len(encoded)) + encoded)
            if len(errors) < args.max_anomalies:
                errors.append(error_record)
    result = {
        "schema": SCHEMA,
        "command": "archive",
        "status": "ok" if counters["errors"] == 0 and not discovery_errors else "partial_error",
        "explicit_archive_mode": True,
        "root": root,
        "pattern": args.pattern,
        "checks": args.checks,
        "discovered_file_count": len(discovered),
        "walk_failure_count": len(walk_failures),
        "pattern_matched_entry_error_count": len(matched_entry_errors),
        "discovery_error_count": len(discovery_errors),
        "pattern_matched_entry_count": len(discovered) + len(matched_entry_errors),
        "selected_file_count": len(selected),
        "limit": args.limit,
        "complete_selected_scan": not discovery_errors and counters["parsed"] + counters["errors"] == len(selected),
        "complete_discovered_scan": not discovery_errors and args.limit == 0 and counters["parsed"] + counters["errors"] == len(discovered),
        "parsed_occurrence_count": counters["parsed"],
        "unique_canonical_payload_count": len(canonical_counts),
        "duplicate_occurrence_count": counters["parsed"] - len(canonical_counts),
        "selected_inventory_records_sha256": inventory_digest.hexdigest(),
        "selected_inventory_digest_scope": (
            "Only the first %d globally sorted accepted regular files selected after applying --limit are authenticated; discovery errors are authenticated separately."
            % len(selected)
            if args.limit != 0 else
            "All globally sorted accepted regular files selected from the explicit root are authenticated; discovery errors are authenticated separately."
        ),
        "selected_inventory_record_encoding": "readable: relative UTF-8 path, NUL, raw SHA-256 ASCII, NUL, decimal byte size, LF; unreadable: relative path, NUL, UNREADABLE, NUL, canonical error JSON, LF",
        "discovery_error_authentication": {
            "sort_key": ["relative_path", "scope", "error_type", "error"],
            "record_encoding": "uint32le canonical-JSON byte length followed by canonical JSON",
            "ordered_all_discovery_errors_sha256": ordered_record_digest(discovery_errors),
            "ordered_walk_failures_sha256": ordered_record_digest(walk_failures),
            "ordered_pattern_matched_entry_errors_sha256": ordered_record_digest(matched_entry_errors),
        },
        "ordered_compact_results_sha256": result_digest.hexdigest(),
        "counts": dict(sorted(counters.items())),
        "anomalies_recorded": anomalies,
        "anomalies_recorded_truncated": counters["anomalous_occurrences"] > len(anomalies),
        "errors_recorded": errors,
        "errors_recorded_truncated": len(discovery_errors) + counters["errors"] > len(errors),
        "record_cap": args.max_anomalies,
        "per_scheme_results_included": bool(args.include_results),
        "schemes": compact_results if args.include_results else None,
        "exact_arithmetic": exact_arithmetic_record(),
        "limitations": archive_limitations(args.checks, args.include_results, args.limit),
    }
    return result


def archive_limitations(checks, include_results, limit):
    limits = [
        "The archive command scans only the explicitly supplied root and pattern; it does not infer or search any other corpus.",
        "Occurrence counts and canonical-payload counts are both reported; duplicate files are not silently treated as new schemes.",
    ]
    if limit != 0:
        limits.append("The selected-inventory digest covers only the first %d globally sorted accepted files chosen by --limit, not every discovered file; every discovery error is authenticated by separate ordered digests." % limit)
    else:
        limits.append("The selected-inventory digest covers every accepted file discovered under the explicit root; every discovery error is authenticated by separate ordered digests.")
    if checks == "structural":
        limits.append("Structural archive mode does not evaluate the 4096 Brent coordinates and therefore does not certify that an occurrence represents matrix multiplication.")
    elif checks == "brent":
        limits.append("Brent archive mode does not compute Jacobian or connected-derivative ranks.")
    if not include_results:
        limits.append("Per-scheme compact records are omitted to keep the 99,101-file output bounded; their deterministic ordered digest and capped anomaly records are emitted.")
    return limits


def exact_arithmetic_record():
    return {
        "field": "GF(2)",
        "representation": "Python/Sage arbitrary-precision integers used as exact bit vectors",
        "linear_algebra": "deterministic XOR elimination with highest-set-coordinate pivots",
        "randomness_used": False,
        "floating_point_used_for_mathematics": False,
        "external_programs_or_imported_project_files": False,
    }


def run_audit(args):
    require(len(args.inputs) > 0, "audit requires at least one explicit input path")
    results = []
    failures = []
    for specification in args.inputs:
        try:
            parsed = read_input(specification, args.format)
            results.append(audit_parsed(parsed, args.checks))
        except Exception as error:
            failures.append({
                "requested_input": specification,
                "error": str(error),
                "error_type": type(error).__name__,
            })
    if args.checks == "structural":
        completed = len(failures) == 0
        valid = None
        status = "structural_only" if completed else "invalid_or_incomplete"
    else:
        valid = len(failures) == 0 and all(result["valid_length_47_scheme"] is True for result in results)
        status = "valid" if valid else "invalid_or_incomplete"
    return {
        "schema": SCHEMA,
        "command": "audit",
        "status": status,
        "checks": args.checks,
        "explicit_inputs": list(args.inputs),
        "input_count": len(args.inputs),
        "parsed_count": len(results),
        "failure_count": len(failures),
        "failures": failures,
        "schemes": results,
        "all_inputs_valid_length_47_schemes": valid,
        "exact_arithmetic": exact_arithmetic_record(),
        "scope": {
            "presentation_not_minimality": "A valid result proves an explicit 47-summand identity and hence rank at most 47; it does not prove rank exactly 47.",
            "local_not_global": "A computed equality of the Jacobian kernel and connected derivative image is local first-order equality at an enumerated point, not global rigidity.",
            "corpus_quantifier": "Only the explicit input list was audited; no catalog, lineage, or universal quantifier is inferred.",
        },
    }


def build_parser():
    parser = argparse.ArgumentParser(
        description="Deterministic exact GF(2) audit of explicit 4x4x4 length-47 schemes.",
        epilog=(
            "Prefix an individual path with native:, exp:, or auto: to override --format. "
            "The archive command is the only recursive mode and always requires an explicit root."
        ),
    )
    parser.add_argument("--pretty", action="store_true", help="pretty-print the deterministic JSON document")
    subparsers = parser.add_subparsers(dest="command", required=True)

    audit = subparsers.add_parser("audit", help="fully audit one or more explicit files")
    audit.add_argument("--format", choices=("auto", "native", "exp"), default="auto")
    audit.add_argument("--checks", choices=("structural", "brent", "full"), default="full")
    audit.add_argument("inputs", nargs="+", help="explicit paths; optional per-path native:/exp:/auto: prefix")

    archive = subparsers.add_parser("archive", help="explicit optional recursive expression-archive scan")
    archive.add_argument("root", help="explicit archive directory; there is no default")
    archive.add_argument("--pattern", default="*.exp", help="relative-path fnmatch pattern (default: *.exp)")
    archive.add_argument("--checks", choices=("structural", "brent", "full"), default="structural")
    archive.add_argument("--limit", type=int, default=0, help="scan only the first N sorted matches; 0 means all")
    archive.add_argument("--include-results", action="store_true", help="include every compact per-scheme result (potentially huge)")
    archive.add_argument("--max-anomalies", type=int, default=100, help="cap stored anomaly and error records")
    return parser


def script_record():
    invoked = sys.argv[0] if sys.argv and sys.argv[0].endswith(".sage") else __file__
    path = os.path.realpath(invoked)
    with open(path, "rb") as source:
        raw = source.read()
    return {"path": path, "bytes": len(raw), "sha256": sha256_bytes(raw)}


def normalize_sage_argv():
    if len(sys.argv) >= 2 and sys.argv[0] == "--":
        sys.argv[:] = [sys.argv[1]] + sys.argv[2:]


def emit(document, pretty):
    document["program"] = script_record()
    if pretty:
        text = json.dumps(document, sort_keys=True, indent=2, default=int)
    else:
        text = json.dumps(document, sort_keys=True, separators=(",", ":"), default=int)
    sys.stdout.write(text + "\n")


def main(argv=None):
    parser = build_parser()
    args = parser.parse_args(argv)
    if hasattr(args, "limit"):
        require(args.limit >= 0, "--limit must be nonnegative")
        require(args.max_anomalies >= 0, "--max-anomalies must be nonnegative")
    if args.command == "audit":
        document = run_audit(args)
    elif args.command == "archive":
        document = run_archive(args)
    else:
        raise AuditError("unsupported command")
    emit(document, args.pretty)
    return 0 if document["status"] in ("valid", "ok", "structural_only") else 1


def entrypoint():
    try:
        return main()
    except (AuditError, OSError, ValueError) as error:
        emit({
            "schema": SCHEMA,
            "command": None,
            "status": "error",
            "error": str(error),
            "error_type": type(error).__name__,
            "exact_arithmetic": exact_arithmetic_record(),
        }, False)
        return 2


if __name__ in ("__main__", "sage.all"):
    normalize_sage_argv()
    exit_code = entrypoint()
    if __name__ == "sage.all":
        sys.stdout.flush()
        sys.stderr.flush()
        os._exit(int(exit_code))
    sys.exit(exit_code)
