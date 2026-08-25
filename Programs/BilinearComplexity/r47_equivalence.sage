#!/usr/bin/env sage
"""Exact rank-47 GF(2) equivalence classifier for native 4x4 schemes.

The native payload convention is one header followed by three payload lines.
Each payload line contains 47 consecutive row-major 16-bit chunks.  A term is
(U,V,W), and W has the native trace coordinate (k,i), so its scalar expansion
is

    tr(U V W) = sum_{i,j,k} U[i,j] V[j,k] W[k,i].

This convention gives the six native tensor orientations directly.  Cyclicity
of trace gives (U,V,W), (V,W,U), and (W,U,V).  Transposing and reversing a
product gives tr(UVW)=tr(T(W)T(V)T(U)); composing that reversal with the two
cycles gives

    id           = (U,V,W)
    cyc          = (V,W,U)
    cyc2         = (W,U,V)
    rev          = (T(W),T(V),T(U))
    rev_cyc      = (T(U),T(W),T(V))
    rev_cyc2     = (T(V),T(U),T(W)).

The validate command reconstructs all 4096 tensor coordinates for every one
of these formulas.  The search action for an oriented source term i and a
target term j is

    A U_i = U'_j B,   B V_i = V'_j C,   C W_i = W'_j A.

Every tentative correspondence adds its homogeneous equations to one packed
48-variable GF(2) system.  DFS uses only necessary exact invariants: factor
ranks, similarity classes of cyclic and mixed products, and ranks of pair and
triple sums.  Similarity is classified exactly by primary nullity sequences
for every irreducible polynomial of degree at most four over GF(2).

A branch is pruned for matrix feasibility only after an exact simultaneous
check that A, B, and C can all be invertible.  The check expresses invertibility
as M*x != 0 for all fifteen nonzero four-bit x and solves the resulting affine
XOR clauses by complete disjoint backtracking.  Small nullspaces are instead
enumerated completely.  A reported inequivalence therefore means that all six
orientation trees were exhausted.  A deadline or branch limit produces the
machine-readable status "unknown", never "inequivalent".

Typical invocations from the repository root are:

  timeout 300 sage Programs/BilinearComplexity/r47_equivalence.sage validate
  timeout 300 sage Programs/BilinearComplexity/r47_equivalence.sage compare local-c561 optimized-c475
  timeout 300 sage Programs/BilinearComplexity/r47_equivalence.sage controls
  timeout 300 sage Programs/BilinearComplexity/r47_equivalence.sage campaign
  timeout 300 sage Programs/BilinearComplexity/r47_equivalence.sage verify-witness result.json

This Sage installation parses dashed script options itself.  When using options,
put Sage's ``--`` before the script, for example

  timeout 300 sage -- Programs/BilinearComplexity/r47_equivalence.sage compare local-c561 optimized-c475 --seconds 120

All normal output is one JSON document on stdout.  Progress goes to stderr.
"""

import argparse
import collections
import hashlib
import itertools
import json
import operator
import os
import re
import struct
import sys
import time


bxor = operator.xor
ONE = int(1)
ZERO = int(0)
N = int(4)
N2 = int(16)
RANK = int(47)
VARIABLES = int(48)
BLOCK_MASK = int(0xffff)
IDENTITY = int(0x8421)
SCHEMA = "r47-gf2-equivalence-v1"

SCRIPT_PATH = os.path.realpath(__file__)
REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(SCRIPT_PATH), "..", ".."))
DATA_ROOT = os.environ.get("R47_DATA_ROOT", "/home/exedev/x/matmul-schemes")

ORIENTATION_FORMULAS = collections.OrderedDict([
    ("id", "(U,V,W)"),
    ("cyc", "(V,W,U)"),
    ("cyc2", "(W,U,V)"),
    ("rev", "(T(W),T(V),T(U))"),
    ("rev_cyc", "(T(U),T(W),T(V))"),
    ("rev_cyc2", "(T(V),T(U),T(W))"),
])
ORIENTATIONS = tuple(ORIENTATION_FORMULAS.keys())
ORIENTATION_DERIVATION = (
    "Native W is W[k,i], hence each term is tr(U V W).  Trace cyclicity gives "
    "id/cyc/cyc2; tr(U V W)=tr(T(W) T(V) T(U)) gives rev, and composing rev "
    "with the two native cycles gives rev_cyc and rev_cyc2."
)

CATALOG_RELATIVE = collections.OrderedDict([
    ("local-c561", "matmul-schemes/z2/4x4x4_m47_c561_iteration7562_Z2.txt"),
    ("local-c625", "matmul-schemes/z2/4x4x4_m47_c625_iteration2409_Z2.txt"),
    ("local-c632", "matmul-schemes/z2/4x4x4_m47_c632_iteration3744_Z2.txt"),
    ("local-c661", "matmul-schemes/z2/4x4x4_m47_c661_iteration3517_Z2.txt"),
    ("local-c767", "matmul-schemes/z2/4x4x4_m47_c767_iteration3252_Z2.txt"),
    ("local-c782", "matmul-schemes/z2/4x4x4_m47_c782_iteration3523_Z2.txt"),
    ("local-c822", "matmul-schemes/z2/4x4x4_m47_c822_iteration8688_Z2.txt"),
    ("alphatensor", "z2/public-rank47-references/alphatensor_m47_raw.txt"),
    ("kauers-moosbauer", "z2/public-rank47-references/kauers-moosbauer_m47_raw.txt"),
    ("optimized-c475", "z2/optimized/r47-c561-sandwich-seed256-diagnostic/4x4x4_m47_c475_f0_Z2.txt"),
    ("optimized-c509", "z2/optimized/r47-c625-sandwich-seed256-diagnostic/4x4x4_m47_c509_f0_Z2.txt"),
])
LOCAL_ALIASES = tuple(name for name in CATALOG_RELATIVE if name.startswith("local-"))
PUBLISHED_ALIASES = ("alphatensor", "kauers-moosbauer")
OPTIMIZED_ALIASES = ("optimized-c475", "optimized-c509")
DEFAULT_ALIASES = LOCAL_ALIASES + PUBLISHED_ALIASES + OPTIMIZED_ALIASES
CONTROL_PAIRS = (
    ("local-c561", "optimized-c475"),
    ("local-c625", "optimized-c509"),
)

IRREDUCIBLES = (
    (int(0b10), int(1)),
    (int(0b11), int(1)),
    (int(0b111), int(2)),
    (int(0b1011), int(3)),
    (int(0b1101), int(3)),
    (int(0b10011), int(4)),
    (int(0b11001), int(4)),
    (int(0b11111), int(4)),
)


class DataError(Exception):
    pass


class SearchInterrupted(Exception):
    def __init__(self, reason):
        Exception.__init__(self, reason)
        self.reason = reason


class Scheme(object):
    def __init__(self, path, alias, dimensions, rank, terms, raw_sha256, payload_sha256, byte_count):
        self.path = os.path.realpath(path)
        self.alias = alias
        self.dimensions = tuple(int(x) for x in dimensions)
        self.rank = int(rank)
        self.terms = tuple(tuple(int(y) for y in term) for term in terms)
        self.raw_sha256 = raw_sha256
        self.payload_sha256 = payload_sha256
        self.byte_count = int(byte_count)


class MemoryScheme(Scheme):
    def __init__(self, alias, terms):
        canonical = canonical_payload_bytes((N, N, N), len(terms), terms)
        digest = hashlib.sha256(canonical).hexdigest()
        Scheme.__init__(
            self,
            "memory://" + alias,
            alias,
            (N, N, N),
            len(terms),
            terms,
            digest,
            digest,
            len(canonical),
        )
        self.path = "memory://" + alias


def catalog_paths():
    return collections.OrderedDict(
        (alias, os.path.realpath(os.path.join(DATA_ROOT, relative)))
        for alias, relative in CATALOG_RELATIVE.items()
    )


def resolve_path(value):
    paths = catalog_paths()
    if value in paths:
        path = paths[value]
        if not os.path.isfile(path):
            raise DataError("catalog input is missing: %s -> %s" % (value, path))
        return path, value
    path = os.path.realpath(value)
    if not os.path.isfile(path):
        raise DataError("input does not exist and is not a catalog alias: %s" % value)
    alias = next((name for name, known in paths.items() if known == path), None)
    return path, alias


def canonical_payload_bytes(dimensions, rank, terms):
    out = bytearray(struct.pack("<4H", int(dimensions[0]), int(dimensions[1]), int(dimensions[2]), int(rank)))
    for factor in range(3):
        for term in terms:
            out.extend(struct.pack("<H", int(term[factor])))
    return bytes(out)


def parse_scheme(value, require_rank47=True):
    path, alias = resolve_path(value)
    with open(path, "rb") as source:
        raw = source.read()
    digest = hashlib.sha256(raw).hexdigest()
    try:
        lines = raw.splitlines()
        if len(lines) != 4:
            raise DataError("%s: expected exactly four lines, found %d" % (path, len(lines)))
        header_tokens = lines[0].decode("ascii").split()
        if len(header_tokens) != 4 or any(not re.fullmatch(r"[0-9]+", token) for token in header_tokens):
            raise DataError("%s: malformed header" % path)
        dimensions = tuple(int(token) for token in header_tokens[:3])
        rank = int(header_tokens[3])
        if dimensions != (N, N, N):
            raise DataError("%s: dimensions are %s, expected 4 4 4" % (path, dimensions))
        if require_rank47 and rank != RANK:
            raise DataError("%s: rank is %d, expected 47" % (path, rank))
        factor_chunks = []
        for factor, line in enumerate(lines[1:]):
            tokens = line.decode("ascii").split()
            expected = rank * N2
            if len(tokens) != expected:
                raise DataError(
                    "%s: factor line %d has %d coefficients, expected %d"
                    % (path, factor + 1, len(tokens), expected)
                )
            if any(token not in ("0", "1") for token in tokens):
                raise DataError("%s: factor line %d contains a non-binary token" % (path, factor + 1))
            chunks = []
            for index in range(rank):
                packed = ZERO
                start = index * N2
                for coordinate in range(N2):
                    if tokens[start + coordinate] == "1":
                        packed |= ONE << coordinate
                chunks.append(packed)
            factor_chunks.append(chunks)
        terms = [tuple(factor_chunks[factor][index] for factor in range(3)) for index in range(rank)]
    except UnicodeDecodeError:
        raise DataError("%s: input is not ASCII" % path)
    canonical = canonical_payload_bytes(dimensions, rank, terms)
    return Scheme(
        path,
        alias,
        dimensions,
        rank,
        terms,
        digest,
        hashlib.sha256(canonical).hexdigest(),
        len(raw),
    )


def matrix_rows(packed):
    return [int((packed >> (N * row)) & int(0xf)) for row in range(N)]


def matrix_record(packed):
    return {
        "packed_hex": "%04x" % int(packed),
        "rows": [
            [int((packed >> (N * row + column)) & ONE) for column in range(N)]
            for row in range(N)
        ],
    }


def mat_transpose(packed):
    result = ZERO
    for row in range(N):
        for column in range(N):
            if (packed >> (N * row + column)) & ONE:
                result |= ONE << (N * column + row)
    return result


def mat_mul(left, right):
    right_rows = matrix_rows(right)
    result = ZERO
    for row in range(N):
        selector = int((left >> (N * row)) & int(0xf))
        output = ZERO
        for middle in range(N):
            if (selector >> middle) & ONE:
                output = bxor(output, right_rows[middle])
        result |= output << (N * row)
    return result


def mat_rank(packed):
    basis = [ZERO] * N
    rank = ZERO
    for row_value in matrix_rows(packed):
        value = row_value
        while value:
            pivot = value.bit_length() - 1
            if basis[pivot]:
                value = bxor(value, basis[pivot])
            else:
                basis[pivot] = value
                rank += ONE
                break
    return int(rank)


def mat_inverse(packed):
    rows = [
        int((packed >> (N * row)) & int(0xf)) | (ONE << (N + row))
        for row in range(N)
    ]
    for column in range(N):
        pivot = next((row for row in range(column, N) if (rows[row] >> column) & ONE), None)
        if pivot is None:
            return None
        rows[column], rows[pivot] = rows[pivot], rows[column]
        for row in range(N):
            if row != column and ((rows[row] >> column) & ONE):
                rows[row] = bxor(rows[row], rows[column])
    result = ZERO
    for row in range(N):
        result |= ((rows[row] >> N) & int(0xf)) << (N * row)
    if mat_mul(packed, result) != IDENTITY or mat_mul(result, packed) != IDENTITY:
        raise AssertionError("packed inversion failed its internal product check")
    return result


_INVERTIBLE_CACHE = {}
_SIMILARITY_CACHE = {}


def is_invertible(packed):
    packed = int(packed)
    answer = _INVERTIBLE_CACHE.get(packed)
    if answer is None:
        answer = mat_rank(packed) == N
        _INVERTIBLE_CACHE[packed] = answer
    return answer


def mat_poly_eval(packed, polynomial):
    degree = int(polynomial).bit_length() - 1
    result = ZERO
    for exponent in range(degree, -1, -1):
        result = mat_mul(result, packed)
        if (polynomial >> exponent) & ONE:
            result = bxor(result, IDENTITY)
    return result


def similarity_key(packed):
    packed = int(packed)
    cached = _SIMILARITY_CACHE.get(packed)
    if cached is not None:
        return cached
    key = []
    for polynomial, degree in IRREDUCIBLES:
        primary = mat_poly_eval(packed, polynomial)
        power = primary
        nullities = []
        for exponent in range(1, N // degree + 1):
            nullities.append(int(N - mat_rank(power)))
            power = mat_mul(power, primary)
        key.append(tuple(nullities))
    answer = tuple(key)
    _SIMILARITY_CACHE[packed] = answer
    return answer


def orient_terms(terms, orientation):
    if orientation == "id":
        return tuple((u, v, w) for u, v, w in terms)
    if orientation == "cyc":
        return tuple((v, w, u) for u, v, w in terms)
    if orientation == "cyc2":
        return tuple((w, u, v) for u, v, w in terms)
    if orientation == "rev":
        return tuple((mat_transpose(w), mat_transpose(v), mat_transpose(u)) for u, v, w in terms)
    if orientation == "rev_cyc":
        return tuple((mat_transpose(u), mat_transpose(w), mat_transpose(v)) for u, v, w in terms)
    if orientation == "rev_cyc2":
        return tuple((mat_transpose(v), mat_transpose(u), mat_transpose(w)) for u, v, w in terms)
    raise DataError("unknown orientation: %s" % orientation)


def set_bit_indices(value):
    value = int(value)
    while value:
        low = value & -value
        yield int(low.bit_length() - 1)
        value -= low


def reconstruct_tensor(terms):
    tensor = ZERO
    for u, v, w in terms:
        for a in set_bit_indices(u):
            for b in set_bit_indices(v):
                base = (a * N2 + b) * N2
                for c in set_bit_indices(w):
                    tensor = bxor(tensor, ONE << (base + c))
    return tensor


def expected_tensor():
    tensor = ZERO
    for i in range(N):
        for j in range(N):
            for k in range(N):
                a = i * N + j
                b = j * N + k
                c = k * N + i
                tensor |= ONE << ((a * N2 + b) * N2 + c)
    return tensor


EXPECTED_TENSOR = expected_tensor()
EXPECTED_TENSOR_HASH = hashlib.sha256(EXPECTED_TENSOR.to_bytes(512, "little")).hexdigest()


def tensor_report(terms, include_mismatches=True):
    got = reconstruct_tensor(terms)
    difference = bxor(got, EXPECTED_TENSOR)
    report = {
        "valid": difference == ZERO,
        "ambient_coordinates": int(N ** 6),
        "expected_ones": int(EXPECTED_TENSOR.bit_count()),
        "reconstructed_ones": int(got.bit_count()),
        "mismatch_count": int(difference.bit_count()),
        "tensor_sha256": hashlib.sha256(got.to_bytes(512, "little")).hexdigest(),
        "expected_tensor_sha256": EXPECTED_TENSOR_HASH,
    }
    if include_mismatches and difference:
        report["mismatch_coordinates"] = [
            [int(index // 256), int((index // 16) % 16), int(index % 16)]
            for index in set_bit_indices(difference)
        ]
    return report


def direct_complexity(terms):
    u_additions = sum(max(int(u.bit_count()) - 1, 0) for u, _, _ in terms)
    v_additions = sum(max(int(v.bit_count()) - 1, 0) for _, v, _ in terms)
    output_counts = [ZERO] * N2
    for _, _, w in terms:
        for coordinate in set_bit_indices(w):
            output_counts[coordinate] += ONE
    w_additions = sum(max(int(count) - 1, 0) for count in output_counts)
    return int(u_additions + v_additions + w_additions)


def unordered_term_hash(terms):
    raw = bytearray()
    for u, v, w in sorted(tuple(tuple(int(x) for x in term) for term in terms)):
        raw.extend(struct.pack("<HHH", u, v, w))
    return hashlib.sha256(bytes(raw)).hexdigest()


def scheme_metadata(scheme, include_tensor=False):
    factor_ones = [sum(int(term[factor].bit_count()) for term in scheme.terms) for factor in range(3)]
    factor_rank_counts = []
    for factor in range(3):
        counts = collections.Counter(mat_rank(term[factor]) for term in scheme.terms)
        factor_rank_counts.append({str(rank): int(counts[rank]) for rank in sorted(counts)})
    zero_factors = [
        [int(index), int(factor)]
        for index, term in enumerate(scheme.terms)
        for factor in range(3)
        if term[factor] == ZERO
    ]
    duplicates = int(len(scheme.terms) - len(set(scheme.terms)))
    complexity = direct_complexity(scheme.terms)
    filename_match = re.search(r"_c([0-9]+)(?:_|\.)", os.path.basename(scheme.path))
    claimed = int(filename_match.group(1)) if filename_match else None
    result = {
        "alias": scheme.alias,
        "path": scheme.path,
        "dimensions": [int(x) for x in scheme.dimensions],
        "rank": int(scheme.rank),
        "bytes": int(scheme.byte_count),
        "raw_sha256": scheme.raw_sha256,
        "canonical_payload_sha256": scheme.payload_sha256,
        "unordered_term_sha256": unordered_term_hash(scheme.terms),
        "payload_layout": "three lines; consecutive row-major 16-bit chunks; W coordinate (k,i)",
        "factor_ones": [int(x) for x in factor_ones],
        "total_ones": int(sum(factor_ones)),
        "factor_rank_counts": factor_rank_counts,
        "zero_factors": zero_factors,
        "duplicate_complete_terms": duplicates,
        "direct_complexity": complexity,
        "filename_complexity_claim": claimed,
        "filename_complexity_matches": None if claimed is None else claimed == complexity,
    }
    if include_tensor:
        result["tensor"] = tensor_report(scheme.terms)
    return result


def validate_scheme(scheme):
    native = tensor_report(scheme.terms)
    orientation_reports = collections.OrderedDict()
    for orientation in ORIENTATIONS:
        orientation_reports[orientation] = tensor_report(orient_terms(scheme.terms, orientation))
    metadata = scheme_metadata(scheme)
    valid = (
        scheme.dimensions == (N, N, N)
        and scheme.rank == RANK
        and not metadata["zero_factors"]
        and native["valid"]
        and all(report["valid"] for report in orientation_reports.values())
    )
    return {
        "valid": bool(valid),
        "metadata": metadata,
        "native_tensor": native,
        "orientation_tensor_checks": orientation_reports,
        "orientation_formulas": dict(ORIENTATION_FORMULAS),
        "orientation_derivation": ORIENTATION_DERIVATION,
    }


def cyclic_product(term):
    return mat_mul(mat_mul(term[0], term[1]), term[2])


def unary_key(term):
    u, v, w = term
    return (
        mat_rank(u),
        mat_rank(v),
        mat_rank(w),
        similarity_key(mat_mul(mat_mul(u, v), w)),
        similarity_key(mat_mul(mat_mul(v, w), u)),
        similarity_key(mat_mul(mat_mul(w, u), v)),
    )


PAIR_PATTERNS = (
    (0, 0, 1),
    (0, 1, 0),
    (0, 1, 1),
    (1, 0, 0),
    (1, 0, 1),
    (1, 1, 0),
)
TRIPLE_PATTERNS = tuple(itertools.permutations(range(3)))


class InvariantIndex(object):
    def __init__(self, terms, budget=None):
        self.terms = tuple(terms)
        self.budget = budget
        unary = []
        for index, term in enumerate(self.terms):
            if self.budget is not None and index % 8 == 0:
                self.budget.check()
            unary.append(unary_key(term))
        self.unary = tuple(unary)
        self.pairs = {}
        self.triples = {}
        self.rooted_pairs = {}

    def pair(self, first, second):
        key = (int(first), int(second))
        cached = self.pairs.get(key)
        if cached is not None:
            return cached
        selected = (self.terms[first], self.terms[second])
        products = []
        for a, b, c in PAIR_PATTERNS:
            products.append(
                similarity_key(
                    mat_mul(mat_mul(selected[a][0], selected[b][1]), selected[c][2])
                )
            )
        answer = (
            mat_rank(bxor(selected[0][0], selected[1][0])),
            mat_rank(bxor(selected[0][1], selected[1][1])),
            mat_rank(bxor(selected[0][2], selected[1][2])),
            tuple(products),
        )
        self.pairs[key] = answer
        return answer

    def canonical_pair(self, first, second):
        forward = self.pair(first, second)
        backward = self.pair(second, first)
        return min(forward, backward)

    def triple(self, first, second, third):
        key = (int(first), int(second), int(third))
        cached = self.triples.get(key)
        if cached is not None:
            return cached
        selected = (self.terms[first], self.terms[second], self.terms[third])
        products = []
        for a, b, c in TRIPLE_PATTERNS:
            products.append(
                similarity_key(
                    mat_mul(mat_mul(selected[a][0], selected[b][1]), selected[c][2])
                )
            )
        answer = (
            mat_rank(bxor(bxor(selected[0][0], selected[1][0]), selected[2][0])),
            mat_rank(bxor(bxor(selected[0][1], selected[1][1]), selected[2][1])),
            mat_rank(bxor(bxor(selected[0][2], selected[1][2]), selected[2][2])),
            tuple(products),
        )
        self.triples[key] = answer
        return answer

    def rooted_pair_profile(self, root):
        root = int(root)
        cached = self.rooted_pairs.get(root)
        if cached is not None:
            return cached
        profile = collections.Counter()
        for other in range(len(self.terms)):
            if self.budget is not None and other % 8 == 0:
                self.budget.check()
            if other != root:
                profile[self.pair(root, other)] += ONE
        answer = tuple(sorted((key, int(value)) for key, value in profile.items()))
        self.rooted_pairs[root] = answer
        return answer

    def global_pair_counter(self):
        counter = collections.Counter()
        for first in range(len(self.terms)):
            if self.budget is not None:
                self.budget.check()
            for second in range(first + 1, len(self.terms)):
                counter[self.canonical_pair(first, second)] += ONE
        return counter


def correspondence_equations(source_term, target_term):
    u, v, w = source_term
    up, vp, wp = target_term
    rows = []
    for row in range(N):
        for column in range(N):
            equation = ZERO
            for middle in range(N):
                if (u >> (N * middle + column)) & ONE:
                    equation |= ONE << (N * row + middle)
                if (up >> (N * row + middle)) & ONE:
                    equation |= ONE << (N2 + N * middle + column)
            if equation:
                rows.append(equation)
    for row in range(N):
        for column in range(N):
            equation = ZERO
            for middle in range(N):
                if (v >> (N * middle + column)) & ONE:
                    equation |= ONE << (N2 + N * row + middle)
                if (vp >> (N * row + middle)) & ONE:
                    equation |= ONE << (2 * N2 + N * middle + column)
            if equation:
                rows.append(equation)
    for row in range(N):
        for column in range(N):
            equation = ZERO
            for middle in range(N):
                if (w >> (N * middle + column)) & ONE:
                    equation |= ONE << (2 * N2 + N * row + middle)
                if (wp >> (N * row + middle)) & ONE:
                    equation |= ONE << (N * middle + column)
            if equation:
                rows.append(equation)
    return tuple(rows)


EMPTY_SYSTEM = tuple((ZERO, ZERO) for _ in range(VARIABLES))


def system_rank(system):
    return int(sum(1 for coefficient, rhs in system if coefficient))


def system_add(system, coefficient, rhs=ZERO):
    coefficient = int(coefficient)
    rhs = int(rhs) & ONE
    rows = list(system)
    for pivot in range(VARIABLES - 1, -1, -1):
        row_coefficient, row_rhs = rows[pivot]
        if row_coefficient and ((coefficient >> pivot) & ONE):
            coefficient = bxor(coefficient, row_coefficient)
            rhs = bxor(rhs, row_rhs)
    if coefficient == ZERO:
        return system if rhs == ZERO else None
    pivot = coefficient.bit_length() - 1
    for other in range(VARIABLES):
        row_coefficient, row_rhs = rows[other]
        if row_coefficient and ((row_coefficient >> pivot) & ONE):
            rows[other] = (bxor(row_coefficient, coefficient), bxor(row_rhs, rhs))
    rows[pivot] = (coefficient, rhs)
    return tuple(rows)


def system_add_many(system, equations):
    current = system
    for coefficient in equations:
        current = system_add(current, coefficient, ZERO)
        if current is None:
            return None
    return current


def system_reduce_form(system, coefficient):
    coefficient = int(coefficient)
    rhs = ZERO
    for pivot in range(VARIABLES - 1, -1, -1):
        row_coefficient, row_rhs = system[pivot]
        if row_coefficient and ((coefficient >> pivot) & ONE):
            coefficient = bxor(coefficient, row_coefficient)
            rhs = bxor(rhs, row_rhs)
    return coefficient, rhs


def system_offset_solution(system):
    solution = ZERO
    for pivot, (coefficient, rhs) in enumerate(system):
        if coefficient and rhs:
            solution |= ONE << pivot
    return solution


def nullspace_basis(system):
    pivot_set = {pivot for pivot, (coefficient, _) in enumerate(system) if coefficient}
    vectors = []
    for free in range(VARIABLES):
        if free in pivot_set:
            continue
        vector = ONE << free
        for pivot, (coefficient, rhs) in enumerate(system):
            if rhs:
                raise AssertionError("nullspace_basis requires a homogeneous system")
            if coefficient and ((coefficient >> free) & ONE):
                vector |= ONE << pivot
        vectors.append(vector)
    return tuple(vectors)


def unpack_transform(vector):
    return (
        int(vector & BLOCK_MASK),
        int((vector >> N2) & BLOCK_MASK),
        int((vector >> (2 * N2)) & BLOCK_MASK),
    )


def transform_is_invertible(vector):
    a, b, c = unpack_transform(vector)
    return is_invertible(a) and is_invertible(b) and is_invertible(c)


def build_invertibility_clauses():
    clauses = []
    for block in range(3):
        offset = block * N2
        for domain_vector in range(1, int(16)):
            forms = []
            for row in range(N):
                form = ZERO
                for column in range(N):
                    if (domain_vector >> column) & ONE:
                        form |= ONE << (offset + N * row + column)
                forms.append(form)
            clauses.append(tuple(forms))
    return tuple(clauses)


INVERTIBILITY_CLAUSES = build_invertibility_clauses()


class SearchBudget(object):
    def __init__(self, seconds, max_branches):
        self.started = time.monotonic()
        self.deadline = self.started + float(seconds) if seconds and float(seconds) > 0 else None
        self.max_branches = int(max_branches) if max_branches else ZERO
        self.branches = ZERO

    def check(self):
        if self.deadline is not None and time.monotonic() >= self.deadline:
            raise SearchInterrupted("deadline")

    def count_branch(self):
        self.check()
        if self.max_branches and self.branches >= self.max_branches:
            raise SearchInterrupted("branch_limit")
        self.branches += ONE

    def elapsed(self):
        return float(time.monotonic() - self.started)


class Counters(object):
    FIELDS = (
        "nodes",
        "branches_considered",
        "assignments",
        "equation_rows_added",
        "pair_checks",
        "triple_checks",
        "block_checks",
        "block_dpll_nodes",
        "block_dpll_cache_hits",
        "block_prunes",
        "small_space_calls",
        "small_space_vectors",
        "small_space_invertible_vectors",
        "small_space_exhausted_prunes",
        "full_multiset_checks",
        "full_multiset_prunes",
        "empty_domain_prunes",
        "hall_checks",
        "hall_prunes",
        "forward_checks",
        "solutions",
        "max_depth",
    )

    def __init__(self):
        for field in self.FIELDS:
            setattr(self, field, ZERO)

    def increment(self, field, amount=ONE):
        setattr(self, field, int(getattr(self, field) + amount))

    def report(self):
        return {field: int(getattr(self, field)) for field in self.FIELDS}


def exact_simultaneous_invertible(system, budget, counters):
    counters.increment("block_checks")
    unsatisfiable = set()

    def recurse(current):
        budget.check()
        counters.increment("block_dpll_nodes")
        if current in unsatisfiable:
            counters.increment("block_dpll_cache_hits")
            return None
        best = None
        best_score = None
        for forms in INVERTIBILITY_CLAUSES:
            reduced = [system_reduce_form(current, form) for form in forms]
            if any(coefficient == ZERO and rhs == ONE for coefficient, rhs in reduced):
                continue
            variable_forms = [coefficient for coefficient, rhs in reduced if coefficient]
            if not variable_forms:
                unsatisfiable.add(current)
                return None
            score = (len(set(variable_forms)), sum(int(value.bit_count()) for value in set(variable_forms)))
            if best_score is None or score < best_score:
                best_score = score
                best = (forms, reduced)
        if best is None:
            solution = system_offset_solution(current)
            if not transform_is_invertible(solution):
                raise AssertionError("invertibility clauses accepted a singular transform")
            return solution
        forms, reduced = best
        prefix = current
        for position in range(N):
            if position:
                prefix = system_add(prefix, forms[position - 1], ZERO)
                if prefix is None:
                    break
            branch = system_add(prefix, forms[position], ONE)
            if branch is None:
                continue
            answer = recurse(branch)
            if answer is not None:
                return answer
        unsatisfiable.add(current)
        budget.check()
        return None

    answer = recurse(system)
    if answer is None:
        counters.increment("block_prunes")
    return answer


def derive_full_mapping(source_terms, target_terms, transform, counters=None):
    if counters is not None:
        counters.increment("full_multiset_checks")
    a, b, c = unpack_transform(transform)
    ai = mat_inverse(a)
    bi = mat_inverse(b)
    ci = mat_inverse(c)
    if ai is None or bi is None or ci is None:
        return None
    buckets = collections.defaultdict(list)
    for target_index, term in enumerate(target_terms):
        buckets[tuple(term)].append(int(target_index))
    for values in buckets.values():
        values.reverse()
    mapping = []
    for u, v, w in source_terms:
        transformed = (
            mat_mul(mat_mul(a, u), bi),
            mat_mul(mat_mul(b, v), ci),
            mat_mul(mat_mul(c, w), ai),
        )
        values = buckets.get(transformed)
        if not values:
            if counters is not None:
                counters.increment("full_multiset_prunes")
            return None
        mapping.append(int(values.pop()))
    if any(values for values in buckets.values()) or sorted(mapping) != list(range(len(target_terms))):
        if counters is not None:
            counters.increment("full_multiset_prunes")
        return None
    return mapping


def enumerate_small_space(system, source_terms, target_terms, budget, counters):
    counters.increment("small_space_calls")
    vectors = nullspace_basis(system)
    current = ZERO
    limit = ONE << len(vectors)
    for counter in range(1, limit):
        if (counter & int(0x3ff)) == ZERO:
            budget.check()
        changed = (counter & -counter).bit_length() - 1
        current = bxor(current, vectors[changed])
        counters.increment("small_space_vectors")
        if not transform_is_invertible(current):
            continue
        counters.increment("small_space_invertible_vectors")
        mapping = derive_full_mapping(source_terms, target_terms, current, counters)
        if mapping is not None:
            return current, mapping
    budget.check()
    counters.increment("small_space_exhausted_prunes")
    return None


def perfect_matching_exists(domains, remaining_sources, used_targets):
    matched_target = {}

    def augment(source, seen):
        for target in domains[source]:
            if target in used_targets or target in seen:
                continue
            seen.add(target)
            previous = matched_target.get(target)
            if previous is None or augment(previous, seen):
                matched_target[target] = source
                return True
        return False

    ordered = sorted(remaining_sources, key=lambda source: len(domains[source]))
    return all(augment(source, set()) for source in ordered)


def witness_record(source, target, orientation, transform, mapping):
    a, b, c = unpack_transform(transform)
    return {
        "schema": SCHEMA + "-witness",
        "source": source.path,
        "target": target.path,
        "source_alias": source.alias,
        "target_alias": target.alias,
        "source_raw_sha256": source.raw_sha256,
        "target_raw_sha256": target.raw_sha256,
        "orientation": orientation,
        "orientation_formula": ORIENTATION_FORMULAS[orientation],
        "A": matrix_record(a),
        "B": matrix_record(b),
        "C": matrix_record(c),
        "source_to_target": [int(value) for value in mapping],
        "source_to_target_1based": [int(value + 1) for value in mapping],
        "index_base": int(0),
        "equations": [
            "A U_i = U'_j B",
            "B V_i = V'_j C",
            "C W_i = W'_j A",
        ],
    }


class OrientationSearch(object):
    def __init__(self, source, target, orientation, budget, close_nullity, use_pair_profiles=True):
        self.source_scheme = source
        self.target_scheme = target
        self.orientation = orientation
        self.source_terms = orient_terms(source.terms, orientation)
        self.target_terms = target.terms
        self.source_index = InvariantIndex(self.source_terms, budget)
        self.target_index = InvariantIndex(self.target_terms, budget)
        self.budget = budget
        self.close_nullity = int(close_nullity)
        self.use_pair_profiles = bool(use_pair_profiles)
        self.counters = Counters()
        self.mapping = {}
        self.used_targets = set()
        self.initial_domains = {}
        self.witness = None
        self.exhaustion_reason = None
        self.started = time.monotonic()

    def compatible_with_mapping(self, source, target):
        assigned = sorted(self.mapping.items())
        for previous_source, previous_target in assigned:
            self.counters.increment("pair_checks")
            if self.source_index.pair(previous_source, source) != self.target_index.pair(previous_target, target):
                return False
        if len(assigned) >= 2:
            for first in range(len(assigned)):
                for second in range(first + 1, len(assigned)):
                    s1, t1 = assigned[first]
                    s2, t2 = assigned[second]
                    self.counters.increment("triple_checks")
                    if self.source_index.triple(s1, s2, source) != self.target_index.triple(t1, t2, target):
                        return False
        return True

    def current_domains(self):
        domains = {}
        for source in range(len(self.source_terms)):
            if source in self.mapping:
                continue
            candidates = []
            for target in self.initial_domains[source]:
                if target in self.used_targets:
                    continue
                self.counters.increment("forward_checks")
                if self.compatible_with_mapping(source, target):
                    candidates.append(target)
            domains[source] = tuple(candidates)
        return domains

    def dfs(self, system):
        self.budget.check()
        self.counters.increment("nodes")
        self.counters.max_depth = max(int(self.counters.max_depth), len(self.mapping))
        if len(self.mapping) == len(self.source_terms):
            transform = exact_simultaneous_invertible(system, self.budget, self.counters)
            if transform is None:
                self.budget.check()
                return False
            mapping = [self.mapping[index] for index in range(len(self.source_terms))]
            induced = derive_full_mapping(self.source_terms, self.target_terms, transform, self.counters)
            if induced is None:
                raise AssertionError("complete correspondence equations did not induce the target multiset")
            self.witness = witness_record(
                self.source_scheme, self.target_scheme, self.orientation, transform, mapping
            )
            self.counters.increment("solutions")
            return True
        domains = self.current_domains()
        self.budget.check()
        if any(not domain for domain in domains.values()):
            self.counters.increment("empty_domain_prunes")
            return False
        remaining = tuple(domains.keys())
        self.counters.increment("hall_checks")
        if not perfect_matching_exists(domains, remaining, self.used_targets):
            self.counters.increment("hall_prunes")
            return False
        source = min(remaining, key=lambda item: (len(domains[item]), item))
        for target in domains[source]:
            self.budget.count_branch()
            self.counters.increment("branches_considered")
            equations = correspondence_equations(self.source_terms[source], self.target_terms[target])
            next_system = system_add_many(system, equations)
            if next_system is None:
                raise AssertionError("homogeneous correspondence equations became inconsistent")
            self.counters.increment("assignments")
            self.counters.increment("equation_rows_added", len(equations))
            self.mapping[source] = target
            self.used_targets.add(target)
            nullity = VARIABLES - system_rank(next_system)
            if nullity <= self.close_nullity:
                closed = enumerate_small_space(
                    next_system,
                    self.source_terms,
                    self.target_terms,
                    self.budget,
                    self.counters,
                )
                if closed is not None:
                    transform, full_mapping = closed
                    self.witness = witness_record(
                        self.source_scheme,
                        self.target_scheme,
                        self.orientation,
                        transform,
                        full_mapping,
                    )
                    self.counters.increment("solutions")
                    return True
                self.budget.check()
            else:
                transform = exact_simultaneous_invertible(next_system, self.budget, self.counters)
                if transform is not None:
                    full_mapping = derive_full_mapping(
                        self.source_terms, self.target_terms, transform, self.counters
                    )
                    if full_mapping is not None:
                        self.witness = witness_record(
                            self.source_scheme,
                            self.target_scheme,
                            self.orientation,
                            transform,
                            full_mapping,
                        )
                        self.counters.increment("solutions")
                        return True
                    if self.dfs(next_system):
                        return True
            self.used_targets.remove(target)
            del self.mapping[source]
        self.budget.check()
        return False

    def run(self):
        self.budget.check()
        source_unary = collections.Counter(self.source_index.unary)
        target_unary = collections.Counter(self.target_index.unary)
        self.budget.check()
        if source_unary != target_unary:
            self.budget.check()
            self.exhaustion_reason = "unary_multiset"
            return self.report("exhausted")
        if self.source_index.global_pair_counter() != self.target_index.global_pair_counter():
            self.budget.check()
            self.exhaustion_reason = "pair_multiset"
            return self.report("exhausted")
        target_by_unary = collections.defaultdict(list)
        for target, key in enumerate(self.target_index.unary):
            target_by_unary[key].append(target)
        for source, key in enumerate(self.source_index.unary):
            self.budget.check()
            candidates = list(target_by_unary[key])
            if self.use_pair_profiles:
                source_profile = self.source_index.rooted_pair_profile(source)
                candidates = [
                    target
                    for target in candidates
                    if self.target_index.rooted_pair_profile(target) == source_profile
                ]
            self.initial_domains[source] = tuple(candidates)
        if any(not domain for domain in self.initial_domains.values()):
            self.budget.check()
            self.exhaustion_reason = "rooted_pair_profile"
            return self.report("exhausted")
        self.counters.increment("hall_checks")
        if not perfect_matching_exists(self.initial_domains, tuple(range(len(self.source_terms))), set()):
            self.budget.check()
            self.counters.increment("hall_prunes")
            self.exhaustion_reason = "initial_hall"
            return self.report("exhausted")
        try:
            found = self.dfs(EMPTY_SYSTEM)
        except SearchInterrupted as interrupted:
            self.exhaustion_reason = interrupted.reason
            return self.report("unknown")
        if found:
            return self.report("equivalent")
        self.budget.check()
        self.exhaustion_reason = "complete_branch_exhaustion"
        return self.report("exhausted")

    def report(self, status):
        return {
            "orientation": self.orientation,
            "formula": ORIENTATION_FORMULAS[self.orientation],
            "status": status,
            "decision_status": (
                "match" if status == "equivalent"
                else "no_match_complete_for_orientation" if status == "exhausted"
                else "timeout" if self.exhaustion_reason == "deadline"
                else "incomplete"
            ),
            "complete": status in ("equivalent", "exhausted"),
            "reason": self.exhaustion_reason,
            "elapsed_seconds": float(time.monotonic() - self.started),
            "initial_domain_sizes": [
                int(len(self.initial_domains.get(index, ())))
                for index in range(len(self.source_terms))
            ],
            "counters": self.counters.report(),
            "witness": self.witness,
        }


def compare_schemes(source, target, orientations, seconds, max_branches, close_nullity, use_pair_profiles=True, shared_budget=None):
    started = time.monotonic()
    if source.dimensions != target.dimensions or source.rank != target.rank:
        return {
            "schema": SCHEMA,
            "command": "compare",
            "status": "inequivalent",
            "decision_status": "no_match_complete",
            "complete": True,
            "reason": "dimension_or_rank_mismatch",
            "source": scheme_metadata(source),
            "target": scheme_metadata(target),
            "orientations": [],
            "elapsed_seconds": float(time.monotonic() - started),
        }
    if source.rank != RANK or source.dimensions != (N, N, N):
        raise DataError("the exact classifier accepts only 4x4x4 rank-47 inputs")
    source_validation = tensor_report(source.terms, include_mismatches=False)
    target_validation = tensor_report(target.terms, include_mismatches=False)
    if not source_validation["valid"] or not target_validation["valid"]:
        raise DataError("compare requires both inputs to reconstruct the native 4x4 multiplication tensor")
    budget = shared_budget if shared_budget is not None else SearchBudget(seconds, max_branches)
    all_native_orientations_requested = set(orientations) == set(ORIENTATIONS)
    orientation_results = []
    witness = None
    unknown = False
    interruption_reason = None
    for orientation in orientations:
        search = None
        try:
            budget.check()
            search = OrientationSearch(
                source,
                target,
                orientation,
                budget,
                close_nullity,
                use_pair_profiles=use_pair_profiles,
            )
            result = search.run()
        except SearchInterrupted as interrupted:
            interruption_reason = interrupted.reason
            if search is None:
                result = {
                    "orientation": orientation,
                    "formula": ORIENTATION_FORMULAS[orientation],
                    "status": "unknown",
                    "decision_status": "timeout" if interrupted.reason == "deadline" else "incomplete",
                    "complete": False,
                    "reason": interrupted.reason,
                    "elapsed_seconds": float(0),
                    "initial_domain_sizes": [],
                    "counters": Counters().report(),
                    "witness": None,
                }
            else:
                search.exhaustion_reason = interrupted.reason
                result = search.report("unknown")
        orientation_results.append(result)
        if result["status"] == "equivalent":
            witness = result["witness"]
            break
        if result["status"] == "unknown":
            unknown = True
            interruption_reason = result.get("reason") or interruption_reason
            break
    if witness is None and not unknown:
        try:
            budget.check()
        except SearchInterrupted as interrupted:
            unknown = True
            interruption_reason = interrupted.reason
    if witness is not None:
        status = "equivalent"
        complete = True
        reason = "constructive_witness"
    elif unknown or len(orientation_results) != len(orientations):
        status = "unknown"
        complete = False
        reason = interruption_reason or next(
            (result.get("reason") for result in orientation_results if result["status"] == "unknown"),
            "incomplete_orientation_search",
        )
    elif all(result["status"] == "exhausted" for result in orientation_results):
        status = "inequivalent" if all_native_orientations_requested else "no_match_requested"
        complete = True
        reason = "all_requested_orientations_exhausted"
    else:
        status = "unknown"
        complete = False
        reason = "incomplete_orientation_search"
    if status == "equivalent":
        decision_status = "match"
    elif status == "inequivalent" and all_native_orientations_requested:
        decision_status = "no_match_complete"
    elif status == "no_match_requested":
        decision_status = "no_match_complete_for_requested_orientations"
    elif reason == "deadline":
        decision_status = "timeout"
    else:
        decision_status = "incomplete"
    output = {
        "schema": SCHEMA,
        "command": "compare",
        "status": status,
        "decision_status": decision_status,
        "complete": complete,
        "reason": reason,
        "source": scheme_metadata(source),
        "target": scheme_metadata(target),
        "requested_orientations": list(orientations),
        "all_native_orientations_requested": all_native_orientations_requested,
        "orientation_formulas": dict(ORIENTATION_FORMULAS),
        "orientation_derivation": ORIENTATION_DERIVATION,
        "orientations": orientation_results,
        "witness": witness,
        "elapsed_seconds": float(time.monotonic() - started),
        "global_budget": {
            "elapsed_seconds": budget.elapsed(),
            "branches": int(budget.branches),
            "max_branches": int(budget.max_branches),
            "deadline_enabled": budget.deadline is not None,
        },
    }
    if witness is not None:
        output["independent_verification"] = verify_memory_witness(
            source, target, witness
        ) if source.path.startswith("memory://") or target.path.startswith("memory://") else verify_witness_object(
            witness, source_override=source.path, target_override=target.path
        )
        if not output["independent_verification"]["valid"]:
            raise AssertionError("search witness failed the independent verifier")
    return output


def _verify_parse(path):
    real = os.path.realpath(path)
    with open(real, "rb") as source:
        raw = source.read()
    lines = raw.splitlines()
    if len(lines) != 4:
        raise DataError("independent verifier: expected four lines in %s" % real)
    header = lines[0].decode("ascii").split()
    if header != ["4", "4", "4", "47"]:
        raise DataError("independent verifier: header is not exactly 4 4 4 47 in %s" % real)
    factors = []
    for line_number in range(3):
        tokens = lines[line_number + 1].decode("ascii").split()
        if len(tokens) != RANK * N2 or any(token not in ("0", "1") for token in tokens):
            raise DataError("independent verifier: malformed payload line %d in %s" % (line_number + 1, real))
        matrices = []
        for term in range(RANK):
            value = ZERO
            for coordinate in range(N2):
                if tokens[term * N2 + coordinate] == "1":
                    value |= ONE << coordinate
            matrices.append(value)
        factors.append(matrices)
    terms = tuple(tuple(factors[factor][term] for factor in range(3)) for term in range(RANK))
    return real, hashlib.sha256(raw).hexdigest(), terms


def _verify_transpose(value):
    output = ZERO
    for source_row in range(N):
        for source_column in range(N):
            bit = (value >> (source_row * N + source_column)) & ONE
            output |= bit << (source_column * N + source_row)
    return output


def _verify_orient(terms, orientation):
    output = []
    for u, v, w in terms:
        if orientation == "id":
            output.append((u, v, w))
        elif orientation == "cyc":
            output.append((v, w, u))
        elif orientation == "cyc2":
            output.append((w, u, v))
        elif orientation == "rev":
            output.append((_verify_transpose(w), _verify_transpose(v), _verify_transpose(u)))
        elif orientation == "rev_cyc":
            output.append((_verify_transpose(u), _verify_transpose(w), _verify_transpose(v)))
        elif orientation == "rev_cyc2":
            output.append((_verify_transpose(v), _verify_transpose(u), _verify_transpose(w)))
        else:
            raise DataError("independent verifier: unknown orientation %s" % orientation)
    return tuple(output)


def _verify_mul(left, right):
    output = ZERO
    for row in range(N):
        for column in range(N):
            bit = ZERO
            for middle in range(N):
                bit = bxor(
                    bit,
                    ((left >> (row * N + middle)) & ONE)
                    & ((right >> (middle * N + column)) & ONE),
                )
            output |= bit << (row * N + column)
    return output


def _verify_inverse(value):
    augmented = []
    for row in range(N):
        augmented.append(
            int((value >> (row * N)) & int(0xf)) | (ONE << (N + row))
        )
    pivot_row = ZERO
    for column in range(N):
        candidate = next(
            (row for row in range(pivot_row, N) if (augmented[row] >> column) & ONE),
            None,
        )
        if candidate is None:
            return None
        augmented[pivot_row], augmented[candidate] = augmented[candidate], augmented[pivot_row]
        for row in range(N):
            if row != pivot_row and ((augmented[row] >> column) & ONE):
                augmented[row] = bxor(augmented[row], augmented[pivot_row])
        pivot_row += ONE
    inverse = ZERO
    for row in range(N):
        inverse |= ((augmented[row] >> N) & int(0xf)) << (row * N)
    if _verify_mul(value, inverse) != IDENTITY or _verify_mul(inverse, value) != IDENTITY:
        return None
    return inverse


def _matrix_from_witness(record, name):
    if not isinstance(record, dict) or "packed_hex" not in record or "rows" not in record:
        raise DataError("independent verifier: witness matrix %s lacks packed_hex or rows" % name)
    if not re.fullmatch(r"[0-9a-fA-F]{1,4}", str(record["packed_hex"])):
        raise DataError("independent verifier: malformed packed_hex for %s" % name)
    packed = int(str(record["packed_hex"]), 16)
    rows = record["rows"]
    if not isinstance(rows, list) or len(rows) != N or any(not isinstance(row, list) or len(row) != N for row in rows):
        raise DataError("independent verifier: malformed rows for %s" % name)
    rebuilt = ZERO
    for row in range(N):
        for column in range(N):
            bit = rows[row][column]
            if bit not in (0, 1):
                raise DataError("independent verifier: non-binary matrix entry for %s" % name)
            rebuilt |= int(bit) << (row * N + column)
    if rebuilt != packed:
        raise DataError("independent verifier: rows and packed_hex disagree for %s" % name)
    return packed


def extract_witness(document):
    if not isinstance(document, dict):
        raise DataError("witness JSON must be an object")
    if document.get("schema") == SCHEMA + "-witness":
        return document
    witness = document.get("witness")
    if isinstance(witness, dict):
        return witness
    raise DataError("JSON object contains no constructive witness")


def verify_witness_object(witness_document, source_override=None, target_override=None):
    witness = extract_witness(witness_document)
    source_path = source_override or witness.get("source")
    target_path = target_override or witness.get("target")
    if not source_path or not target_path:
        raise DataError("independent verifier needs source and target paths")
    source_path, source_hash, source_terms = _verify_parse(source_path)
    target_path, target_hash, target_terms = _verify_parse(target_path)
    hash_errors = []
    if witness.get("source_raw_sha256") and witness["source_raw_sha256"] != source_hash:
        hash_errors.append("source hash mismatch")
    if witness.get("target_raw_sha256") and witness["target_raw_sha256"] != target_hash:
        hash_errors.append("target hash mismatch")
    orientation = witness.get("orientation")
    oriented = _verify_orient(source_terms, orientation)
    a = _matrix_from_witness(witness.get("A"), "A")
    b = _matrix_from_witness(witness.get("B"), "B")
    c = _matrix_from_witness(witness.get("C"), "C")
    ai = _verify_inverse(a)
    bi = _verify_inverse(b)
    ci = _verify_inverse(c)
    mapping = witness.get("source_to_target")
    mapping_error = None
    if not isinstance(mapping, list) or len(mapping) != RANK or any(not isinstance(value, int) for value in mapping):
        mapping_error = "mapping must contain 47 integer target indices"
    elif sorted(mapping) != list(range(RANK)):
        mapping_error = "mapping is not a bijection of 0,...,46"
    mapping_entries_checked = ZERO
    cross_equations_checked = ZERO
    mismatches = []
    if ai is None or bi is None or ci is None:
        mismatches.append({"reason": "one or more witness matrices are singular"})
    elif mapping_error is None:
        for source_index, target_index in enumerate(mapping):
            mapping_entries_checked += ONE
            cross_equations_checked += 3
            u, v, w = oriented[source_index]
            up, vp, wp = target_terms[target_index]
            got = (
                _verify_mul(_verify_mul(a, u), bi),
                _verify_mul(_verify_mul(b, v), ci),
                _verify_mul(_verify_mul(c, w), ai),
            )
            expected = (up, vp, wp)
            cross_products = (
                (_verify_mul(a, u), _verify_mul(up, b)),
                (_verify_mul(b, v), _verify_mul(vp, c)),
                (_verify_mul(c, w), _verify_mul(wp, a)),
            )
            failed_cross_equations = [
                equation_index
                for equation_index, (left, right) in enumerate(cross_products)
                if left != right
            ]
            if got != expected or failed_cross_equations:
                mismatches.append({
                    "source_index": int(source_index),
                    "target_index": int(target_index),
                    "failed_cross_equations": failed_cross_equations,
                    "got": ["%04x" % value for value in got],
                    "expected": ["%04x" % value for value in expected],
                })
    valid = not hash_errors and mapping_error is None and not mismatches
    return {
        "schema": SCHEMA + "-verification",
        "command": "verify-witness",
        "valid": bool(valid),
        "source": source_path,
        "target": target_path,
        "source_raw_sha256": source_hash,
        "target_raw_sha256": target_hash,
        "orientation": orientation,
        "mapping_entries_checked": int(mapping_entries_checked),
        "cross_equations_checked": int(cross_equations_checked),
        "hash_errors": hash_errors,
        "mapping_error": mapping_error,
        "term_mismatches": mismatches,
        "independent_path": (
            "fresh byte parse, separately implemented orientation, Gauss inversion, packed multiplication, "
            "and direct mapped-triple comparison; no search equations reused"
        ),
    }


def verify_memory_witness(source, target, witness_document):
    witness = extract_witness(witness_document)
    orientation = witness["orientation"]
    oriented = _verify_orient(source.terms, orientation)
    a = _matrix_from_witness(witness["A"], "A")
    b = _matrix_from_witness(witness["B"], "B")
    c = _matrix_from_witness(witness["C"], "C")
    ai, bi, ci = _verify_inverse(a), _verify_inverse(b), _verify_inverse(c)
    mapping = witness["source_to_target"]
    mismatches = []
    if ai is None or bi is None or ci is None or sorted(mapping) != list(range(len(target.terms))):
        mismatches.append({"reason": "singular transform or non-bijection"})
    else:
        for source_index, target_index in enumerate(mapping):
            u, v, w = oriented[source_index]
            got = (
                _verify_mul(_verify_mul(a, u), bi),
                _verify_mul(_verify_mul(b, v), ci),
                _verify_mul(_verify_mul(c, w), ai),
            )
            if got != target.terms[target_index]:
                mismatches.append({"source_index": source_index, "target_index": target_index})
    return {
        "schema": SCHEMA + "-verification",
        "command": "verify-memory-witness",
        "valid": not mismatches,
        "term_mismatches": mismatches,
        "mapping_entries_checked": len(mapping),
        "independent_path": "separate orientation, inversion, multiplication, and direct term comparison",
    }


def deterministic_control_matrices():
    matrices = (
        int(0x8423),
        int(0xc421),
        int(0x8c61),
    )
    if not all(is_invertible(matrix) for matrix in matrices):
        raise AssertionError("deterministic control matrices must be invertible")
    return matrices


def make_synthetic_target(source, orientation):
    oriented = orient_terms(source.terms, orientation)
    a, b, c = deterministic_control_matrices()
    ai, bi, ci = mat_inverse(a), mat_inverse(b), mat_inverse(c)
    transformed = [
        (
            mat_mul(mat_mul(a, u), bi),
            mat_mul(mat_mul(b, v), ci),
            mat_mul(mat_mul(c, w), ai),
        )
        for u, v, w in oriented
    ]
    permutation = [int((17 * index + 9) % RANK) for index in range(RANK)]
    target_terms = [None] * RANK
    for source_index, target_index in enumerate(permutation):
        target_terms[target_index] = transformed[source_index]
    target = MemoryScheme("synthetic-" + orientation, target_terms)
    return target, permutation, (a, b, c)


def algebra_control_report(source, budget):
    a, b, c = deterministic_control_matrices()
    vector = a | (b << N2) | (c << (2 * N2))
    equation_rows_checked = ZERO
    equation_failures = []
    action_failures = []
    for orientation in ORIENTATIONS:
        target, expected_mapping, ignored_transform = make_synthetic_target(source, orientation)
        oriented = orient_terms(source.terms, orientation)
        for source_index, target_index in enumerate(expected_mapping):
            budget.check()
            rows = correspondence_equations(oriented[source_index], target.terms[target_index])
            equation_rows_checked += len(rows)
            bad = [
                int(index)
                for index, row in enumerate(rows)
                if ((row & vector).bit_count() & ONE)
            ]
            if bad:
                equation_failures.append({
                    "orientation": orientation,
                    "source_index": int(source_index),
                    "row_indices": bad,
                })
            induced = derive_full_mapping(oriented, target.terms, vector)
            if induced is None or induced != expected_mapping:
                action_failures.append({
                    "orientation": orientation,
                    "expected_mapping": expected_mapping,
                    "induced_mapping": induced,
                })
                break
    dpll_counters = Counters()
    unconstrained = exact_simultaneous_invertible(EMPTY_SYSTEM, budget, dpll_counters)
    forced_singular = EMPTY_SYSTEM
    for variable in range(N2):
        forced_singular = system_add(forced_singular, ONE << variable, ZERO)
    singular_answer = exact_simultaneous_invertible(forced_singular, budget, dpll_counters)
    inverse_checks = []
    for matrix in (a, b, c):
        inverse = mat_inverse(matrix)
        inverse_checks.append(
            inverse is not None
            and mat_mul(matrix, inverse) == IDENTITY
            and mat_mul(inverse, matrix) == IDENTITY
        )
    valid = (
        not equation_failures
        and not action_failures
        and unconstrained is not None
        and transform_is_invertible(unconstrained)
        and singular_answer is None
        and all(inverse_checks)
    )
    return {
        "valid": bool(valid),
        "equation_rows_checked": int(equation_rows_checked),
        "equation_failures": equation_failures,
        "known_action_failures": action_failures,
        "inverse_checks": inverse_checks,
        "unconstrained_invertible_sat": unconstrained is not None,
        "forced_singular_unsat": singular_answer is None,
        "dpll_counters": dpll_counters.report(),
    }


def run_controls(args):
    started = time.monotonic()
    budget = SearchBudget(args.seconds, args.max_branches)
    validation = []
    all_valid = True
    for alias in DEFAULT_ALIASES:
        budget.check()
        scheme = parse_scheme(alias)
        report = validate_scheme(scheme)
        validation.append({"alias": alias, "valid": report["valid"], "metadata": report["metadata"]})
        all_valid = all_valid and report["valid"]
    source = parse_scheme(args.synthetic_source)
    algebra = algebra_control_report(source, budget)
    synthetic = []
    for orientation in ORIENTATIONS:
        try:
            budget.check()
        except SearchInterrupted as interrupted:
            synthetic.append({"orientation": orientation, "status": "unknown", "reason": interrupted.reason})
            break
        target, expected_mapping, expected_transform = make_synthetic_target(source, orientation)
        comparison = compare_schemes(
            source,
            target,
            (orientation,),
            args.seconds,
            args.max_branches,
            args.close_nullity,
            use_pair_profiles=not args.no_pair_profiles,
            shared_budget=budget,
        )
        mapping_ok = comparison.get("witness") is not None
        synthetic.append({
            "orientation": orientation,
            "status": comparison["status"],
            "valid_witness": bool(mapping_ok and comparison["independent_verification"]["valid"]),
            "expected_mapping": expected_mapping,
            "known_transform": {
                "A": matrix_record(expected_transform[0]),
                "B": matrix_record(expected_transform[1]),
                "C": matrix_record(expected_transform[2]),
            },
            "comparison": comparison,
        })
        if comparison["status"] != "equivalent":
            break
    optimized = []
    if not args.skip_optimized:
        for left, right in CONTROL_PAIRS:
            try:
                budget.check()
            except SearchInterrupted as interrupted:
                optimized.append({"source": left, "target": right, "status": "unknown", "reason": interrupted.reason})
                break
            comparison = compare_schemes(
                parse_scheme(left),
                parse_scheme(right),
                ORIENTATIONS,
                args.seconds,
                args.max_branches,
                args.close_nullity,
                use_pair_profiles=not args.no_pair_profiles,
                shared_budget=budget,
            )
            optimized.append(comparison)
            if comparison["status"] == "unknown":
                break
    synthetic_ok = len(synthetic) == len(ORIENTATIONS) and all(
        entry.get("status") == "equivalent" and entry.get("valid_witness") for entry in synthetic
    )
    optimized_ok = args.skip_optimized or (
        len(optimized) == len(CONTROL_PAIRS)
        and all(entry.get("status") == "equivalent" for entry in optimized)
    )
    complete = all_valid and algebra["valid"] and synthetic_ok and optimized_ok
    return {
        "schema": SCHEMA,
        "command": "controls",
        "status": "passed" if complete else "incomplete_or_failed",
        "complete": bool(complete),
        "all_inputs_valid": bool(all_valid),
        "algebra_controls": algebra,
        "input_validation": validation,
        "synthetic_six_orientation_controls": synthetic,
        "optimized_sandwich_controls": optimized,
        "optimized_controls_skipped": bool(args.skip_optimized),
        "elapsed_seconds": float(time.monotonic() - started),
        "global_budget": {
            "elapsed_seconds": budget.elapsed(),
            "branches": int(budget.branches),
            "max_branches": int(budget.max_branches),
        },
    }


def comparison_pairs(mode, aliases):
    if mode == "controls":
        return list(CONTROL_PAIRS)
    if mode == "published":
        return [(local, published) for local in LOCAL_ALIASES for published in PUBLISHED_ALIASES] + list(CONTROL_PAIRS)
    return list(itertools.combinations(aliases, 2))


def run_campaign(args, command_name):
    aliases = tuple(args.inputs) if args.inputs else DEFAULT_ALIASES
    schemes = collections.OrderedDict((alias, parse_scheme(alias)) for alias in aliases)
    pairs = comparison_pairs(args.mode, aliases)
    for left, right in pairs:
        if left not in schemes:
            schemes[left] = parse_scheme(left)
        if right not in schemes:
            schemes[right] = parse_scheme(right)
    budget = SearchBudget(args.seconds, args.max_branches)
    results = []
    matrix = collections.OrderedDict(
        (alias, collections.OrderedDict((other, "self" if alias == other else "pending") for other in schemes))
        for alias in schemes
    )
    for left, right in pairs:
        try:
            budget.check()
        except SearchInterrupted as interrupted:
            results.append({"source_alias": left, "target_alias": right, "status": "unknown", "complete": False, "reason": interrupted.reason})
            matrix[left][right] = "unknown"
            matrix[right][left] = "unknown"
            break
        comparison = compare_schemes(
            schemes[left],
            schemes[right],
            ORIENTATIONS,
            args.seconds,
            args.max_branches,
            args.close_nullity,
            use_pair_profiles=not args.no_pair_profiles,
            shared_budget=budget,
        )
        compact = {
            "source_alias": left,
            "target_alias": right,
            "status": comparison["status"],
            "decision_status": comparison["decision_status"],
            "complete": comparison["complete"],
            "reason": comparison["reason"],
            "elapsed_seconds": comparison["elapsed_seconds"],
            "branches": comparison["global_budget"]["branches"],
            "witness": comparison.get("witness"),
            "orientation_summaries": [
                {
                    "orientation": result["orientation"],
                    "status": result["status"],
                    "reason": result["reason"],
                    "counters": result["counters"],
                }
                for result in comparison["orientations"]
            ],
        }
        results.append(compact)
        matrix[left][right] = comparison["status"]
        matrix[right][left] = comparison["status"]
        if comparison["status"] == "unknown":
            break
    complete = len(results) == len(pairs) and all(result.get("complete") for result in results)
    return {
        "schema": SCHEMA,
        "command": command_name,
        "mode": args.mode,
        "status": "complete" if complete else "unknown",
        "complete": bool(complete),
        "inputs": [scheme_metadata(scheme) for scheme in schemes.values()],
        "pair_count_requested": int(len(pairs)),
        "pair_count_completed": int(sum(1 for result in results if result.get("complete"))),
        "results": results,
        "table": matrix,
        "global_budget": {
            "elapsed_seconds": budget.elapsed(),
            "branches": int(budget.branches),
            "max_branches": int(budget.max_branches),
        },
    }


def parse_orientations(value):
    if value == "all":
        return ORIENTATIONS
    requested = tuple(token.strip() for token in value.split(",") if token.strip())
    unknown = [token for token in requested if token not in ORIENTATIONS]
    if unknown or not requested:
        raise argparse.ArgumentTypeError(
            "orientations must be 'all' or a comma-separated subset of %s" % ",".join(ORIENTATIONS)
        )
    return requested


def add_search_options(parser, default_seconds=285.0):
    parser.add_argument("--seconds", type=float, default=float(default_seconds), help="internal wall deadline; 0 disables it")
    parser.add_argument("--max-branches", type=int, default=0, help="explicit DFS branch cap; 0 is unlimited")
    parser.add_argument(
        "--close-nullity",
        type=int,
        default=16,
        help="completely enumerate a branch once its 48-variable nullity is at most this value",
    )
    parser.add_argument(
        "--no-pair-profiles",
        action="store_true",
        help="validation control: disable rooted pair-profile candidate pruning; exact pair/triple DFS checks remain",
    )


def build_parser():
    aliases = "\n".join("  %-20s %s" % (alias, path) for alias, path in catalog_paths().items())
    epilog = (
        "Native orientations derive from tr(U V W) with W[k,i]: "
        + ", ".join("%s=%s" % item for item in ORIENTATION_FORMULAS.items())
        + "\n\nCatalog aliases (R47_DATA_ROOT=%s):\n%s" % (DATA_ROOT, aliases)
    )
    parser = argparse.ArgumentParser(
        description="Complete constructive equivalence classifier for native rank-47 4x4 GF(2) schemes.",
        epilog=epilog,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--pretty", action="store_true", help="indent JSON output")
    subparsers = parser.add_subparsers(dest="command", required=True)

    validate = subparsers.add_parser("validate", help="strictly parse, hash, stat, and reconstruct inputs in all six orientations")
    validate.add_argument("inputs", nargs="*", help="paths or aliases; default is all eleven required inputs")

    compare = subparsers.add_parser("compare", aliases=["classify"], help="compare two schemes and emit a witness or a complete/unknown result")
    compare.add_argument("source")
    compare.add_argument("target")
    compare.add_argument("--orientations", type=parse_orientations, default=ORIENTATIONS)
    add_search_options(compare)

    controls = subparsers.add_parser("controls", help="validate eleven inputs, six synthetic orientations, and two optimized pairs")
    controls.add_argument("--synthetic-source", default="local-c561")
    controls.add_argument("--skip-optimized", action="store_true", help="run only parser/tensor and synthetic controls")
    add_search_options(controls)

    campaign = subparsers.add_parser("campaign", help="run a machine-readable exact comparison campaign")
    campaign.add_argument("inputs", nargs="*", help="paths or aliases; default is the eleven required inputs")
    campaign.add_argument("--mode", choices=("published", "controls", "all"), default="published")
    add_search_options(campaign)

    table = subparsers.add_parser("table", help="run comparisons and emit a symmetric JSON status table")
    table.add_argument("inputs", nargs="*", help="paths or aliases; default is the eleven required inputs")
    table.add_argument("--mode", choices=("published", "controls", "all"), default="all")
    add_search_options(table)

    verify = subparsers.add_parser("verify-witness", help="freshly parse and independently verify a witness JSON document")
    verify.add_argument("witness", help="JSON file containing a witness or a compare result; '-' reads stdin")
    verify.add_argument("--source", help="override witness source path")
    verify.add_argument("--target", help="override witness target path")
    return parser


def json_default(value):
    try:
        return int(value)
    except Exception:
        return str(value)


def emit(document, pretty=False):
    if pretty:
        text = json.dumps(document, sort_keys=True, indent=2, default=json_default)
    else:
        text = json.dumps(document, sort_keys=True, separators=(",", ":"), default=json_default)
    sys.stdout.write(text + "\n")


def normalize_sage_argv():
    if len(sys.argv) >= 2 and sys.argv[0] == "--":
        sys.argv[:] = [sys.argv[1]] + sys.argv[2:]


def main(argv=None):
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        if args.command == "validate":
            inputs = args.inputs or list(DEFAULT_ALIASES)
            reports = [validate_scheme(parse_scheme(value)) for value in inputs]
            valid = all(report["valid"] for report in reports)
            document = {
                "schema": SCHEMA,
                "command": "validate",
                "status": "valid" if valid else "invalid",
                "valid": bool(valid),
                "orientation_formulas": dict(ORIENTATION_FORMULAS),
                "orientation_derivation": ORIENTATION_DERIVATION,
                "inputs": reports,
            }
            emit(document, args.pretty)
            return 0 if valid else 1
        if args.command in ("compare", "classify"):
            source = parse_scheme(args.source)
            target = parse_scheme(args.target)
            document = compare_schemes(
                source,
                target,
                tuple(args.orientations),
                args.seconds,
                args.max_branches,
                args.close_nullity,
                use_pair_profiles=not args.no_pair_profiles,
            )
            emit(document, args.pretty)
            return 3 if document["status"] == "unknown" else 0
        if args.command == "controls":
            document = run_controls(args)
            emit(document, args.pretty)
            return 0 if document["status"] == "passed" else 3
        if args.command in ("campaign", "table"):
            document = run_campaign(args, args.command)
            emit(document, args.pretty)
            return 0 if document["complete"] else 3
        if args.command == "verify-witness":
            if args.witness == "-":
                raw = sys.stdin.read()
            else:
                with open(args.witness, "r", encoding="utf-8") as source:
                    raw = source.read()
            document = verify_witness_object(json.loads(raw), args.source, args.target)
            emit(document, args.pretty)
            return 0 if document["valid"] else 1
        raise DataError("unknown command")
    except (DataError, OSError, ValueError, json.JSONDecodeError) as error:
        emit({
            "schema": SCHEMA,
            "command": getattr(args, "command", None),
            "status": "error",
            "decision_status": "error",
            "complete": False,
            "error": str(error),
        }, getattr(args, "pretty", False))
        return 2
    except SearchInterrupted as interrupted:
        emit({
            "schema": SCHEMA,
            "command": getattr(args, "command", None),
            "status": "unknown",
            "decision_status": "timeout" if interrupted.reason == "deadline" else "incomplete",
            "complete": False,
            "reason": interrupted.reason,
        }, getattr(args, "pretty", False))
        return 3


if __name__ in ("__main__", "sage.all") and os.environ.get("R47_EQUIVALENCE_LIBRARY") != "1":
    normalize_sage_argv()
    exit_code = main()
    if __name__ == "sage.all":
        sys.stdout.flush()
        sys.stderr.flush()
        os._exit(int(exit_code))
    sys.exit(exit_code)
