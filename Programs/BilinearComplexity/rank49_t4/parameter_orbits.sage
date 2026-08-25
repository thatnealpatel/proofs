#!/usr/bin/env sage
"""Exact acceptance checker for the rank-49 T4 parameter correspondence."""

from collections import Counter
from datetime import datetime, timezone
from hashlib import sha256
from itertools import combinations, product
from pathlib import Path
import argparse
import json
import os
import platform
import sys
import tempfile

from sage.all import GF, FractionField, PolynomialRing, identity_matrix, matrix, vector
from sage.env import SAGE_VERSION


SCRIPT_PATH = Path(sys.argv[0]).resolve()
SCRIPT_DIR = SCRIPT_PATH.parent
REPOSITORY_ROOT = SCRIPT_PATH.parents[3]
ARTIFACT_PATH = SCRIPT_DIR / "artifacts" / "parameter_orbits.json"
SOURCE_FIXTURE_RELATIVE_TO_SCRIPT = Path("fixtures") / "4x4x4_m49_c680_iteration65_Z2.txt"
SOURCE_PATH = SCRIPT_DIR / SOURCE_FIXTURE_RELATIVE_TO_SCRIPT
SOURCE_SHA256 = "5fc92a6bf83fc29d9527ab100bad5d72d769178b616b31a36c3c0c0b8ad9d09d"
ORIGINAL_EXTERNAL_SOURCE_LOCATOR = "/home/exedev/x/tensor/data/z2/4x4x4_m49_c680_iteration65_Z2.txt"
BASE_GIT_REVISION = "6866f8be63692dc918e26d75db9414325b03b78c"
HISTORICAL_T3_CERTIFICATE_SHA256 = "2221bd3c1bc082cc54ccd21912f7277d954dbb78429675d5a6e57b5509ffaf71"
T3_LEAN_PROVENANCE_PATH = "Proofs/BilinearComplexity/PairedCircuit.lean"
T3_LEAN_PROVENANCE_SHA256 = "2589a379ec7d9aaf1dbf8972cac0833bc39cc34ba28de1f477165981789001fa"
ENCODED_T3_UPDATES_SHA256 = "71163385c61ba5c79fca4a1e9189d1e7513899449189bfd948c7d6fc89d83dc2"
ENCODED_T3_UPDATES = {
    "s": "t/(1+t)",
    "s_part": {"1": {"U": "0500"}, "37": {"U": "0500"}, "42": {"U": "0500"}},
    "t_part": {"14": {"W": "0070"}, "29": {"U": "9990"}, "37": {"W": "7707"}, "42": {"W": "0070"}},
}
DECLARED_FINITE_FIELD_DEGREES = (1, 2)
ORIENTATIONS = ("abc", "bca", "cab", "acb", "cba", "bac")
ORIENTATION_FORMULAS = {
    "abc": ("U", "V", "W"),
    "bca": ("V", "W", "U"),
    "cab": ("W", "U", "V"),
    "acb": ("W^T", "V^T", "U^T"),
    "cba": ("V^T", "U^T", "W^T"),
    "bac": ("U^T", "W^T", "V^T"),
}
CHANGED_TERMS = (1, 14, 29, 37, 42)
LEG_NAMES = ("U", "V", "W")


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def file_sha256(path):
    return sha256(path.read_bytes()).hexdigest()


def json_default(value):
    try:
        return int(value)
    except (TypeError, ValueError):
        raise TypeError("not JSON serializable: %r" % (value,))


def canonical_json_bytes(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True, default=json_default).encode("ascii")


def digest_records(records):
    h = sha256()
    count = 0
    for record in records:
        h.update(canonical_json_bytes(record))
        h.update(b"\n")
        count += 1
    return h.hexdigest(), count


def parse_source():
    raw = SOURCE_PATH.read_bytes()
    require(sha256(raw).hexdigest() == SOURCE_SHA256, "canonical source hash mismatch")
    lines = raw.decode("ascii").splitlines()
    require(len(lines) == 4, "source must have one header and three factor rows")
    require([int(x) for x in lines[0].split()] == [4, 4, 4, 49], "source header mismatch")
    field = GF(2)
    factor_rows = []
    for line in lines[1:]:
        entries = [int(x) for x in line.split()]
        require(len(entries) == 49 * 16, "source factor row has wrong length")
        require(all(x in (0, 1) for x in entries), "source is not binary")
        factor_rows.append(tuple(matrix(field, 4, 4, entries[16 * i:16 * (i + 1)]) for i in range(49)))
    return tuple(tuple(factor_rows[leg][i] for leg in range(3)) for i in range(49))


def encoded_family_specification():
    specification = json.loads(canonical_json_bytes(ENCODED_T3_UPDATES).decode("ascii"))
    require(sha256(canonical_json_bytes(specification)).hexdigest() == ENCODED_T3_UPDATES_SHA256, "encoded T3 update hash mismatch")
    require(specification["s"] == "t/(1+t)", "encoded T3 rational coefficient mismatch")
    require(tuple(sorted(int(index) for index in set(specification["s_part"]) | set(specification["t_part"]))) == CHANGED_TERMS, "encoded T3 support mismatch")
    return specification


def mask_matrix(field, mask_hex):
    value = int(mask_hex, 16) if isinstance(mask_hex, str) else int(mask_hex)
    return matrix(field, 4, 4, [field((value >> i) & 1) for i in range(16)])


def matrix_mask(binary_matrix):
    return "%04x" % sum(int(x) << i for i, x in enumerate(binary_matrix.list()))


def change_terms_ring(terms, field):
    return tuple(tuple(factor.change_ring(field) for factor in term) for term in terms)


def construct_family(base_terms, field, beta, family_spec):
    require(beta != 0, "family parameter must be nonzero")
    terms = [list(term) for term in change_terms_ring(base_terms, field)]
    tau = beta + field(1)
    sigma = tau / beta
    for term_text, updates in family_spec["s_part"].items():
        term = int(term_text)
        for leg, leg_name in enumerate(LEG_NAMES):
            if leg_name in updates:
                terms[term][leg] += sigma * mask_matrix(field, updates[leg_name])
    for term_text, updates in family_spec["t_part"].items():
        term = int(term_text)
        for leg, leg_name in enumerate(LEG_NAMES):
            if leg_name in updates:
                terms[term][leg] += tau * mask_matrix(field, updates[leg_name])
    return tuple(tuple(term) for term in terms)


def orient_term(term, orientation):
    u, v, w = term
    if orientation == "abc":
        return u, v, w
    if orientation == "bca":
        return v, w, u
    if orientation == "cab":
        return w, u, v
    if orientation == "acb":
        return w.transpose(), v.transpose(), u.transpose()
    if orientation == "cba":
        return v.transpose(), u.transpose(), w.transpose()
    if orientation == "bac":
        return u.transpose(), w.transpose(), v.transpose()
    raise ValueError(orientation)


def evaluate_fraction(value, point, polynomial_ring):
    numerator = polynomial_ring(value.numerator())(point)
    denominator = polynomial_ring(value.denominator())(point)
    require(denominator != 0, "attempted specialization at a pole")
    return numerator / denominator


def verify_family(base_terms, generic_terms, polynomial_ring, beta):
    field2 = GF(2)
    source_tensor_coordinates = 0
    for a, b_index, b_prime, c, c_prime, a_prime in product(range(4), repeat=6):
        source_value = sum((term[0][a, b_index] * term[1][b_prime, c] * term[2][c_prime, a_prime] for term in base_terms), field2.zero())
        expected = field2((b_index == b_prime) and (c == c_prime) and (a == a_prime))
        require(source_value == expected, "canonical source does not sum to the 4x4 matrix-multiplication tensor")
        source_tensor_coordinates += 1
    require(source_tensor_coordinates == 4096, "source tensor coordinate coverage failed")
    base_at_one = []
    for term in generic_terms:
        base_at_one.append(tuple(matrix(field2, 4, 4, [field2(evaluate_fraction(x, field2.one(), polynomial_ring)) for x in factor.list()]) for factor in term))
    require(tuple(base_at_one) == base_terms, "generic family does not specialize to the source at b=1")
    for i in range(49):
        if i not in CHANGED_TERMS:
            for leg in range(3):
                require(generic_terms[i][leg] == base_terms[i][leg].change_ring(generic_terms[i][leg].base_ring()), "an anchor term varies")
    changed = CHANGED_TERMS
    flattened_base = [[vector(generic_terms[0][0].base_ring(), base_terms[i][leg].list()) for leg in range(3)] for i in changed]
    flattened_generic = [[vector(generic_terms[0][0].base_ring(), generic_terms[i][leg].list()) for leg in range(3)] for i in changed]
    family_identity_coordinates = 0
    for x, y, z in product(range(16), repeat=3):
        old_value = sum((term[0][x] * term[1][y] * term[2][z] for term in flattened_base), generic_terms[0][0].base_ring().zero())
        new_value = sum((term[0][x] * term[1][y] * term[2][z] for term in flattened_generic), generic_terms[0][0].base_ring().zero())
        require(old_value == new_value, "encoded five-term family tensor identity failed")
        family_identity_coordinates += 1
    require(family_identity_coordinates == 4096, "family tensor coordinate coverage failed")
    return {
        "canonical_source_target_coordinates_checked": source_tensor_coordinates,
        "five_term_family_identity_coordinates_checked": family_identity_coordinates,
    }


def denominator_b_exponent(value, polynomial_ring, beta):
    denominator = polynomial_ring(value.denominator())
    require(denominator != 0, "zero denominator")
    exponent = 0
    while denominator != 1 and denominator[0] == 0:
        quotient, remainder = denominator.quo_rem(beta)
        require(remainder == 0, "denominator division failed")
        denominator = quotient
        exponent += 1
    require(denominator == 1, "a denominator has a factor other than b")
    return exponent


def matrix_denominator_bound(value, polynomial_ring, beta):
    return max((denominator_b_exponent(x, polynomial_ring, beta) for x in value.list()), default=0)


def factor_list(polynomial):
    if polynomial in (0, 1):
        return []
    return [[str(factor.monic()), int(exponent)] for factor, exponent in polynomial.factor()]


def maximal_minor_certificate(value, polynomial_ring, beta):
    rank = int(value.rank())
    denominator_exponent = matrix_denominator_bound(value, polynomial_ring, beta)
    if rank == 0:
        require(value.is_zero(), "rank-zero matrix is not zero")
        return {
            "rank": 0,
            "maximal_minor_gcd": "0",
            "gcd_factors": [],
            "entry_denominator_max_b_exponent": denominator_exponent,
            "nonzero_minor_witness": None,
            "minors_examined": 0,
        }
    gcd_value = polynomial_ring.zero()
    witness = None
    examined = 0
    stop = False
    for rows in combinations(range(4), rank):
        for columns in combinations(range(4), rank):
            determinant = value.matrix_from_rows_and_columns(rows, columns).det()
            examined += 1
            if determinant == 0:
                continue
            denominator_b_exponent(determinant, polynomial_ring, beta)
            numerator = polynomial_ring(determinant.numerator())
            if witness is None:
                witness = {
                    "rows": list(rows),
                    "columns": list(columns),
                    "numerator": str(numerator),
                    "denominator": str(polynomial_ring(determinant.denominator())),
                }
            gcd_value = numerator if gcd_value == 0 else gcd(gcd_value, numerator)
            if gcd_value == 1:
                stop = True
                break
        if stop:
            break
    require(witness is not None, "positive generic rank has no nonzero maximal minor")
    gcd_value = gcd_value.monic()
    return {
        "rank": rank,
        "maximal_minor_gcd": str(gcd_value),
        "gcd_factors": factor_list(gcd_value),
        "entry_denominator_max_b_exponent": denominator_exponent,
        "nonzero_minor_witness": witness,
        "minors_examined": examined,
    }


def summarize_rank_records(records, permitted_irreducibles):
    rank_counts = Counter(record["rank"] for record in records)
    exception_records = []
    irreducible_label_counts = Counter()
    irreducible_exponent_totals = Counter()
    maximum_denominator_exponent = 0
    for record in records:
        maximum_denominator_exponent = max(maximum_denominator_exponent, record["entry_denominator_max_b_exponent"])
        factors = record["gcd_factors"]
        for factor, exponent in factors:
            require(factor in permitted_irreducibles, "uncovered exceptional irreducible %s" % factor)
            irreducible_label_counts[factor] += 1
            irreducible_exponent_totals[factor] += exponent
        if factors:
            exception_records.append(record)
    digest, count = digest_records(records)
    return {
        "record_count": count,
        "records_sha256": digest,
        "generic_rank_counts": {str(rank): int(rank_counts[rank]) for rank in sorted(rank_counts)},
        "exception_label_count": len(exception_records),
        "irreducible_label_counts": {factor: int(irreducible_label_counts[factor]) for factor in sorted(irreducible_label_counts)},
        "irreducible_exponent_totals": {factor: int(irreducible_exponent_totals[factor]) for factor in sorted(irreducible_exponent_totals)},
        "entry_denominator_max_b_exponent": int(maximum_denominator_exponent),
        "exceptions": exception_records,
    }


def graph_from_terms(terms, orientation):
    oriented = [orient_term(term, orientation) for term in terms]
    vertices = [tuple(int(factor.rank()) for factor in term) for term in oriented]
    edges = {}
    for i, (u, v, w) in enumerate(oriented):
        for j, (u2, v2, w2) in enumerate(oriented):
            edges[i, j] = (int((u * v2).rank()), int((v * w2).rank()), int((w * u2).rank()))
    return vertices, edges


def certify_symbolic_strata(base_terms, generic_terms, polynomial_ring, beta):
    factor_output = {}
    edge_output = {}
    generic_graphs = {}
    base_graphs = {}
    all_factor_records = []
    all_edge_records = []
    for orientation in ORIENTATIONS:
        oriented_generic = [orient_term(term, orientation) for term in generic_terms]
        factor_records = []
        vertices = []
        for term_index, term in enumerate(oriented_generic):
            ranks = []
            for leg, value in enumerate(term):
                certificate = maximal_minor_certificate(value, polynomial_ring, beta)
                record = {"orientation": orientation, "term": term_index, "leg": LEG_NAMES[leg], **certificate}
                factor_records.append(record)
                all_factor_records.append(record)
                ranks.append(certificate["rank"])
            vertices.append(tuple(ranks))
        factor_summary = summarize_rank_records(factor_records, {"b"})
        require(factor_summary["record_count"] == 147, "factor rank coverage is incomplete")
        factor_output[orientation] = factor_summary

        edges = {}
        edge_records = []
        for i, (u, v, w) in enumerate(oriented_generic):
            for j, (u2, v2, w2) in enumerate(oriented_generic):
                products = (u * v2, v * w2, w * u2)
                edge_ranks = []
                for component, value in enumerate(products):
                    certificate = maximal_minor_certificate(value, polynomial_ring, beta)
                    record = {
                        "orientation": orientation,
                        "source_term": i,
                        "target_term": j,
                        "component": ("UV", "VW", "WU")[component],
                        **certificate,
                    }
                    edge_records.append(record)
                    all_edge_records.append(record)
                    edge_ranks.append(certificate["rank"])
                edges[i, j] = tuple(edge_ranks)
        edge_summary = summarize_rank_records(edge_records, {"b", "b + 1"})
        require(edge_summary["record_count"] == 49 * 49 * 3, "edge rank coverage is incomplete")
        edge_output[orientation] = edge_summary
        generic_graphs["generic:" + orientation] = (vertices, edges)
        base_graph = graph_from_terms(base_terms, orientation)
        base_graphs["base:" + orientation] = base_graph
        base_factor_counts = Counter(rank for vertex in base_graph[0] for rank in vertex)
        base_edge_counts = Counter(rank for edge in base_graph[1].values() for rank in edge)
        factor_output[orientation]["base_rank_counts"] = {str(rank): int(base_factor_counts[rank]) for rank in sorted(base_factor_counts)}
        edge_output[orientation]["base_rank_counts"] = {str(rank): int(base_edge_counts[rank]) for rank in sorted(base_edge_counts)}

    factor_digest, factor_count = digest_records(all_factor_records)
    edge_digest, edge_count = digest_records(all_edge_records)
    require(factor_count == 6 * 49 * 3, "global factor rank coverage is incomplete")
    require(edge_count == 6 * 49 * 49 * 3, "global edge rank coverage is incomplete")
    observed_factor_irreducibles = sorted({factor for summary in factor_output.values() for factor in summary["irreducible_label_counts"]})
    observed_edge_irreducibles = sorted({factor for summary in edge_output.values() for factor in summary["irreducible_label_counts"]})
    require(observed_factor_irreducibles == ["b"], "factor exceptional-locus census changed")
    require(observed_edge_irreducibles == ["b", "b + 1"], "edge exceptional-locus census changed")
    for orientation in ORIENTATIONS:
        require(factor_output[orientation]["generic_rank_counts"] == {"1": 108, "2": 36, "4": 3}, "factor generic rank census changed")
        require(edge_output[orientation]["generic_rank_counts"] == {"0": 3064, "1": 3920, "2": 216, "4": 3}, "edge generic rank census changed")
        require(edge_output[orientation]["irreducible_label_counts"] == {"b": 57, "b + 1": 32}, "edge exceptional-factor census changed")
    graphs = {}
    graphs.update(base_graphs)
    graphs.update(generic_graphs)
    graph_serialization = []
    for key in sorted(graphs):
        vertices, edges = graphs[key]
        graph_serialization.append({
            "key": key,
            "vertices": [list(value) for value in vertices],
            "edges_row_major": [list(edges[i, j]) for i in range(49) for j in range(49)],
        })
    return {
        "factor": {
            "global_record_count": factor_count,
            "global_records_sha256": factor_digest,
            "observed_exception_irreducibles": observed_factor_irreducibles,
            "orientations": factor_output,
        },
        "directed_edge": {
            "global_record_count": edge_count,
            "global_records_sha256": edge_digest,
            "observed_exception_irreducibles": observed_edge_irreducibles,
            "orientations": edge_output,
        },
        "strata": [
            {"name": "base", "condition": "b = 1"},
            {"name": "generic", "condition": "b != 0 and b + 1 != 0"},
        ],
        "graphs_sha256": sha256(canonical_json_bytes(graph_serialization)).hexdigest(),
    }, graphs


def refine_graph_colors(graphs):
    keys = sorted(graphs)
    initial = {(key, i): graphs[key][0][i] for key in keys for i in range(49)}
    values = sorted(set(initial.values()))
    value_to_color = {value: i for i, value in enumerate(values)}
    colors = {(key, i): value_to_color[value] for (key, i), value in initial.items()}
    trace = []
    for iteration in range(50):
        histograms = {key: sorted(colors[key, i] for i in range(49)) for key in keys}
        trace.append({
            "iteration": iteration,
            "color_count": len(set(colors.values())),
            "histograms_sha256": sha256(canonical_json_bytes(histograms)).hexdigest(),
        })
        signatures = {}
        for key in keys:
            edges = graphs[key][1]
            for i in range(49):
                outgoing = tuple(sorted((edges[i, j], colors[key, j]) for j in range(49)))
                incoming = tuple(sorted((edges[j, i], colors[key, j]) for j in range(49)))
                signatures[key, i] = (colors[key, i], outgoing, incoming)
        values = sorted(set(signatures.values()))
        value_to_color = {value: i for i, value in enumerate(values)}
        new_colors = {(key, i): value_to_color[value] for (key, i), value in signatures.items()}
        if len(set(new_colors.values())) == len(set(colors.values())):
            colors = new_colors
            histograms = {key: sorted(colors[key, i] for i in range(49)) for key in keys}
            trace.append({
                "iteration": iteration + 1,
                "color_count": len(set(colors.values())),
                "histograms_sha256": sha256(canonical_json_bytes(histograms)).hexdigest(),
            })
            return colors, trace
        colors = new_colors
    raise RuntimeError("graph color refinement did not stabilize")


def compare_graphs(graphs, colors, source_key, target_key):
    source_histogram = sorted(colors[source_key, i] for i in range(49))
    target_histogram = sorted(colors[target_key, i] for i in range(49))
    output = {
        "source": source_key,
        "target": target_key,
        "stable_histograms_equal": source_histogram == target_histogram,
    }
    if source_histogram != target_histogram:
        source_counts = Counter(source_histogram)
        target_counts = Counter(target_histogram)
        discrepancies = sorted((color, source_counts[color], target_counts[color]) for color in set(source_counts) | set(target_counts) if source_counts[color] != target_counts[color])
        output["first_histogram_discrepancy"] = list(discrepancies[0])
        output["status"] = "rejected"
        output["reason"] = "stable color histogram mismatch"
        return output
    source_classes = {color: [i for i in range(49) if colors[source_key, i] == color] for color in set(source_histogram)}
    target_classes = {color: [i for i in range(49) if colors[target_key, i] == color] for color in set(target_histogram)}
    output["source_stable_class_sizes"] = sorted(len(indices) for indices in source_classes.values())
    output["target_stable_class_sizes"] = sorted(len(indices) for indices in target_classes.values())
    require(all(len(indices) == 1 for indices in source_classes.values()), "surviving source graph has a nonsingleton class")
    require(all(len(indices) == 1 for indices in target_classes.values()), "surviving target graph has a nonsingleton class")
    target_by_color = {colors[target_key, j]: j for j in range(49)}
    permutation = [target_by_color[colors[source_key, i]] for i in range(49)]
    source_vertices, source_edges = graphs[source_key]
    target_vertices, target_edges = graphs[target_key]
    vertex_verified = all(source_vertices[i] == target_vertices[permutation[i]] for i in range(49))
    edge_verified = all(source_edges[i, j] == target_edges[permutation[i], permutation[j]] for i in range(49) for j in range(49))
    require(vertex_verified and edge_verified, "stable-color permutation does not preserve the full graph")
    output.update({
        "status": "survived",
        "unique_permutation": permutation,
        "all_49_vertex_labels_verified": vertex_verified,
        "all_2401_directed_edge_labels_verified": edge_verified,
    })
    return output


def certify_graph_coverage(graphs):
    colors, trace = refine_graph_colors(graphs)
    require([entry["color_count"] for entry in trace] == [3, 368, 588, 588], "graph refinement trace changed")
    comparisons = []
    for target_stratum in ("base", "generic"):
        target_key = target_stratum + ":abc"
        for source_stratum in ("base", "generic"):
            for orientation in ORIENTATIONS:
                source_key = source_stratum + ":" + orientation
                comparisons.append(compare_graphs(graphs, colors, source_key, target_key))
    require(len(comparisons) == 24, "graph branch coverage is incomplete")
    survivors = [entry for entry in comparisons if entry["status"] == "survived"]
    expected_survivors = [("base:abc", "base:abc"), ("generic:abc", "generic:abc")]
    require([(entry["source"], entry["target"]) for entry in survivors] == expected_survivors, "unexpected graph branch survived or expected branch disappeared")
    identity = list(range(49))
    require(all(entry["unique_permutation"] == identity for entry in survivors), "surviving graph permutation is not identity")
    coverage = {
        "invariant": {
            "vertex_color": "(rank A_i, rank B_i, rank C_i)",
            "directed_edge_color": "(rank(A_i B_j), rank(B_i C_j), rank(C_i A_j))",
            "action_reason": "under coupled sandwiching each product is multiplied on the left and right by invertible matrices and by a nonzero scalar; a common term permutation is therefore a colored directed graph isomorphism",
        },
        "refinement_trace": trace,
        "branch_count": len(comparisons),
        "rejected_branch_count": len(comparisons) - len(survivors),
        "surviving_branch_count": len(survivors),
        "comparisons": comparisons,
    }
    return coverage, colors


def certify_symbolic_scheme_validity(graphs, colors, family_coordinates):
    strata = []
    for stratum in ("base", "generic"):
        key = stratum + ":abc"
        vertices, _edges = graphs[key]
        require(all(all(rank > 0 for rank in label) for label in vertices), "a factor vanishes on a parameter stratum")
        stable_colors = [colors[key, i] for i in range(49)]
        require(len(set(stable_colors)) == 49, "stable rank-graph colors do not separate all evaluated summands")
        strata.append({
            "stratum": "b=1" if stratum == "base" else "b!=0,1",
            "all_147_factor_matrices_nonzero": True,
            "all_49_evaluated_summands_nonzero": True,
            "all_49_evaluated_summands_pairwise_distinct": True,
            "all_49_stable_graph_colors_singleton": True,
        })
    require(family_coordinates["canonical_source_target_coordinates_checked"] == 4096, "source sum certificate is incomplete")
    require(family_coordinates["five_term_family_identity_coordinates_checked"] == 4096, "family sum certificate is incomplete")
    return {
        "definition_matched": "sumTensor=4x4 matrix-multiplication tensor; every evaluated term is nonzero; the map from 49 slots to evaluated tensors is injective",
        "scope": "every field extension K/F2 and every b in K^times",
        "sum_tensor": {
            "canonical_source_coordinates_checked": 4096,
            "rational_family_delta_coordinates_checked": 4096,
            "verified": True,
        },
        "term_nonzero_argument": "on both exhaustive Gm strata every one of the three factor matrices in every slot has positive rank; over a field their pure tensor is therefore nonzero",
        "pairwise_distinct_argument": "equality of two nonzero pure tensors makes their three factors projectively proportional; transposing those slots would then preserve every vertex and directed-edge rank label, contradicting their distinct stable graph colors",
        "strata": strata,
        "all_fibers_scheme_valid_equivalent": True,
        "formal_lean_theorem_claimed": False,
    }


def matrix_multiplication_tensor_vector(field):
    target = [field.zero() for _ in range(4096)]
    for a, b_index, c in product(range(4), repeat=3):
        x = 4 * a + b_index
        y = 4 * b_index + c
        z = 4 * c + a
        target[(x * 16 + y) * 16 + z] = field.one()
    return tuple(target)


def finite_field_encoding(value, degree):
    if degree == 1:
        return int(value)
    coefficients = [int(coefficient) for coefficient in value.polynomial().list()]
    coefficients.extend([0] * (degree - len(coefficients)))
    return sum(coefficient << i for i, coefficient in enumerate(coefficients))


def certify_declared_finite_fields(base_terms, family_spec):
    output = []
    for degree in DECLARED_FINITE_FIELD_DEGREES:
        if degree == 1:
            field = GF(2)
            modulus = None
        elif degree == 2:
            binary_polynomial_ring = PolynomialRing(GF(2), "x2")
            x2 = binary_polynomial_ring.gen()
            field = GF(4, "z2", modulus=x2 ** 2 + x2 + 1)
            modulus = str(field.modulus())
        else:
            raise RuntimeError("undeclared finite-field constructor")
        parameters = sorted((value for value in field if value != 0), key=lambda value: finite_field_encoding(value, degree))
        require(len(parameters) == field.cardinality() - 1, "Gm cardinality mismatch")
        target = matrix_multiplication_tensor_vector(field)
        fiber_records = []
        for beta_value in parameters:
            terms = construct_family(base_terms, field, beta_value, family_spec)
            total = [field.zero() for _ in range(4096)]
            evaluated_keys = set()
            for slot, term in enumerate(terms):
                entries = tuple(x * y * z for x in term[0].list() for y in term[1].list() for z in term[2].list())
                require(any(value != 0 for value in entries), "a declared finite-field fiber has a zero evaluated summand")
                key = tuple(finite_field_encoding(value, degree) for value in entries)
                require(key not in evaluated_keys, "a declared finite-field fiber has repeated evaluated summands")
                evaluated_keys.add(key)
                total = [left + right for left, right in zip(total, entries)]
            require(tuple(total) == target, "a declared finite-field fiber does not sum to matrix multiplication")
            require(len(evaluated_keys) == 49, "declared finite-field injectivity count mismatch")
            fiber_records.append({
                "parameter_integer_encoding": finite_field_encoding(beta_value, degree),
                "parameter_display": str(beta_value),
                "sum_coordinates_checked": 4096,
                "nonzero_evaluated_summands": 49,
                "distinct_evaluated_summands": 49,
                "scheme_valid_equivalent": True,
            })
        q = int(field.cardinality())
        output.append({
            "field": "F%d" % q,
            "construction": "prime field F2" if degree == 1 else "F4 with generator z2 satisfying z2^2+z2+1=0 (Sage modulus display: %s)" % modulus,
            "characteristic": 2,
            "cardinality": q,
            "parameter_space": "Gm(F%d)" % q,
            "parameter_encodings": [finite_field_encoding(value, degree) for value in parameters],
            "all_fibers_directly_checked": True,
            "fiber_records": fiber_records,
            "parameter_count": q - 1,
            "family_orbit_count": q - 1,
            "orbit_count_deduction": "R(F%d) is diagonal on this F%d-rational family, so its %d rational parameters give %d distinct family orbits" % (q, q, q - 1, q - 1),
            "rationality": "every factor is evaluated in F%d and each diagonal identity witness is defined over F2 inside F%d" % (q, q),
            "scope_exclusion": "this counts only orbits represented by the declared parameterized family, not all ambient rank-49 decompositions",
        })
    return {
        "declared_fields_only": [entry["field"] for entry in output],
        "all_declared_fibers_directly_scheme_valid_checked": True,
        "counts_use_pointwise_diagonal_correspondence_not_scheme_structure": True,
        "fields": output,
    }


def packed_binary_matrix_sha256(value):
    bits = [int(x) for x in value.list()]
    packed = bytearray((len(bits) + 7) // 8)
    for i, bit in enumerate(bits):
        packed[i // 8] |= bit << (i % 8)
    return sha256(bytes(packed)).hexdigest()


def pointwise_projective_system(vectors):
    field = vectors[0].base_ring()
    dimension = len(vectors[0])
    count = len(vectors)
    system = matrix(field, count * dimension, dimension * dimension + count)
    for i, value in enumerate(vectors):
        for row in range(dimension):
            for column in range(dimension):
                system[i * dimension + row, row * dimension + column] = value[column]
            system[i * dimension + row, dimension * dimension + i] = -value[row]
    return system


def certify_anchor(base_terms, generic_terms):
    field = GF(2)
    anchor_indices = [i for i in range(49) if i not in CHANGED_TERMS]
    require(len(anchor_indices) == 44, "anchor count mismatch")
    vectors = [vector(field, base_terms[i][0].list()) for i in anchor_indices]
    require(int(matrix(field, vectors).rank()) == 16, "U anchors do not span the factor space")
    for i in anchor_indices:
        require(generic_terms[i][0] == base_terms[i][0].change_ring(generic_terms[i][0].base_ring()), "U anchor varies symbolically")
    system = pointwise_projective_system(vectors)
    require((system.nrows(), system.ncols()) == (704, 300), "anchor system shape mismatch")
    pivot_columns = list(system.pivots())
    rank = len(pivot_columns)
    require(rank == 299, "anchor system rank is not 299")
    column_basis = system.matrix_from_columns(pivot_columns)
    pivot_rows = list(column_basis.transpose().pivots())
    require(len(pivot_rows) == 299, "failed to select 299 independent anchor equations")
    witness_minor = system.matrix_from_rows_and_columns(pivot_rows, pivot_columns)
    witness_determinant = witness_minor.det()
    require(witness_determinant == 1, "rank-299 witness minor is singular")
    identity_vector = vector(field, identity_matrix(field, 16).list() + [1] * 44)
    require(system * identity_vector == 0, "scalar identity is not in the anchor kernel")
    require(system.ncols() - rank == 1, "anchor kernel is not one-dimensional")
    return {
        "leg": "U",
        "anchor_term_indices": anchor_indices,
        "anchor_count": 44,
        "anchor_span_dimension": 16,
        "unknown_order": "256 row-major entries of L followed by c_i in anchor_term_indices order",
        "equations": "L v_i = c_i v_i",
        "matrix_shape": [704, 300],
        "matrix_rank_over_F2": rank,
        "matrix_sha256_little_endian_row_major_bits": packed_binary_matrix_sha256(system),
        "rank_299_minor": {
            "rows": pivot_rows,
            "columns": pivot_columns,
            "determinant_in_F2": int(witness_determinant),
        },
        "kernel_dimension": 1,
        "kernel_generator": {
            "L": [[int(x) for x in row] for row in identity_matrix(field, 16).rows()],
            "c": [1] * 44,
        },
        "scalar_extension_reason": "the coefficient matrix is over F2 and the displayed 299 by 299 minor has determinant 1; hence its rank remains 299 and its kernel remains the scalar-identity line over every field extension",
    }


def certify_parameter_separator(base_terms, generic_terms, polynomial_ring, beta):
    field = generic_terms[0][0].base_ring()
    u_b_binary = mask_matrix(GF(2), "9990")
    u_d_binary = mask_matrix(GF(2), "0500")
    require(base_terms[14][0] == u_b_binary, "U_b mask is not source term 14 U")
    require(base_terms[37][0] == u_d_binary, "U_d mask is not source term 37 U")
    require(base_terms[42][0] == u_b_binary + u_d_binary, "base term 42 U does not equal U_b+U_d")
    u_b = u_b_binary.change_ring(field)
    u_d = u_d_binary.change_ring(field)
    require(generic_terms[42][0] == u_b + (field(1) / beta) * u_d, "moving U_42 equation failed")
    independent_matrix = matrix(GF(2), [vector(GF(2), u_b_binary.list()), vector(GF(2), u_d_binary.list())]).transpose()
    require(independent_matrix.rank() == 2, "U_b and U_d are dependent")
    coordinate_rows = [4, 10]
    independent_minor = independent_matrix.matrix_from_rows_and_columns(coordinate_rows, [0, 1])
    require(independent_minor.det() == 1, "displayed U_b,U_d independence minor failed")
    separator_ring = PolynomialRing(GF(2), names=("b", "bp", "mu"))
    b0, bp0, mu = separator_ring.gens()
    ub_coefficient_equation = mu + 1
    ud_coefficient_equation_cleared = b0 + mu * bp0
    conclusion = b0 + bp0
    ideal_combination = ud_coefficient_equation_cleared + bp0 * ub_coefficient_equation
    require(ideal_combination == conclusion, "parameter-separator ideal identity failed")
    return {
        "moving_term": 42,
        "leg": "U",
        "equation": "U_42(b) = U_b + b^-1 U_d",
        "U_b": {"mask": "9990", "source_term": 14},
        "U_d": {"mask": "0500", "source_term": 37},
        "independence_rank": 2,
        "independence_minor": {"coordinate_rows": coordinate_rows, "columns": [0, 1], "determinant_in_F2": 1},
        "projective_equation_convention": "U_42(bp) = mu U_42(b)",
        "coefficient_equations_after_clearing_nonzero_b_bp": ["mu + 1", "b + mu*bp"],
        "conclusion_equation": "b + bp",
        "ideal_membership_certificate": "b + bp = (b + mu*bp) + bp*(mu + 1) in F2[b,bp,mu]",
        "consequence": "for nonzero b,bp in any field extension of F2, projective equality of the moving U factor forces bp=b",
    }


def nested_matrix(value):
    return [[int(x) for x in row] for row in value.rows()]


def certify_diagonal_witness(generic_terms):
    field = generic_terms[0][0].base_ring()
    identity4 = identity_matrix(field, 4)
    inverse4 = identity4.inverse()
    require(identity4 * inverse4 == identity4 and inverse4 * identity4 == identity4, "identity inverse check failed")
    permutation = list(range(49))
    gauges = []
    equations = []
    for i, term in enumerate(generic_terms):
        a = b = c = field.one()
        require(a * b * c == 1, "diagonal gauge product failed")
        oriented = orient_term(term, "abc")
        mapped = (
            a * identity4 * oriented[0] * inverse4,
            b * identity4 * oriented[1] * inverse4,
            c * identity4 * oriented[2] * inverse4,
        )
        target = generic_terms[permutation[i]]
        checks = [mapped[leg] == target[leg] for leg in range(3)]
        require(all(checks), "diagonal mapped-factor equation failed at term %d" % i)
        gauges.append({"term": i, "a": 1, "b": 1, "c": 1, "product": 1})
        equations.append({
            "source_term": i,
            "target_term": permutation[i],
            "U": "U_%d(b) = 1*I4*U_%d(b)*I4" % (i, i),
            "V": "V_%d(b) = 1*I4*V_%d(b)*I4" % (i, i),
            "W": "W_%d(b) = 1*I4*W_%d(b)*I4" % (i, i),
            "verified": checks,
        })
    require(len(equations) == 49, "diagonal equation coverage failed")
    binary_identity = identity_matrix(GF(2), 4)
    return {
        "defined_over": "F2 (and hence over every K/F2)",
        "orientation": "abc",
        "P": nested_matrix(binary_identity),
        "Q": nested_matrix(binary_identity),
        "R": nested_matrix(binary_identity),
        "P_inverse": nested_matrix(binary_identity),
        "Q_inverse": nested_matrix(binary_identity),
        "R_inverse": nested_matrix(binary_identity),
        "inverse_equations_verified": ["P*P_inverse=I4", "Q*Q_inverse=I4", "R*R_inverse=I4"],
        "source_to_target_permutation": permutation,
        "gauges": gauges,
        "mapped_factor_equations": equations,
        "mapped_factor_equation_count": len(equations),
        "verified_over": "F2(b)",
    }


def build_artifact():
    base_terms = parse_source()
    family_spec = encoded_family_specification()
    polynomial_ring = PolynomialRing(GF(2), "b")
    beta = polynomial_ring.gen()
    function_field = FractionField(polynomial_ring)
    generic_terms = construct_family(base_terms, function_field, function_field(beta), family_spec)
    family_coordinates = verify_family(base_terms, generic_terms, polynomial_ring, beta)
    strata, graphs = certify_symbolic_strata(base_terms, generic_terms, polynomial_ring, beta)
    graph_coverage, graph_colors = certify_graph_coverage(graphs)
    scheme_validity = certify_symbolic_scheme_validity(graphs, graph_colors, family_coordinates)
    anchor = certify_anchor(base_terms, generic_terms)
    separator = certify_parameter_separator(base_terms, generic_terms, polynomial_ring, function_field(beta))
    diagonal_witness = certify_diagonal_witness(generic_terms)
    declared_finite_fields = certify_declared_finite_fields(base_terms, family_spec)
    checker_relative = str(SCRIPT_PATH.relative_to(REPOSITORY_ROOT))
    artifact_relative = str(ARTIFACT_PATH.relative_to(REPOSITORY_ROOT))
    source_fixture_relative = str(SOURCE_PATH.relative_to(REPOSITORY_ROOT))
    family_summary = {
        "construction": "vendored canonical binary tensor fixture plus the authenticated T3 update table encoded in the checker; neither the original external source locator nor a family-certificate file is opened",
        "parameter_change": "t=b+1, s=t/(1+t)=(b+1)/b",
        "domain": "b != 0",
        "indexing": "zero-based terms; bit e=4*row+column of a 16-bit mask",
        "changed_terms_zero_based": list(CHANGED_TERMS),
        "encoded_t3_updates_sha256": ENCODED_T3_UPDATES_SHA256,
        "s_part": family_spec["s_part"],
        "t_part": family_spec["t_part"],
        "specialization_at_b_1_equals_source": True,
        "canonical_source_target_coordinates_checked": family_coordinates["canonical_source_target_coordinates_checked"],
        "five_term_tensor_identity_coordinates_checked": family_coordinates["five_term_family_identity_coordinates_checked"],
        "all_44_other_terms_symbolically_fixed": True,
    }
    return {
        "schema": "rank49-t4-parameter-orbits-v2",
        "provenance": {
            "base_git_revision": BASE_GIT_REVISION,
            "base_revision_role": "repository revision from which this unstaged acceptance artifact was generated; the checker does not query git",
            "checker": checker_relative,
            "checker_sha256": file_sha256(SCRIPT_PATH),
            "checker_hash_scope": "exact script bytes executed",
            "artifact": artifact_relative,
            "canonical_source_fixture": source_fixture_relative,
            "canonical_source_fixture_relative_to_checker": str(SOURCE_FIXTURE_RELATIVE_TO_SCRIPT),
            "canonical_source_fixture_resolution": "resolve checker path, then join its directory with canonical_source_fixture_relative_to_checker",
            "canonical_source_fixture_sha256": SOURCE_SHA256,
            "original_external_source_locator": ORIGINAL_EXTERNAL_SOURCE_LOCATOR,
            "original_external_source_locator_role": "provenance only; represented as a string and never opened",
            "original_external_source_runtime_dependency": False,
            "runtime_file_inputs": [source_fixture_relative],
            "encoded_t3_updates_sha256": ENCODED_T3_UPDATES_SHA256,
            "t3_lean_provenance": T3_LEAN_PROVENANCE_PATH,
            "t3_lean_provenance_sha256": T3_LEAN_PROVENANCE_SHA256,
            "historical_poc_certificate_sha256": HISTORICAL_T3_CERTIFICATE_SHA256,
            "historical_poc_certificate_role": "hash-only provenance; no path is opened and no certificate content is used at runtime",
            "historical_poc_certificate_runtime_dependency": False,
            "sage_version": str(SAGE_VERSION),
            "python_version": platform.python_version(),
            "working_directory": "repository root containing the recorded checker-relative paths",
            "write_command": "sage %s -- --write" % checker_relative,
            "check_command": "sage %s -- --check" % checker_relative,
            "acceptance_check_command": "/usr/bin/time -v timeout 60 sage %s -- --check" % checker_relative,
            "time_limit_seconds": 60,
            "memory_limit": "no explicit memory limit; measured RSS is reported by the acceptance command, not embedded dynamically",
            "random_seeds": [],
            "randomness": "none",
            "fields": ["F2", "F2[b]", "F2(b)", "F4 with generator z2 and z2^2+z2+1=0"],
            "solver_status": "no solver; exact deterministic exhaustive assertions",
            "completion_status": "complete",
            "completion_basis": "all deterministic construction assertions passed before artifact serialization; check mode additionally requires exact artifact equality and exit status 0",
            "artifact_write": "UTF-8 canonical pretty JSON written to a same-directory temporary file, fsynced, chmod 0644, then atomically replaced and parent-directory fsynced",
        },
        "action_scope": {
            "source_orientation_then_sandwich": "(A_i,B_i,C_i) maps to (P A_i Q^-1, Q B_i R^-1, R C_i P^-1)",
            "orientations": {orientation: list(ORIENTATION_FORMULAS[orientation]) for orientation in ORIENTATIONS},
            "term_action": "one common permutation of 49 terms",
            "gauges": "three nonzero scalars per term with product one",
            "negative_certificate_strength": "the rank graph permits arbitrary nonzero factor gauges, and the anchor system permits arbitrary GL16 factor maps; both are superclasses of the stated action",
        },
        "canonical_family": family_summary,
        "scheme_valid_equivalent": scheme_validity,
        "declared_finite_field_family_orbits": declared_finite_fields,
        "symbolic_rank_strata": strata,
        "graph_branch_coverage": graph_coverage,
        "anchor_projective_stabilizer": anchor,
        "parameter_separator": separator,
        "positive_diagonal_witness": diagonal_witness,
        "result": {
            "pointwise_rational_correspondence": "For every field extension K/F2, R(K)={(b,b): b in K^times} for the action_scope encoded here.",
            "forward_direction": "the explicit identity witness is defined over F2 and verifies all 49 mapped-factor equations over F2(b)",
            "reverse_direction": "symbolic rank strata cover b=1 and b!=0,1; all 24 stratum/orientation cells are rejected except same-stratum abc with identity permutation; the fixed-anchor scalar-kernel certificate and moving-factor equation then force b'=b",
            "fiber_validity": "the exact sum, nonzero evaluated summands, and injective evaluated-term map are certified for every b in Gm over every field extension; every F2 and F4 fiber is additionally evaluated directly",
            "rational_function_scope": "the universal positive witness is rational over F2(b); the negative argument is pointwise over arbitrary fields and does not assert a scheme-theoretic ideal for a possibly nonreduced witness scheme",
            "pointwise_vs_scheme_correspondence": "Scheme.Valid-equivalent properties are proved fiberwise, but the witness correspondence is certified only as a functor of field-valued points; its scheme structure and nilpotents are not computed",
            "geometric_scope": "after base change to an algebraic closure, the set of geometric parameter pairs admitting a witness is the diagonal set; no nonreduced scheme-structure claim is made",
            "extension_and_descent": "an unequal pair over K cannot acquire a witness after any field extension, because the same certificates apply over that extension; diagonal witnesses already descend to F2",
            "finite_field_orbit_scope": "the recorded q-1 counts apply only to the F2- and F4-rational fibers of this parameterized family, with rational identity witnesses; they are not counts of all ambient decompositions",
            "complete_pointwise_branches_within_action_scope": True,
            "unknown_pointwise_branches_within_action_scope": [],
            "not_claimed": [
                "scheme-theoretic or nonreduced structure of the witness correspondence",
                "orbit counts outside the explicitly declared F2 and F4 parameterized families",
                "a count of all ambient rank-49 decomposition orbits",
                "equivalence under transformations outside action_scope",
                "a formal Lean Scheme.Valid theorem or a minimal-rank assertion",
            ],
        },
    }


def atomic_write_text(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(prefix=path.name + ".", suffix=".tmp", dir=str(path.parent))
    try:
        os.fchmod(descriptor, 0o644)
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as output:
            output.write(text)
            output.flush()
            os.fsync(output.fileno())
        os.replace(temporary_name, path)
        directory_descriptor = os.open(str(path.parent), os.O_RDONLY)
        try:
            os.fsync(directory_descriptor)
        finally:
            os.close(directory_descriptor)
    finally:
        if os.path.exists(temporary_name):
            os.unlink(temporary_name)


def first_difference(left, right, path="root"):
    if type(left) is not type(right):
        return "%s: type %s != %s" % (path, type(left).__name__, type(right).__name__)
    if isinstance(left, dict):
        if set(left) != set(right):
            return "%s: key sets differ" % path
        for key in sorted(left):
            difference = first_difference(left[key], right[key], path + "." + str(key))
            if difference:
                return difference
        return None
    if isinstance(left, list):
        if len(left) != len(right):
            return "%s: lengths %d != %d" % (path, len(left), len(right))
        for i, (x, y) in enumerate(zip(left, right)):
            difference = first_difference(x, y, "%s[%d]" % (path, i))
            if difference:
                return difference
        return None
    if left != right:
        return "%s: %r != %r" % (path, left, right)
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true", help="compute and write the canonical artifact")
    mode.add_argument("--check", action="store_true", help="recompute and compare with the checked-in artifact")
    arguments = parser.parse_args([argument for argument in sys.argv[1:] if argument != "--"])
    started = datetime.now(timezone.utc)
    computed = json.loads(canonical_json_bytes(build_artifact()).decode("ascii"))
    if arguments.write:
        atomic_write_text(ARTIFACT_PATH, json.dumps(computed, indent=2, sort_keys=True) + "\n")
        mode_name = "WRITE"
    else:
        require(ARTIFACT_PATH.is_file(), "artifact is missing")
        recorded = json.loads(ARTIFACT_PATH.read_text(encoding="utf-8"))
        difference = first_difference(recorded, computed)
        require(difference is None, "artifact replay mismatch: " + str(difference))
        mode_name = "CHECK"
    elapsed = (datetime.now(timezone.utc) - started).total_seconds()
    artifact_hash = file_sha256(ARTIFACT_PATH)
    print("parameter_orbits %s PASS" % mode_name)
    print("source_sha256=%s" % SOURCE_SHA256)
    print("checker_sha256=%s" % computed["provenance"]["checker_sha256"])
    print("artifact_sha256=%s" % artifact_hash)
    print("symbolic_factor_records=%d" % computed["symbolic_rank_strata"]["factor"]["global_record_count"])
    print("symbolic_edge_records=%d" % computed["symbolic_rank_strata"]["directed_edge"]["global_record_count"])
    print("graph_cells=%d rejected=%d survived=%d" % (
        computed["graph_branch_coverage"]["branch_count"],
        computed["graph_branch_coverage"]["rejected_branch_count"],
        computed["graph_branch_coverage"]["surviving_branch_count"],
    ))
    print("anchor_shape=704x300 anchor_rank=299 anchor_kernel_dimension=1")
    print("scheme_valid_equivalent=all Gm fibers; direct finite checks=F2,F4")
    print("declared_family_orbit_counts=F2:1,F4:3")
    print("result=R(K) is the diagonal for every field extension K/F2 within the encoded action scope")
    print("elapsed_seconds=%.3f" % elapsed)


main()
