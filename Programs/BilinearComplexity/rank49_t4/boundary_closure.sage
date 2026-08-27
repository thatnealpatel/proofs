#!/usr/bin/env sage
"""Bounded exact affine-boundary test for two committed paired-T3 moves."""

import argparse
import hashlib
import itertools
import json
import math
import operator
import resource
import signal
import sys
import time
from functools import lru_cache
from pathlib import Path

from sage.all import GF, PolynomialRing


SCRIPT_PATH = Path(sys.argv[0]).resolve()
SCRIPT_DIR = SCRIPT_PATH.parent
FIXTURE_PATH = SCRIPT_DIR / "fixtures" / "4x4x4_m49_c680_iteration65_Z2.txt"
SUPPORT_PATH = SCRIPT_DIR / "artifacts" / "support5_census.json"
FIXTURE_SHA256 = "5fc92a6bf83fc29d9527ab100bad5d72d769178b616b31a36c3c0c0b8ad9d09d"
SUPPORT_SHA256 = "1afc16b7db176e4a480fb3c06a5b6cfe104be974bef0c5af3f48ac4d0a4c78de"
ORIENTATION_ORDER = ("abc", "bca", "cab", "acb", "cba", "bac")
LEG_NAMES = "UVW"
STATUS_VALUES = ("proved", "refuted", "unknown")


class BoundExpired(Exception):
    pass


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha256_bytes(value):
    return hashlib.sha256(value).hexdigest()


def json_default(value):
    try:
        return int(value)
    except (TypeError, ValueError, OverflowError):
        raise TypeError("not JSON serializable: %r" % (value,))


def canonical_bytes(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True, default=json_default).encode("ascii")


def element_encoding(value, degree):
    if degree == 1:
        return int(value)
    coefficients = [int(coefficient) for coefficient in value.polynomial().list()]
    coefficients.extend([0] * (degree - len(coefficients)))
    return sum(coefficient << i for i, coefficient in enumerate(coefficients[:degree]))


def parse_inputs():
    fixture_raw = FIXTURE_PATH.read_bytes()
    support_raw = SUPPORT_PATH.read_bytes()
    require(sha256_bytes(fixture_raw) == FIXTURE_SHA256, "committed fixture hash mismatch")
    require(sha256_bytes(support_raw) == SUPPORT_SHA256, "committed support-five artifact hash mismatch")
    lines = fixture_raw.decode("ascii").splitlines()
    require(len(lines) == 4, "fixture must have four lines")
    require([int(entry) for entry in lines[0].split()] == [4, 4, 4, 49], "fixture header mismatch")
    rows = [[int(entry) for entry in line.split()] for line in lines[1:]]
    require(all(len(row) == 49 * 16 for row in rows), "fixture factor-row length mismatch")
    require(all(entry in (0, 1) for row in rows for entry in row), "fixture is not binary")
    terms = []
    for slot in range(49):
        terms.append(tuple(sum(rows[leg][16 * slot + bit] << bit for bit in range(16)) for leg in range(3)))
    artifact = json.loads(support_raw.decode("utf-8"))
    result = artifact["result"]
    require(result["schema"] == "rank49-t4-support5-census-v4", "support artifact schema mismatch")
    records = result["positive_normal_supports"]
    require(len(records) == 63, "committed paired-T3 move count mismatch")
    moves = []
    for record in records:
        certificate = record["paired_t3"]["canonical_oriented_factor_update_witness"]
        require(certificate is not None, "missing canonical paired-T3 witness")
        updates = certificate["separate_factor_updates_in_original_coordinate_frame"]
        move = {
            "support": tuple(int(slot) for slot in record["support0"]),
            "orientation": certificate["orientation"],
            "labels": tuple(int(slot) for slot in certificate["labels_abcde"]),
            "updates": updates,
        }
        require(set(updates) == {"s", "t"}, "paired-T3 update table mismatch")
        require(set(move["support"]) == set(move["labels"]), "paired-T3 labels do not cover support")
        moves.append(move)
    moves.sort(key=move_key)
    require(len({move_key(move) for move in moves}) == 63, "canonical paired-T3 moves are not unique")
    return terms, moves


def move_key(move):
    return (move["support"], ORIENTATION_ORDER.index(move["orientation"]), move["labels"])


@lru_cache(maxsize=None)
def outer3_mask(first, second, third):
    zero = int(0)
    one = int(1)
    width = int(16)
    output = zero
    for i in range(width):
        if not ((first >> i) & one):
            continue
        for j in range(width):
            if not ((second >> j) & one):
                continue
            prefix = (i * width + j) * width
            for k in range(width):
                if (third >> k) & one:
                    output = operator.xor(output, one << (prefix + k))
    return output


def add_laurent(output, exponent, value):
    if not value:
        return
    output[exponent] = operator.xor(output.get(exponent, int(0)), value)
    if output[exponent] == 0:
        del output[exponent]


def laurent_factor(base, slot, leg, move_axis):
    output = {(0, 0): base}
    for move, axis in move_axis:
        coefficients = {
            "s": ((0, 0), (-1, 0) if axis == 0 else (0, -1)),
            "t": ((0, 0), (1, 0) if axis == 0 else (0, 1)),
        }
        for kind in ("s", "t"):
            for update in move["updates"][kind]:
                if int(update["slot"]) == slot and LEG_NAMES.index(update["factor"]) == leg:
                    mask = int(update["add"], 16)
                    for exponent in coefficients[kind]:
                        add_laurent(output, exponent, mask)
    return output


def laurent_term(terms, slot, move_axis):
    factors = [laurent_factor(terms[slot][leg], slot, leg, move_axis) for leg in range(3)]
    output = {}
    for exponent0, first in factors[0].items():
        for exponent1, second in factors[1].items():
            for exponent2, third in factors[2].items():
                exponent = (
                    exponent0[0] + exponent1[0] + exponent2[0],
                    exponent0[1] + exponent1[1] + exponent2[1],
                )
                add_laurent(output, exponent, outer3_mask(first, second, third))
    return output


def laurent_residual(terms, first, second=None):
    if second is None:
        output = {}
        for slot in first["support"]:
            for exponent, value in laurent_term(terms, slot, [(first, 0)]).items():
                add_laurent(output, exponent, value)
            add_laurent(output, (0, 0), outer3_mask(*terms[slot]))
        return output
    output = {}
    intersection = sorted(set(first["support"]) & set(second["support"]))
    for slot in intersection:
        for move_axis in ([(first, 0), (second, 1)], [(first, 0)], [(second, 1)]):
            for exponent, value in laurent_term(terms, slot, move_axis).items():
                add_laurent(output, exponent, value)
        add_laurent(output, (0, 0), outer3_mask(*terms[slot]))
    return output


def select_canonical_pair(terms, moves):
    individual_failures = []
    for move in moves:
        if laurent_residual(terms, move):
            individual_failures.append(move_key(move))
    require(not individual_failures, "a committed canonical move failed exact Laurent replay")
    compatible = []
    overlap_histogram = {}
    overlapping_pairs = 0
    for first, second in itertools.combinations(moves, 2):
        intersection = tuple(sorted(set(first["support"]) & set(second["support"])))
        if not intersection:
            continue
        overlapping_pairs += 1
        overlap_histogram[len(intersection)] = overlap_histogram.get(len(intersection), 0) + 1
        if not laurent_residual(terms, first, second):
            compatible.append((first, second, intersection))
    require(compatible, "no compatible overlapping committed pair exists")
    first, second, intersection = compatible[0]
    require(first["support"] == (0, 7, 23, 39, 45), "canonical first support changed")
    require(second["support"] == (7, 23, 32, 35, 45), "canonical second support changed")
    return first, second, {
        "selection_rule": "lexicographically first pair by (support, orientation order, labels) among overlapping committed canonical moves whose simultaneous two-variable Laurent tensor residual is identically zero",
        "committed_move_count": len(moves),
        "individual_moves_exactly_replayed": len(moves),
        "overlapping_pairs_exactly_tested": overlapping_pairs,
        "overlap_size_histogram": {str(key): overlap_histogram[key] for key in sorted(overlap_histogram)},
        "compatible_pair_count": len(compatible),
        "selected_intersection": list(intersection),
        "selected_union": sorted(set(first["support"]) | set(second["support"])),
    }


def move_json(move, parameter):
    return {
        "support0": list(move["support"]),
        "orientation": move["orientation"],
        "labels_abcde": list(move["labels"]),
        "parameter": parameter,
        "substitution": {"s": "1+%si" % parameter, "t": "1+%s" % parameter},
        "updates_in_original_coordinate_frame": move["updates"],
    }


def target_mask():
    output = int(0)
    for row in range(4):
        for middle in range(4):
            for column in range(4):
                first = 4 * row + middle
                second = 4 * middle + column
                third = 4 * column + row
                output = operator.xor(output, int(1) << ((first * 16 + second) * 16 + third))
    return output


def build_polynomial_family(terms, first_move, second_move):
    ring = PolynomialRing(GF(2), names=("b", "bi", "c", "ci"), order="degrevlex")
    b, bi, c, ci = ring.gens()
    move_data = ((first_move, b, bi), (second_move, c, ci))

    def factor(slot, leg):
        entries = [ring((terms[slot][leg] >> bit) & 1) for bit in range(16)]
        for move, parameter, inverse in move_data:
            coefficients = {"s": ring.one() + inverse, "t": ring.one() + parameter}
            for kind in ("s", "t"):
                for update in move["updates"][kind]:
                    if int(update["slot"]) == slot and LEG_NAMES.index(update["factor"]) == leg:
                        mask = int(update["add"], 16)
                        for bit in range(16):
                            if (mask >> bit) & 1:
                                entries[bit] += coefficients[kind]
        return tuple(entries)

    factors = []
    evaluated = []
    for slot in range(49):
        triple = tuple(factor(slot, leg) for leg in range(3))
        factors.append(triple)
        evaluated.append(tuple(x * y * z for x in triple[0] for y in triple[1] for z in triple[2]))
    equations = (b * bi + 1, c * ci + 1)
    ideal = ring.ideal(equations)
    require(ideal.dimension() == 2, "torus inverse-variable ideal has wrong dimension")
    target = target_mask()
    base_sum = int(0)
    for term in terms:
        base_sum = operator.xor(base_sum, outer3_mask(*term))
    require(base_sum == target, "fixture does not sum to the matrix-multiplication tensor")
    for coordinate in range(4096):
        total = sum((evaluated[slot][coordinate] for slot in range(49)), ring.zero())
        expected = ring((target >> coordinate) & 1)
        require(ideal.reduce(total + expected) == 0, "combined evaluated-term Laurent family is not tensor-constant modulo the torus equations")
    return ring, equations, factors, evaluated


def coordinate_label(slot, coordinate):
    return {
        "slot": slot,
        "factor_vector_coordinates": [coordinate // 256, (coordinate // 16) % 16, coordinate % 16],
    }


def recovery_certificates(ring, evaluated, varying_slots):
    coordinate_records = []
    monomials = set()
    for slot in varying_slots:
        for coordinate, polynomial in enumerate(evaluated[slot]):
            if polynomial == 0:
                continue
            support = {tuple(int(value) for value in exponent) for exponent in polynomial.dict()}
            coordinate_records.append((slot, coordinate, support, polynomial))
            monomials.update(support)
    ordered_monomials = sorted(monomials)
    monomial_index = {monomial: index for index, monomial in enumerate(ordered_monomials)}
    basis = {}
    for slot, coordinate, support, _polynomial in coordinate_records:
        vector = sum(int(1) << monomial_index[monomial] for monomial in support)
        witness = frozenset({(slot, coordinate)})
        while vector:
            pivot = vector.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = (vector, witness)
                break
            vector = operator.xor(vector, basis[pivot][0])
            witness = witness.symmetric_difference(basis[pivot][1])
    targets = (("1", ring.one()), ("b", ring.gen(0)), ("bi", ring.gen(1)), ("c", ring.gen(2)), ("ci", ring.gen(3)))
    output = {}
    for name, target in targets:
        target_support = {tuple(int(value) for value in exponent) for exponent in target.dict()}
        require(len(target_support) == 1, "recovery target is not a monomial")
        vector = int(1) << monomial_index[next(iter(target_support))]
        witness = frozenset()
        while vector:
            pivot = vector.bit_length() - 1
            require(pivot in basis, "evaluated coordinates do not recover %s" % name)
            vector = operator.xor(vector, basis[pivot][0])
            witness = witness.symmetric_difference(basis[pivot][1])
        recovered = sum((evaluated[slot][coordinate] for slot, coordinate in witness), ring.zero())
        require(recovered == target, "coordinate recovery identity failed for %s" % name)
        output[name] = {
            "xor_of_evaluated_term_coordinates": [coordinate_label(slot, coordinate) for slot, coordinate in sorted(witness)],
            "verified_as_polynomial_identity_before_quotient": True,
        }
    return {
        "varying_slots_used": list(varying_slots),
        "nonzero_evaluated_coordinates_examined": len(coordinate_records),
        "coordinate_function_linear_span_dimension": len(basis),
        "coordinate_function_monomials_in_b_bi_c_ci": [list(monomial) for monomial in ordered_monomials],
        "recoveries": output,
    }


def unique_generators(equations, constraints):
    raw = [polynomial for polynomial in itertools.chain(equations, constraints) if polynomial != 0]
    unique = {}
    for polynomial in raw:
        unique[str(polynomial)] = polynomial
    return raw, [unique[key] for key in sorted(unique)]


def make_cases(evaluated, varying_slots):
    varying = set(varying_slots)
    fixed = set(range(49)) - varying
    cases = []
    for first, second in itertools.combinations(varying_slots, 2):
        constraints = tuple(evaluated[first]) + tuple(evaluated[second])
        cases.append({
            "id": "zero_pair:%d:%d" % (first, second),
            "kind": "zero_pair",
            "slots": (first, second),
            "constraints": constraints,
            "parity_saving": "two zero evaluated terms can both be deleted, changing length 49 to at most 47",
        })
    for first, second in itertools.combinations(range(49), 2):
        if first in fixed and second in fixed:
            continue
        constraints = tuple(left + right for left, right in zip(evaluated[first], evaluated[second]))
        cases.append({
            "id": "collision:%d:%d" % (first, second),
            "kind": "collision",
            "slots": (first, second),
            "constraints": constraints,
            "parity_saving": "equal evaluated terms cancel in characteristic two and can both be deleted, changing length 49 to at most 47",
        })
    return cases, fixed


def finite_point_search(generators, max_degree, point_cap):
    points_examined = 0
    for degree in range(1, max_degree + 1):
        field = GF(2) if degree == 1 else GF(2 ** degree, name="z%d" % degree, modulus="conway")
        values = sorted((value for value in field if value != 0), key=lambda value: element_encoding(value, degree))
        field_points = len(values) ** 2
        if points_examined + field_points > point_cap:
            return None, points_examined, "residue_point_cap"
        for b_value in values:
            for c_value in values:
                points_examined += 1
                point = (b_value, b_value ** -1, c_value, c_value ** -1)
                if all(polynomial(*point) == 0 for polynomial in generators):
                    common_degree = next(
                        exponent for exponent in range(1, degree + 1)
                        if b_value ** (2 ** exponent) == b_value and c_value ** (2 ** exponent) == c_value)
                    return {
                        "field": field,
                        "ambient_degree": degree,
                        "residue_degree": common_degree,
                        "point": point,
                    }, points_examined, None
    return None, points_examined, "max_residue_degree"


def evaluate_polynomial_list(polynomials, point):
    return tuple(polynomial(*point) for polynomial in polynomials)


def shorter_decomposition(case, point_data, factors, evaluated, target):
    field = point_data["field"]
    degree = point_data["ambient_degree"]
    point = point_data["point"]
    term_values = [evaluate_polynomial_list(term, point) for term in evaluated]
    first, second = case["slots"]
    if case["kind"] == "zero_pair":
        require(not any(term_values[first]) and not any(term_values[second]), "zero-pair residue witness failed")
    else:
        require(term_values[first] == term_values[second], "collision residue witness failed")
    removed = {first, second}
    additionally_zero = [slot for slot in range(49) if slot not in removed and not any(term_values[slot])]
    removed.update(additionally_zero)
    retained = [slot for slot in range(49) if slot not in removed]
    total = [field.zero() for _ in range(4096)]
    for slot in retained:
        total = [left + right for left, right in zip(total, term_values[slot])]
    expected = [field((target >> coordinate) & 1) for coordinate in range(4096)]
    require(total == expected, "shorter decomposition does not sum to the target")
    require(len(retained) <= 47, "parity reduction did not save two terms")
    encoded_factors = []
    for slot in retained:
        triple = []
        for leg in range(3):
            values = evaluate_polynomial_list(factors[slot][leg], point)
            require(any(values), "retained pure tensor has a zero factor")
            triple.append([element_encoding(value, degree) for value in values])
        encoded_factors.append({"slot": slot, "factors": triple})
    return {
        "exists": True,
        "exact_length": len(retained),
        "retained_slots": retained,
        "additional_zero_slots_deleted": additionally_zero,
        "factor_encoding": "polynomial-basis integers in the displayed finite field, 16 row-major entries per factor",
        "encoded_factor_triples_sha256": sha256_bytes(canonical_bytes(encoded_factors)),
        "target_coordinates_exactly_checked": 4096,
        "sum_equals_4x4_matrix_multiplication_tensor": True,
    }


def solve_case(case, ring, equations, factors, evaluated, target, arguments):
    raw, generators = unique_generators(equations, case["constraints"])
    ideal = ring.ideal(generators)
    basis = tuple(ideal.groebner_basis())
    base = {
        "id": case["id"],
        "kind": case["kind"],
        "slots": list(case["slots"]),
        "parity_saving": case["parity_saving"],
        "ideal": {
            "ambient_ring": "F2[b,bi,c,ci]",
            "torus_equations": [str(equation) for equation in equations],
            "raw_nonzero_generator_count": len(raw),
            "distinct_generator_count": len(generators),
            "term_order": "degrevlex",
            "reduced_groebner_basis": [str(polynomial) for polynomial in basis[:32]],
            "groebner_basis_truncated": len(basis) > 32,
        },
    }
    if any(polynomial == 1 for polynomial in basis):
        base.update({
            "status": "refuted",
            "status_reason": "the exact torus-localized stratum ideal is the unit ideal",
            "residue_field": None,
            "exact_shorter_decomposition": {"exists": False, "reason": "empty affine-closure stratum"},
        })
        return base
    dimension = ideal.dimension()
    base["ideal"]["dimension"] = int(dimension)
    point_data, examined, search_stop = finite_point_search(generators, arguments.max_residue_degree, arguments.residue_point_cap)
    base["bounded_residue_search"] = {
        "maximum_extension_degree": arguments.max_residue_degree,
        "point_cap": arguments.residue_point_cap,
        "points_examined": examined,
        "stop_reason": search_stop,
    }
    if point_data is None:
        base.update({
            "status": "unknown",
            "status_reason": "the stratum ideal is proper, but no exact residue point was constructed within the declared bound",
            "residue_field": None,
            "exact_shorter_decomposition": {"exists": None, "reason": "no bounded exact residue witness"},
        })
        return base
    field = point_data["field"]
    degree = point_data["ambient_degree"]
    point = point_data["point"]
    base.update({
        "status": "proved",
        "status_reason": "an exact residue-field point and its parity-shortened target decomposition were directly verified",
        "residue_field": {
            "isomorphism_type": "GF(2^%d)" % point_data["residue_degree"],
            "residue_degree": point_data["residue_degree"],
            "evaluation_ambient_field": "GF(2^%d)" % degree,
            "evaluation_ambient_modulus": None if degree == 1 else str(field.modulus()),
            "parameter_order": ["b", "bi", "c", "ci"],
            "parameter_polynomial_basis_encodings": [element_encoding(value, degree) for value in point],
            "maximal_ideal_interpretation": "kernel of evaluation; its image is the finite field generated over F2 by b and c",
        },
        "exact_shorter_decomposition": shorter_decomposition(case, point_data, factors, evaluated, target),
    })
    return base


def unknown_case_result(case, reason, detail_reason, abort_remaining_strata=False, signal_failure_stage=None):
    result = {
        "id": case["id"],
        "kind": case["kind"],
        "slots": list(case["slots"]),
        "parity_saving": case["parity_saving"],
        "status": "unknown",
        "status_reason": reason,
        "residue_field": None,
        "exact_shorter_decomposition": {"exists": None, "reason": detail_reason},
    }
    if abort_remaining_strata:
        result["abort_remaining_strata"] = True
    if signal_failure_stage is not None:
        result["signal_failure_stage"] = signal_failure_stage
    return result


def inject_signal_failure(arguments, stage):
    if arguments.inject_signal_failure == stage and not arguments.signal_failure_injected:
        arguments.signal_failure_injected = True
        raise OSError("injected %s signal failure" % stage)


def run_bounded_case(case, ring, equations, factors, evaluated, target, arguments, seconds):
    duration = float(seconds)
    previous_handler = None
    handler_installed = False
    result = None
    cleanup_failures = []

    def expire(_signum, _frame):
        raise BoundExpired()

    try:
        try:
            previous_handler = signal.getsignal(signal.SIGALRM)
        except Exception as error:
            result = unknown_case_result(
                case,
                "signal timer setup failed at getsignal: %s" % error,
                "signal setup failure",
                True,
                "getsignal")
        if result is None:
            try:
                signal.signal(signal.SIGALRM, expire)
                handler_installed = True
            except Exception as error:
                result = unknown_case_result(
                    case,
                    "signal timer setup failed at handler installation: %s" % error,
                    "signal setup failure",
                    True,
                    "handler_installation")
        if result is None:
            try:
                inject_signal_failure(arguments, "setup")
                signal.setitimer(signal.ITIMER_REAL, max(duration, float(0.0)))
            except Exception as error:
                result = unknown_case_result(
                    case,
                    "signal timer setup failed at timer installation: %s" % error,
                    "signal setup failure",
                    False,
                    "timer_installation")
        if result is None:
            try:
                result = solve_case(case, ring, equations, factors, evaluated, target, arguments)
            except BoundExpired:
                result = unknown_case_result(
                    case,
                    "exact case wall-time bound expired; timeout is not refutation",
                    "timeout")
            except (MemoryError, ArithmeticError, RuntimeError, TypeError) as error:
                result = unknown_case_result(
                    case,
                    "exact case did not complete: %s" % error,
                    "resource or exact-computation failure")
    finally:
        if handler_installed:
            try:
                inject_signal_failure(arguments, "cancellation")
                signal.setitimer(signal.ITIMER_REAL, float(0.0))
            except Exception as error:
                cleanup_failures.append(("timer_cancellation", error))
                try:
                    signal.setitimer(signal.ITIMER_REAL, float(0.0))
                except Exception as retry_error:
                    cleanup_failures.append(("timer_cancellation_retry", retry_error))
            try:
                inject_signal_failure(arguments, "restoration")
                signal.signal(signal.SIGALRM, previous_handler)
            except Exception as error:
                cleanup_failures.append(("handler_restoration", error))
                try:
                    signal.signal(signal.SIGALRM, previous_handler)
                except Exception as retry_error:
                    cleanup_failures.append(("handler_restoration_retry", retry_error))
    if cleanup_failures:
        stages = ", ".join(stage for stage, _error in cleanup_failures)
        details = "; ".join("%s: %s" % (stage, error) for stage, error in cleanup_failures)
        result = unknown_case_result(
            case,
            "signal timer cleanup failed (%s); computed result discarded and remaining strata aborted" % details,
            "signal cleanup failure",
            True,
            stages)
    return result


def set_memory_limit(memory_mib):
    if memory_mib <= 0:
        return None
    requested = memory_mib * 1024 * 1024
    soft, hard = resource.getrlimit(resource.RLIMIT_AS)
    new_soft = requested if hard == resource.RLIM_INFINITY else min(requested, hard)
    resource.setrlimit(resource.RLIMIT_AS, (new_soft, hard))
    return memory_mib


def build_output(arguments):
    applied_memory_limit = set_memory_limit(arguments.memory_mib)
    terms, moves = parse_inputs()
    first, second, selection = select_canonical_pair(terms, moves)
    ring, equations, factors, evaluated = build_polynomial_family(terms, first, second)
    varying_slots = tuple(selection["selected_union"])
    recovery = recovery_certificates(ring, evaluated, varying_slots)
    cases, fixed_slots = make_cases(evaluated, varying_slots)
    all_case_ids = {case["id"] for case in cases}
    if arguments.case:
        missing = sorted(set(arguments.case) - all_case_ids)
        require(not missing, "unknown case id(s): %s" % ", ".join(missing))
        requested = set(arguments.case)
        cases = [case for case in cases if case["id"] in requested]
    if arguments.kind != "all":
        cases = [case for case in cases if case["kind"] == arguments.kind]
    selected_before_cap = len(cases)
    if arguments.max_strata:
        cases = cases[:arguments.max_strata]
    target = target_mask()
    deadline = float(time.monotonic()) + float(arguments.global_timeout)
    results = []
    for index, case in enumerate(cases):
        remaining = float(deadline - float(time.monotonic()))
        if remaining <= 0:
            for pending in cases[index:]:
                results.append({
                    "id": pending["id"],
                    "kind": pending["kind"],
                    "slots": list(pending["slots"]),
                    "parity_saving": pending["parity_saving"],
                    "status": "unknown",
                    "status_reason": "global wall-time bound expired before this case ran; timeout is not refutation",
                    "residue_field": None,
                    "exact_shorter_decomposition": {"exists": None, "reason": "global timeout"},
                })
            break
        result = run_bounded_case(
            case, ring, equations, factors, evaluated, target, arguments,
            float(min(float(arguments.case_timeout), remaining)))
        results.append(result)
        if result.get("abort_remaining_strata", False):
            for pending in cases[index + 1:]:
                results.append(unknown_case_result(
                    pending,
                    "execution aborted after a signal setup or cleanup failure left signal state potentially unsafe",
                    "unsafe signal state",
                    True,
                    "prior_case_abort"))
            break
    require(all(result["status"] in STATUS_VALUES for result in results), "invalid stratum status")
    status_counts = {status: sum(result["status"] == status for result in results) for status in STATUS_VALUES}
    fixed_tensors = {slot: outer3_mask(*terms[slot]) for slot in fixed_slots}
    require(all(value != 0 for value in fixed_tensors.values()), "a fixed evaluated term is zero")
    require(len(set(fixed_tensors.values())) == len(fixed_tensors), "two fixed evaluated terms collide")
    nontrivial_zero_pairs = math.comb(len(varying_slots), 2)
    nontrivial_collisions = math.comb(49, 2) - math.comb(len(fixed_slots), 2)
    complete_nontrivial_selection = (
        not arguments.case and arguments.kind == "all" and not arguments.max_strata
        and len(results) == nontrivial_zero_pairs + nontrivial_collisions)
    all_refuted = bool(results) and status_counts["refuted"] == len(results)
    route_status = "refuted" if complete_nontrivial_selection and all_refuted else "unknown"
    return {
        "schema": "rank49-t4-boundary-closure-v1",
        "status_semantics": {
            "proved": "the affine-closure stratum has an explicit exact residue-field point and the resulting length-at-most-47 decomposition was checked in all 4096 target coordinates",
            "refuted": "the exact torus-localized stratum ideal has reduced Groebner basis [1], so the stratum is empty in the affine closure",
            "unknown": "a declared bound or exact-computation limit was reached, or a proper ideal lacked a bounded explicit residue witness; timeout is never refutation",
        },
        "provenance": {
            "fixture": str(FIXTURE_PATH.relative_to(SCRIPT_DIR)),
            "fixture_sha256": FIXTURE_SHA256,
            "support5_artifact": str(SUPPORT_PATH.relative_to(SCRIPT_DIR)),
            "support5_artifact_sha256": SUPPORT_SHA256,
            "runtime_inputs": [str(FIXTURE_PATH.relative_to(SCRIPT_DIR)), str(SUPPORT_PATH.relative_to(SCRIPT_DIR))],
            "concurrent_authored_file_dependencies": [],
            "randomness": "none",
            "writes_files": False,
        },
        "canonical_compatible_pair": {
            **selection,
            "first_move": move_json(first, "b"),
            "second_move": move_json(second, "c"),
            "parameter_ring": "F2[b,bi,c,ci]/(b*bi+1,c*ci+1)",
            "evaluated_term_map": "49 ordered pure tensors, each with 4096 polynomial coordinates",
            "simultaneous_family_sum": "the 4096 coordinate polynomials equal the 4x4 matrix-multiplication tensor",
            "simultaneous_family_identity_verified": True,
        },
        "torus_image": {
            "source": "Spec F2[b,bi,c,ci]/(b*bi+1,c*ci+1) = Gm^2",
            "dimension": 2,
            "inverse_variables": {"bi": "b^-1", "ci": "c^-1"},
            "domain_is_prime_verified": True,
            "domain_is_prime_reason": "the quotient is explicitly the Laurent polynomial domain F2[b^+-1,c^+-1]",
            "meaning": "actual two-parameter fibers with both parameters units",
        },
        "affine_closure": {
            "method": "inverse-variable localization (equivalent to saturation by b*c), followed by exact coordinate-ring recovery and exact Groebner ideals for strata",
            "coordinate_recovery": recovery,
            "closed_immersion_argument": "the evaluated-coordinate subalgebra contains 1,b,bi,c,ci by the displayed polynomial identities, hence equals the Laurent source ring; the induced coordinate-ring map is surjective, so the torus map is a closed immersion",
            "affine_closure_equals_torus_image": True,
            "elimination_consequence": "intersecting an evaluated-term stratum with the affine closure is exactly its pullback ideal together with b*bi+1 and c*ci+1",
        },
        "projective_and_valuation_artifacts": {
            "part_of_affine_test": False,
            "finite_affine_monomial_valuation_cone": [[0, 0]],
            "reason": "recovered coordinates b and bi force val(b)>=0 and -val(b)>=0; recovered c and ci force the analogous inequalities, so every finite affine monomial valuation has val(b)=val(c)=0",
            "excluded_artifacts": "independently rescaling or projectivizing individual summands can hide Laurent poles, but such termwise limits are not points of the common affine evaluated-term closure and do not preserve the displayed affine tensor-sum identity without a separate exact construction",
            "b_zero_b_infinity_c_zero_c_infinity_are_torus_fibers": False,
        },
        "strata_scope": {
            "direct_parity_mechanisms": ["two evaluated terms are zero", "two evaluated terms collide and cancel in characteristic two"],
            "varying_slots": list(varying_slots),
            "fixed_slots": sorted(fixed_slots),
            "fixed_terms_directly_verified_nonzero": len(fixed_slots),
            "fixed_terms_directly_verified_pairwise_distinct": True,
            "nontrivial_zero_pair_ideals": nontrivial_zero_pairs,
            "zero_pair_strata_prefiltered_by_a_fixed_nonzero_term": math.comb(49, 2) - nontrivial_zero_pairs,
            "nontrivial_collision_ideals": nontrivial_collisions,
            "fixed_fixed_collision_strata_prefiltered_by_distinctness": math.comb(len(fixed_slots), 2),
            "selected_before_max_strata_cap": selected_before_cap,
            "tested_result_count": len(results),
            "complete_nontrivial_default_selection": complete_nontrivial_selection,
        },
        "bounds": {
            "per_case_wall_seconds": arguments.case_timeout,
            "global_wall_seconds": arguments.global_timeout,
            "address_space_memory_mib": applied_memory_limit,
            "maximum_residue_extension_degree": arguments.max_residue_degree,
            "residue_point_cap_per_case": arguments.residue_point_cap,
            "maximum_strata": arguments.max_strata or None,
            "signal_failure_injection": arguments.inject_signal_failure,
        },
        "strata": results,
        "summary": {
            "status_counts": status_counts,
            "canonical_pair_direct_parity_boundary_route_status": route_status,
            "established": (
                "For the selected canonical compatible pair, every nontrivial two-zero and collision stratum in its affine evaluated-term closure is empty."
                if route_status == "refuted" else
                "The bounded run does not decide every nontrivial direct-parity stratum for the selected pair."
            ),
            "global_rank49_to47_claim": "not decided; only one canonical compatible pair and direct zero/collision parity strata are tested",
            "residue_field_conclusion": "none exists for every refuted empty stratum; a proved stratum would display its exact finite residue field",
            "exact_shorter_decomposition_conclusion": "none exists on the tested direct-parity strata when the route status is refuted",
        },
    }


def parse_arguments():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", action="append", default=[], help="run one nontrivial case id, for example collision:0:7; repeatable")
    parser.add_argument("--kind", choices=("all", "zero_pair", "collision"), default="all")
    parser.add_argument("--max-strata", type=int, default=0, help="deterministically cap selected strata; zero means no cap")
    parser.add_argument("--case-timeout", type=float, default=5.0, help="wall seconds per exact stratum")
    parser.add_argument("--global-timeout", type=float, default=120.0, help="wall seconds for all exact strata after family construction")
    parser.add_argument("--memory-mib", type=int, default=0, help="optional RLIMIT_AS in MiB; zero leaves the inherited limit")
    parser.add_argument("--max-residue-degree", type=int, default=4, help="bounded positive-witness search through GF(2^d)")
    parser.add_argument("--residue-point-cap", type=int, default=65536, help="maximum finite parameter pairs examined per proper stratum ideal")
    parser.add_argument("--inject-signal-failure", choices=("setup", "cancellation", "restoration"), default=None, help=argparse.SUPPRESS)
    arguments = parser.parse_args([argument for argument in sys.argv[1:] if argument != "--"])
    arguments.max_strata = int(arguments.max_strata)
    arguments.case_timeout = float(arguments.case_timeout)
    arguments.global_timeout = float(arguments.global_timeout)
    arguments.memory_mib = int(arguments.memory_mib)
    arguments.max_residue_degree = int(arguments.max_residue_degree)
    arguments.residue_point_cap = int(arguments.residue_point_cap)
    arguments.signal_failure_injected = False
    require(arguments.max_strata >= 0, "max-strata must be nonnegative")
    require(arguments.case_timeout > 0, "case-timeout must be positive")
    require(arguments.global_timeout > 0, "global-timeout must be positive")
    require(arguments.memory_mib >= 0, "memory-mib must be nonnegative")
    require(arguments.max_residue_degree >= 1, "max-residue-degree must be positive")
    require(arguments.residue_point_cap >= 1, "residue-point-cap must be positive")
    return arguments


def main():
    try:
        output = build_output(parse_arguments())
        print(json.dumps(output, sort_keys=True, separators=(",", ":"), default=json_default))
    except Exception as error:
        failure = {
            "schema": "rank49-t4-boundary-closure-v1",
            "fatal_status": "unknown",
            "reason": "%s: %s" % (type(error).__name__, error),
            "timeout_is_refutation": False,
        }
        print(json.dumps(failure, sort_keys=True, separators=(",", ":"), default=json_default))
        raise SystemExit(1)


main()
