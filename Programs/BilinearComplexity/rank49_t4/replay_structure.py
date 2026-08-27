#!/usr/bin/env python3
"""Read-only exact GF(2) replay of post-T4 rank-49 structural claims."""

from __future__ import annotations

import sys

sys.dont_write_bytecode = True

import argparse
import copy
import functools
import hashlib
import itertools
import json
import math
import subprocess
from collections import Counter, defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

SCHEMA = "rank49-t4-structure-replay-v2"
CATALOG_SCOPE = "conditioned_on_authenticated_support5_census_positive_normal_supports"
CATALOG_BOUNDARY = "The 63-move list is consumed from the authenticated support5 census artifact. This replay checks that list and its deterministic representatives but does not regenerate the exhaustive five-support census, so catalog selection and completeness are conditional on that artifact."
HERE = Path(__file__).resolve().parent
REPOSITORY_ROOT = HERE.parents[2]
MANIFEST = HERE / "manifest.json"
EXPECTED_MANIFEST_SHA256 = "8736d8001178dacde576f7273e5c63eecccdd47f69d51762673228c83a9ffa82"
EXPECTED_MANIFEST_PAYLOAD_SHA256 = "5343a5371e3d9b643f36025b7c72e2a227e8f0221e8f8ffe1f43b58be8d2d258"
EXPECTED_BASE_REVISION = "6866f8be63692dc918e26d75db9414325b03b78c"
EXPECTED_INVENTORY = {
    "canonical_fixture": {
        "path": "Programs/BilinearComplexity/rank49_t4/fixtures/4x4x4_m49_c680_iteration65_Z2.txt",
        "bytes": 4716,
        "sha256": "5fc92a6bf83fc29d9527ab100bad5d72d769178b616b31a36c3c0c0b8ad9d09d",
    },
    "support5_census_script": {
        "path": "Programs/BilinearComplexity/rank49_t4/support5_census.py",
        "bytes": 93348,
        "sha256": "3af318d568bd76fabea18dcaa77fc12aaad9f2bf776ff48f0235c57756a23a2f",
    },
    "support5_census_artifact": {
        "path": "Programs/BilinearComplexity/rank49_t4/artifacts/support5_census.json",
        "bytes": 2171403,
        "sha256": "1afc16b7db176e4a480fb3c06a5b6cfe104be974bef0c5af3f48ac4d0a4c78de",
    },
    "generic_germ_script": {
        "path": "Programs/BilinearComplexity/rank49_t4/generic_germ.py",
        "bytes": 52098,
        "sha256": "4165af7a47cfba2dffe88c6501372fdadccc2d520dba4954f79f60e3bac91425",
    },
    "generic_germ_artifact": {
        "path": "Programs/BilinearComplexity/rank49_t4/artifacts/generic_germ.json",
        "bytes": 195551,
        "sha256": "fb2ed08df59a07c8b22df9481433cd4939ad9828e038ef3952198e62bb9e9d52",
    },
}
ORIENTATION_ORDER = ("abc", "bca", "cab", "acb", "cba", "bac")
ORIENTATION_MIDDLE_LEG = {
    "abc": "V",
    "bca": "W",
    "cab": "U",
    "acb": "V",
    "cba": "U",
    "bac": "W",
}
FACTOR_LEGS = "UVW"
RANK = 49
FACTOR_DIMENSION = 16
DOMAIN_DIMENSION = 3 * RANK * FACTOR_DIMENSION
TENSOR_DIMENSION = FACTOR_DIMENSION**3
EXPECTED = {
    "move_count": 63,
    "pair_count": 1953,
    "jacobian_rank": 2155,
    "kernel_dimension": 197,
    "gauge_generator_count": 146,
    "gauge_rank": 143,
    "normal_dimension": 54,
    "direction_rank": 63,
    "direction_gauge_intersection": 9,
    "block_count": 7,
    "moves_per_block": 9,
    "pole_circuit_occurrences": 126,
}


class ReplayFailure(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ReplayFailure(message)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def hash_file(path: Path) -> tuple[str, int]:
    digest = hashlib.sha256()
    size = 0
    with path.open("rb") as stream:
        while True:
            block = stream.read(1024 * 1024)
            if not block:
                break
            digest.update(block)
            size += len(block)
    return digest.hexdigest(), size


def run_git_read_only(*arguments: str, accepted: tuple[int, ...] = (0,)) -> tuple[int, str]:
    try:
        process = subprocess.run(
            ("git", "--no-replace-objects", "-C", str(REPOSITORY_ROOT), *arguments),
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
    except OSError as error:
        raise ReplayFailure(f"cannot execute read-only Git check: {error}") from error
    stdout = process.stdout.decode("utf-8", "replace").strip()
    stderr = process.stderr.decode("utf-8", "replace").strip()
    require(process.returncode in accepted, f"read-only Git {' '.join(arguments)} failed: {stderr or f'exit {process.returncode}'}")
    return process.returncode, stdout


def verify_base_revision_policy(revision: str) -> dict[str, Any]:
    _, object_type = run_git_read_only("cat-file", "-t", revision)
    require(object_type == "commit", "manifest base revision does not name a commit object")
    ancestor_status, _ = run_git_read_only("merge-base", "--is-ancestor", revision, "HEAD", accepted=(0, 1))
    require(ancestor_status == 0, "manifest base revision is not an ancestor of current HEAD")
    _, head = run_git_read_only("rev-parse", "--verify", "HEAD")
    require(len(head) == 40 and all(character in "0123456789abcdef" for character in head), "current Git HEAD is not a full commit id")
    return {
        "status": "PASS",
        "recorded_base_revision": revision,
        "object_type": object_type,
        "is_ancestor_of_checked_head": True,
        "checked_head": head,
        "method": "read-only git cat-file, merge-base --is-ancestor, and rev-parse with replacement objects disabled",
    }


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def canonical_pretty(value: Any) -> bytes:
    return (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=True) + "\n").encode("utf-8")


def reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def load_json(data: bytes, label: str) -> dict[str, Any]:
    try:
        value = json.loads(data.decode("utf-8"), object_pairs_hook=reject_duplicate_keys)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ReplayFailure(f"invalid JSON in {label}: {error}") from error
    require(isinstance(value, dict), f"{label} is not a JSON object")
    return value


def fixed_width_digest(values: Iterable[int], byte_width: int) -> str:
    digest = hashlib.sha256()
    for value in values:
        digest.update(value.to_bytes(byte_width, "little"))
    return digest.hexdigest()


def authenticate_inputs() -> tuple[dict[str, Any], dict[str, Any], bytes, dict[str, Any]]:
    manifest_raw = MANIFEST.read_bytes()
    require(sha256_bytes(manifest_raw) == EXPECTED_MANIFEST_SHA256, "manifest file SHA-256 mismatch")
    manifest = load_json(manifest_raw, str(MANIFEST))
    require(manifest_raw == canonical_pretty(manifest), "manifest is not canonical pretty JSON")
    require(manifest.get("schema") == "rank49-t4-integration-manifest-v2", "manifest schema mismatch")
    authentication = manifest.get("authentication")
    require(isinstance(authentication, dict), "manifest authentication is absent")
    require(authentication.get("payload_sha256") == EXPECTED_MANIFEST_PAYLOAD_SHA256, "manifest payload digest changed")
    payload = copy.deepcopy(manifest)
    payload_authentication = payload.get("authentication")
    require(isinstance(payload_authentication, dict), "manifest authentication is malformed")
    payload_authentication.pop("payload_sha256", None)
    require(sha256_bytes(canonical_json(payload)) == EXPECTED_MANIFEST_PAYLOAD_SHA256, "manifest payload verification failed")
    repository = manifest.get("repository")
    require(isinstance(repository, dict), "manifest repository record is absent")
    require(repository.get("base_git_revision") == EXPECTED_BASE_REVISION, "generation base revision changed")
    require(repository.get("base_revision_role") == "generation base recorded by all lane artifacts; it must exist and be an ancestor of current HEAD", "manifest base-revision role changed")
    require(repository.get("head_policy") == "later commits are allowed because every delivered bundle file remains authenticated by size and SHA-256", "manifest HEAD policy changed")
    base_revision_policy = verify_base_revision_policy(EXPECTED_BASE_REVISION)
    records = manifest.get("files")
    require(isinstance(records, list), "manifest file inventory is absent")
    by_id = {record.get("id"): record for record in records if isinstance(record, dict)}
    require(len(by_id) == len(records), "manifest file ids are invalid or duplicated")
    observed: dict[str, Any] = {
        "manifest": {
            "path": MANIFEST.relative_to(REPOSITORY_ROOT).as_posix(),
            "bytes": len(manifest_raw),
            "sha256": EXPECTED_MANIFEST_SHA256,
            "payload_sha256": EXPECTED_MANIFEST_PAYLOAD_SHA256,
            "base_revision_policy": base_revision_policy,
        }
    }
    loaded: dict[str, bytes] = {}
    for file_id, expected in EXPECTED_INVENTORY.items():
        record = by_id.get(file_id)
        require(isinstance(record, dict), f"manifest inventory id {file_id!r} is absent")
        for field in ("path", "bytes", "sha256"):
            require(record.get(field) == expected[field], f"manifest {file_id} {field} changed")
        path = REPOSITORY_ROOT / expected["path"]
        require(path.is_file(), f"input file is absent: {expected['path']}")
        if file_id in ("canonical_fixture", "support5_census_artifact", "generic_germ_artifact"):
            data = path.read_bytes()
            loaded[file_id] = data
            actual_hash = sha256_bytes(data)
            actual_size = len(data)
        else:
            actual_hash, actual_size = hash_file(path)
        require(actual_hash == expected["sha256"], f"input SHA-256 mismatch: {expected['path']}")
        require(actual_size == expected["bytes"], f"input byte count mismatch: {expected['path']}")
        observed[file_id] = dict(expected)
    support = load_json(loaded["support5_census_artifact"], EXPECTED_INVENTORY["support5_census_artifact"]["path"])
    require(support.get("artifact_schema") == "rank49-t4-support5-census-v4", "support artifact schema mismatch")
    certificate = support.get("result", {}).get("census_content_certificate")
    require(isinstance(certificate, dict), "support content certificate is absent")
    require(sha256_bytes(canonical_json(certificate.get("content"))) == certificate.get("content_sha256"), "support content certificate digest mismatch")
    generic = load_json(loaded["generic_germ_artifact"], EXPECTED_INVENTORY["generic_germ_artifact"]["path"])
    require(generic.get("schema") == "BilinearComplexity.rank49_t4.generic_germ.v3", "generic-germ artifact schema mismatch")
    generic_authentication = generic.get("authentication")
    require(isinstance(generic_authentication, dict), "generic-germ authentication is absent")
    generic_payload = {key: value for key, value in generic.items() if key != "authentication"}
    require(sha256_bytes(canonical_json(generic_payload)) == generic_authentication.get("payload_sha256"), "generic-germ payload digest mismatch")
    return support, generic, loaded["canonical_fixture"], observed


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
            base = 256 * i + 16 * j
            for k in bit_positions(third):
                result ^= 1 << (base + k)
    return result


def parse_fixture(raw: bytes) -> tuple[tuple[int, int, int], ...]:
    tokens = raw.split()
    require(len(tokens) == 4 + 3 * RANK * FACTOR_DIMENSION, "fixture token count mismatch")
    try:
        values = [int(token) for token in tokens]
    except ValueError as error:
        raise ReplayFailure("fixture has a noninteger token") from error
    require(values[:4] == [4, 4, 4, 49], "fixture header mismatch")
    payload = values[4:]
    require(all(value in (0, 1) for value in payload), "fixture is not binary")
    legs: list[list[int]] = []
    offset = 0
    for _ in range(3):
        leg = []
        for _ in range(RANK):
            leg.append(sum(payload[offset + entry] << entry for entry in range(FACTOR_DIMENSION)))
            offset += FACTOR_DIMENSION
        legs.append(leg)
    terms = tuple(zip(*legs))
    require(len(terms) == RANK, "fixture term count mismatch")
    represented = 0
    for term in terms:
        require(all(term), "fixture has a zero factor")
        represented ^= outer3(*term)
    target = 0
    for a in range(4):
        for b in range(4):
            for c in range(4):
                target ^= 1 << (256 * (4 * a + b) + 16 * (4 * b + c) + (4 * c + a))
    require(represented == target, "fixture fails the 4096 Brent equations")
    return terms


def add_to_basis(basis: dict[int, int], value: int) -> bool:
    while value:
        pivot = value.bit_length() - 1
        old = basis.get(pivot)
        if old is None:
            basis[pivot] = value
            return True
        value ^= old
    return False


def vector_rank(values: Iterable[int]) -> int:
    basis: dict[int, int] = {}
    for value in values:
        add_to_basis(basis, value)
    return len(basis)


def plain_basis(values: Iterable[int]) -> dict[int, int]:
    basis: dict[int, int] = {}
    for value in values:
        add_to_basis(basis, value)
    return basis


def normal_form(basis: dict[int, int], value: int) -> int:
    for pivot in sorted(basis, reverse=True):
        if (value >> pivot) & 1:
            value ^= basis[pivot]
    return value


def echelon_with_tags(columns: list[int]) -> tuple[dict[int, tuple[int, int]], list[int], list[int]]:
    basis: dict[int, tuple[int, int]] = {}
    kernel: list[int] = []
    pivots: list[int] = []
    for index, column in enumerate(columns):
        value = column
        tag = 1 << index
        while value:
            pivot = value.bit_length() - 1
            old = basis.get(pivot)
            if old is None:
                basis[pivot] = (value, tag)
                pivots.append(index)
                break
            value ^= old[0]
            tag ^= old[1]
        if not value:
            require(tag != 0, "zero kernel dependency")
            kernel.append(tag)
    return basis, kernel, pivots


def solve_echelon(basis: dict[int, tuple[int, int]], target: int) -> int | None:
    solution = 0
    while target:
        pivot = target.bit_length() - 1
        old = basis.get(pivot)
        if old is None:
            return None
        target ^= old[0]
        solution ^= old[1]
    return solution


def apply_columns(columns: list[int], coefficients: int) -> int:
    result = 0
    for index in bit_positions(coefficients):
        result ^= columns[index]
    return result


def full_jacobian(terms: tuple[tuple[int, int, int], ...]) -> list[int]:
    columns = []
    for leg in range(3):
        for first, second, third in terms:
            if leg == 0:
                columns.extend(outer3(1 << entry, second, third) for entry in range(16))
            elif leg == 1:
                columns.extend(outer3(first, 1 << entry, third) for entry in range(16))
            else:
                columns.extend(outer3(first, second, 1 << entry) for entry in range(16))
    require(len(columns) == DOMAIN_DIMENSION, "Jacobian column count mismatch")
    return columns


def pack_variation(rows: Iterable[Iterable[int]]) -> int:
    result = 0
    rows_tuple = tuple(tuple(row) for row in rows)
    require(len(rows_tuple) == RANK and all(len(row) == 3 for row in rows_tuple), "variation shape mismatch")
    for term, row in enumerate(rows_tuple):
        for leg, value in enumerate(row):
            require(0 <= value < (1 << 16), "variation factor is not a 16-bit mask")
            result ^= value << ((leg * RANK + term) * FACTOR_DIMENSION)
    return result


def left_matrix_unit(mask: int, row: int, column: int) -> int:
    return ((mask >> (4 * column)) & 0xF) << (4 * row)


def right_matrix_unit(mask: int, row: int, column: int) -> int:
    result = 0
    for source_row in range(4):
        result |= ((mask >> (4 * source_row + row)) & 1) << (4 * source_row + column)
    return result


def connected_gauge(terms: tuple[tuple[int, int, int], ...]) -> list[int]:
    generators = []
    for term, (first, second, third) in enumerate(terms):
        rows = [[0, 0, 0] for _ in range(RANK)]
        rows[term] = [first, second, 0]
        generators.append(pack_variation(rows))
        rows = [[0, 0, 0] for _ in range(RANK)]
        rows[term] = [first, 0, third]
        generators.append(pack_variation(rows))
    for vertex in range(3):
        for row in range(4):
            for column in range(4):
                variation = []
                for first, second, third in terms:
                    if vertex == 0:
                        variation.append((left_matrix_unit(first, row, column), 0, right_matrix_unit(third, row, column)))
                    elif vertex == 1:
                        variation.append((right_matrix_unit(first, row, column), left_matrix_unit(second, row, column), 0))
                    else:
                        variation.append((0, right_matrix_unit(second, row, column), left_matrix_unit(third, row, column)))
                generators.append(pack_variation(variation))
    require(len(generators) == EXPECTED["gauge_generator_count"], "connected-gauge generator count mismatch")
    return generators


def parse_hex_mask(value: Any, label: str) -> int:
    require(isinstance(value, str) and len(value) == 4, f"invalid 16-bit mask at {label}")
    try:
        result = int(value, 16)
    except ValueError as error:
        raise ReplayFailure(f"invalid hexadecimal mask at {label}") from error
    require(0 <= result < (1 << 16), f"mask out of range at {label}")
    return result


def rows_from_sparse(records: Any, label: str) -> tuple[tuple[int, int, int], ...]:
    require(isinstance(records, list), f"{label} is not a list")
    rows = [[0, 0, 0] for _ in range(RANK)]
    seen: set[int] = set()
    for record in records:
        require(isinstance(record, dict), f"{label} entry is not an object")
        slot = record.get("slot")
        require(isinstance(slot, int) and 0 <= slot < RANK and slot not in seen, f"invalid or repeated slot in {label}")
        seen.add(slot)
        for leg, name in enumerate(FACTOR_LEGS):
            rows[slot][leg] = parse_hex_mask(record.get(name), f"{label}[{slot}].{name}")
    return tuple(tuple(row) for row in rows)


def updates_from_records(value: Any, label: str) -> tuple[tuple[int, int, int], ...]:
    require(isinstance(value, list), f"{label} is not a list")
    rows = [[0, 0, 0] for _ in range(RANK)]
    occupied: set[tuple[int, int]] = set()
    for record in value:
        require(isinstance(record, dict), f"{label} entry is not an object")
        slot = record.get("slot")
        factor = record.get("factor")
        require(isinstance(slot, int) and 0 <= slot < RANK, f"invalid slot in {label}")
        require(factor in FACTOR_LEGS, f"invalid factor in {label}")
        leg = FACTOR_LEGS.index(factor)
        require((slot, leg) not in occupied, f"duplicate update in {label}")
        occupied.add((slot, leg))
        rows[slot][leg] = parse_hex_mask(record.get("add"), f"{label}[{slot}].add")
        require(rows[slot][leg] != 0, f"zero update in {label}")
    return tuple(tuple(row) for row in rows)


def xor_rows(first: tuple[tuple[int, int, int], ...], second: tuple[tuple[int, int, int], ...]) -> tuple[tuple[int, int, int], ...]:
    return tuple(tuple(x ^ y for x, y in zip(a, b)) for a, b in zip(first, second))


@dataclass(frozen=True)
class Move:
    index: int
    combinadic_lex_id: int
    support: tuple[int, ...]
    orientation: str
    labels: tuple[int, ...]
    middle_leg: str
    s_updates: tuple[tuple[int, int, int], ...]
    t_updates: tuple[tuple[int, int, int], ...]
    tangent_rows: tuple[tuple[int, int, int], ...]
    tangent: int
    section_rows: tuple[tuple[int, int, int], ...]
    section: int
    artifact_record: dict[str, Any]


def transpose(mask: int) -> int:
    return sum(((mask >> (4 * row + column)) & 1) << (4 * column + row) for row in range(4) for column in range(4))


def oriented_terms(terms: tuple[tuple[int, int, int], ...], orientation: str) -> tuple[tuple[int, int, int], ...]:
    if orientation == "abc":
        return terms
    if orientation == "bca":
        return tuple((second, third, first) for first, second, third in terms)
    if orientation == "cab":
        return tuple((third, first, second) for first, second, third in terms)
    if orientation == "acb":
        return tuple((transpose(third), transpose(second), transpose(first)) for first, second, third in terms)
    if orientation == "cba":
        return tuple((transpose(second), transpose(first), transpose(third)) for first, second, third in terms)
    if orientation == "bac":
        return tuple((transpose(first), transpose(third), transpose(second)) for first, second, third in terms)
    raise ReplayFailure(f"invalid orientation {orientation!r}")


def inverse_orient_variation(orientation: str, variation: tuple[int, int, int]) -> tuple[int, int, int]:
    first, second, third = variation
    if orientation == "abc":
        return first, second, third
    if orientation == "bca":
        return third, first, second
    if orientation == "cab":
        return second, third, first
    if orientation == "acb":
        return transpose(third), transpose(second), transpose(first)
    if orientation == "cba":
        return transpose(second), transpose(first), transpose(third)
    if orientation == "bac":
        return transpose(first), transpose(third), transpose(second)
    raise ReplayFailure(f"invalid orientation {orientation!r}")


def reconstruct_updates(
    terms: tuple[tuple[int, int, int], ...], orientation: str, labels: tuple[int, ...]
) -> tuple[tuple[tuple[int, int, int], ...], tuple[tuple[int, int, int], ...]]:
    oriented = oriented_terms(terms, orientation)
    a, b, c, d, e = labels
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
    zero = (0, 0, 0)
    s_updates = tuple(inverse_orient_variation(orientation, s_oriented.get(slot, zero)) for slot in range(RANK))
    t_updates = tuple(inverse_orient_variation(orientation, t_oriented.get(slot, zero)) for slot in range(RANK))
    return s_updates, t_updates


def parse_moves(
    support_artifact: dict[str, Any], terms: tuple[tuple[int, int, int], ...]
) -> tuple[list[Move], dict[str, int]]:
    result = support_artifact.get("result")
    require(isinstance(result, dict), "support result is absent")
    raw_records = result.get("positive_normal_supports")
    require(isinstance(raw_records, list) and len(raw_records) == EXPECTED["move_count"], "positive-support count mismatch")
    records = sorted(raw_records, key=lambda record: (record.get("combinadic_lex_id"), record.get("support0")))
    moves = []
    canonical_matches_section = 0
    for index, record in enumerate(records):
        require(isinstance(record, dict), "positive-support entry is not an object")
        support = tuple(record.get("support0", ()))
        require(len(support) == 5 and tuple(sorted(support)) == support and len(set(support)) == 5, "invalid five-support")
        require(record.get("normal_dimension") == 1 and record.get("reduced_rank") == 229, "positive-support rank/normal data changed")
        paired = record.get("paired_t3")
        require(isinstance(paired, dict), "paired-T3 record is absent")
        canonical = paired.get("canonical_oriented_factor_update_witness")
        require(isinstance(canonical, dict), "canonical paired-T3 witness is absent")
        orientation = canonical.get("orientation")
        labels = tuple(canonical.get("labels_abcde", ()))
        require(orientation in ORIENTATION_ORDER, "canonical orientation is invalid")
        require(len(labels) == 5 and set(labels) == set(support), "canonical labels do not equal the support")
        updates = canonical.get("separate_factor_updates_in_original_coordinate_frame")
        require(isinstance(updates, dict), "canonical original-frame updates are absent")
        s_updates = updates_from_records(updates.get("s"), f"move {index} s-updates")
        t_updates = updates_from_records(updates.get("t"), f"move {index} t-updates")
        reconstructed_s, reconstructed_t = reconstruct_updates(terms, orientation, labels)
        require(s_updates == reconstructed_s and t_updates == reconstructed_t, f"move {index} stored updates disagree with the fixture-derived paired-T3 construction")
        tangent_rows = xor_rows(s_updates, t_updates)
        tangent = pack_variation(tangent_rows)
        projective = record.get("projective_directions", {}).get("F2", {}).get("directions")
        require(isinstance(projective, list) and len(projective) == 1, "binary projective direction changed")
        section_rows = rows_from_sparse(projective[0].get("raw_variation"), f"move {index} normal section")
        section = pack_variation(section_rows)
        witnesses = paired.get("witnesses")
        require(isinstance(witnesses, list) and witnesses, "paired-T3 witnesses are absent")
        candidates = []
        selected_witness_vector = None
        for witness in witnesses:
            require(isinstance(witness, dict), "paired-T3 witness is not an object")
            witness_rows = rows_from_sparse(witness.get("raw_tangent"), f"move {index} witness")
            witness_vector = pack_variation(witness_rows)
            witness_orientation = witness.get("orientation")
            witness_labels = tuple(witness.get("labels", ()))
            require(witness_orientation in ORIENTATION_ORDER and len(witness_labels) == 5, "invalid paired-T3 witness key")
            key = (witness_vector != section, ORIENTATION_ORDER.index(witness_orientation), witness_labels)
            candidates.append((key, witness_orientation, witness_labels, witness_vector))
            if witness_orientation == orientation and witness_labels == labels:
                selected_witness_vector = witness_vector
        chosen = min(candidates)
        require((chosen[1], chosen[2]) == (orientation, labels), "canonical witness selection rule failed")
        require(selected_witness_vector == tangent, "canonical updates do not reproduce the selected witness tangent")
        canonical_matches_section += tangent == section
        moves.append(Move(
            index=index,
            combinadic_lex_id=record.get("combinadic_lex_id"),
            support=support,
            orientation=orientation,
            labels=labels,
            middle_leg=ORIENTATION_MIDDLE_LEG[orientation],
            s_updates=s_updates,
            t_updates=t_updates,
            tangent_rows=tangent_rows,
            tangent=tangent,
            section_rows=section_rows,
            section=section,
            artifact_record=record,
        ))
    require(len({move.combinadic_lex_id for move in moves}) == len(moves), "duplicate move lex id")
    require(len({move.support for move in moves}) == len(moves), "duplicate move support")
    return moves, {"canonical_equals_normal_section": canonical_matches_section, "canonical_differs_by_gauge": len(moves) - canonical_matches_section}


def xor_coefficient(target: dict[Any, int], key: Any, value: int) -> None:
    if not value:
        return
    target[key] = target.get(key, 0) ^ value
    if target[key] == 0:
        del target[key]


def laurent_factor(base: int, s_update: int, t_update: int) -> dict[int, int]:
    result: dict[int, int] = {}
    xor_coefficient(result, 0, base ^ s_update ^ t_update)
    xor_coefficient(result, -1, s_update)
    xor_coefficient(result, 1, t_update)
    return result


def polynomial_factor(base: int, s_update: int, t_update: int) -> dict[tuple[int, int], int]:
    result = {(0, 0): base}
    xor_coefficient(result, (1, 0), s_update)
    xor_coefficient(result, (0, 1), t_update)
    return result


def expand_tensor(first: dict[Any, int], second: dict[Any, int], third: dict[Any, int]) -> dict[Any, int]:
    result: dict[Any, int] = {}
    for first_key, first_value in first.items():
        for second_key, second_value in second.items():
            for third_key, third_value in third.items():
                if isinstance(first_key, tuple):
                    key = tuple(a + b + c for a, b, c in zip(first_key, second_key, third_key))
                else:
                    key = first_key + second_key + third_key
                xor_coefficient(result, key, outer3(first_value, second_value, third_value))
    return result


def factor_three_circuits(terms: tuple[tuple[int, int, int], ...]) -> dict[str, list[tuple[int, int, int]]]:
    result: dict[str, list[tuple[int, int, int]]] = {}
    for leg, name in enumerate(FACTOR_LEGS):
        values = [term[leg] for term in terms]
        require(all(values) and len(set(values)) == len(values), f"{name} factor list is not simple")
        by_value = {value: index for index, value in enumerate(values)}
        circuits = []
        for first in range(RANK):
            for second in range(first + 1, RANK):
                third = by_value.get(values[first] ^ values[second])
                if third is not None and second < third:
                    circuits.append((first, second, third))
        result[name] = circuits
    return result


def replay_poles(
    terms: tuple[tuple[int, int, int], ...], moves: list[Move], support_artifact: dict[str, Any]
) -> tuple[dict[str, Any], list[tuple[tuple[str, tuple[int, int, int]], tuple[str, tuple[int, int, int]]]]]:
    all_factor_circuits = factor_three_circuits(terms)
    expected_counts = support_artifact["result"]["factor_three_circuits"].get("counts")
    require([len(all_factor_circuits[name]) for name in FACTOR_LEGS] == expected_counts == [29, 29, 27], "factor three-circuit census changed")
    coefficient_digest = hashlib.sha256()
    endpoint_records = []
    coefficient_records = []
    coefficient_labelled_circuits: set[tuple[tuple[int, int], ...]] = set()
    exact_family_count = 0
    pole_occurrences = []
    pole_multiplicity: Counter[tuple[str, tuple[int, int, int]]] = Counter()
    for move in moves:
        polynomial: dict[tuple[int, int], int] = {}
        laurent: dict[int, int] = {}
        per_term_laurent: list[dict[int, int]] = []
        base_tensor = 0
        for slot, base in enumerate(terms):
            ds = move.s_updates[slot]
            dt = move.t_updates[slot]
            polynomial_term = expand_tensor(
                polynomial_factor(base[0], ds[0], dt[0]),
                polynomial_factor(base[1], ds[1], dt[1]),
                polynomial_factor(base[2], ds[2], dt[2]),
            )
            for key, value in polynomial_term.items():
                xor_coefficient(polynomial, key, value)
            laurent_term = expand_tensor(
                laurent_factor(base[0], ds[0], dt[0]),
                laurent_factor(base[1], ds[1], dt[1]),
                laurent_factor(base[2], ds[2], dt[2]),
            )
            require(all(-1 <= exponent <= 1 for exponent in laurent_term), f"move {move.index} summand {slot} has Laurent exponent outside [-1,1]")
            per_term_laurent.append(laurent_term)
            for exponent, value in laurent_term.items():
                xor_coefficient(laurent, exponent, value)
            base_tensor ^= outer3(*base)
        xor_coefficient(polynomial, (0, 0), base_tensor)
        xor_coefficient(laurent, 0, base_tensor)
        require(not laurent, f"move {move.index} Laurent family is not tensor-constant")
        require(set(polynomial) == {(1, 0), (0, 1), (1, 1)}, f"move {move.index} bivariate support changed")
        coefficient_a = polynomial[(1, 0)]
        require(coefficient_a != 0 and coefficient_a == polynomial[(0, 1)] == polynomial[(1, 1)], f"move {move.index} fails A=B=C")
        exact_family_count += 1
        coefficient_records.append(coefficient_a)
        a, b, c, d, e = move.labels
        expected_triples = ((a, d, e), (b, c, e))
        endpoints = []
        for pole_number, (exponent, expected_triple) in enumerate(zip((-1, 1), expected_triples)):
            leading = [(slot, coefficients[exponent]) for slot, coefficients in enumerate(per_term_laurent) if coefficients.get(exponent)]
            actual_triple = tuple(slot for slot, _ in leading)
            require(len(leading) == 3 and actual_triple == tuple(sorted(expected_triple)), f"move {move.index} pole leading support changed")
            tensors = [value for _, value in leading]
            require(len(set(tensors)) == 3 and all(tensors) and tensors[0] ^ tensors[1] ^ tensors[2] == 0, f"move {move.index} pole leading tensors are not a simple three-circuit")
            factor_triple = tuple(sorted(expected_triple))
            factor_values = [terms[slot][FACTOR_LEGS.index(move.middle_leg)] for slot in factor_triple]
            require(len(set(factor_values)) == 3 and all(factor_values) and factor_values[0] ^ factor_values[1] ^ factor_values[2] == 0, f"move {move.index} middle factors are not a simple three-circuit")
            require(factor_triple in all_factor_circuits[move.middle_leg], f"move {move.index} pole circuit is absent from the factor census")
            artifact_inside = move.artifact_record["factor_three_circuits_inside_support"][move.middle_leg]
            require(list(factor_triple) in artifact_inside, f"move {move.index} pole circuit is absent from its support certificate")
            endpoint = (move.middle_leg, factor_triple)
            endpoints.append(endpoint)
            pole_occurrences.append(endpoint)
            pole_multiplicity[endpoint] += 1
            coefficient_labelled_circuits.add(tuple((slot, tensor) for slot, tensor in leading))
            coefficient_digest.update(bytes((move.index, pole_number)))
            for slot, tensor in leading:
                coefficient_digest.update(bytes((slot,)))
                coefficient_digest.update(tensor.to_bytes(512, "little"))
        endpoint_records.append((endpoints[0], endpoints[1]))
    require(exact_family_count == EXPECTED["move_count"], "not all canonical Laurent families replayed")
    require(len(pole_occurrences) == EXPECTED["pole_circuit_occurrences"], "pole circuit occurrence count mismatch")
    require(len(coefficient_labelled_circuits) == EXPECTED["pole_circuit_occurrences"], "coefficient-labelled pole circuits are not all distinct")
    require(set(pole_multiplicity.values()) == {2}, "pole factor-circuit occurrence multiplicities changed")
    serialized_endpoints = [
        [[leg, list(triple)] for leg, triple in endpoints]
        for endpoints in endpoint_records
    ]
    claim = {
        "status": "PASS",
        "catalog_scope": CATALOG_SCOPE,
        "definition": "For each of the 63 authenticated-artifact paired-T3 representatives, the nonzero b^-1 and b^1 coefficients of individual summands form simple three-circuits; their term triples are the two certified middle-factor circuits.",
        "authenticated_artifact_families_replayed": exact_family_count,
        "bivariate_A_equals_B_equals_C": exact_family_count,
        "pole_counts": {"b=0 (exponent -1)": len(moves), "b=infinity (exponent +1)": len(moves)},
        "leading_three_circuit_occurrences": len(pole_occurrences),
        "distinct_coefficient_labelled_circuits": len(coefficient_labelled_circuits),
        "unique_factor_three_circuits_used": len(pole_multiplicity),
        "occurrence_multiplicity_histogram": {str(key): value for key, value in sorted(Counter(pole_multiplicity.values()).items())},
        "all_factor_three_circuit_counts": {name: len(all_factor_circuits[name]) for name in FACTOR_LEGS},
        "endpoints_sha256": sha256_bytes(canonical_json(serialized_endpoints)),
        "leading_circuit_transcript_sha256": coefficient_digest.hexdigest(),
        "A_coefficients_sha256_512le": fixed_width_digest(coefficient_records, 512),
    }
    return claim, endpoint_records


def support_components(moves: list[Move]) -> list[list[int]]:
    supports = [set(move.support) for move in moves]
    unseen = set(range(len(moves)))
    components = []
    while unseen:
        start = min(unseen)
        unseen.remove(start)
        queue = deque([start])
        component = []
        while queue:
            current = queue.popleft()
            component.append(current)
            neighbors = {other for other in unseen if supports[current] & supports[other]}
            unseen -= neighbors
            queue.extend(sorted(neighbors))
        components.append(sorted(component))
    return sorted(components, key=lambda component: component[0])


def replay_blocks(moves: list[Move], pole_endpoints: list[tuple[tuple[str, tuple[int, int, int]], tuple[str, tuple[int, int, int]]]]) -> dict[str, Any]:
    components = support_components(moves)
    require(len(components) == EXPECTED["block_count"] and all(len(component) == EXPECTED["moves_per_block"] for component in components), "support components are not seven blocks of nine")
    blocks = []
    term_blocks = []
    pair_intersections: Counter[int] = Counter()
    for component_index, component in enumerate(components):
        support_sets = [set(moves[index].support) for index in component]
        term_set = set().union(*support_sets)
        hub = set.intersection(*support_sets)
        require(len(term_set) == 7 and len(hub) == 1, f"block {component_index} does not have seven terms and one hub")
        omission_edges = {index: tuple(sorted(term_set - set(moves[index].support))) for index in component}
        require(all(len(edge) == 2 and not (set(edge) & hub) for edge in omission_edges.values()), f"block {component_index} has a bad omitted pair")
        adjacency: dict[int, set[int]] = defaultdict(set)
        for first, second in omission_edges.values():
            adjacency[first].add(second)
            adjacency[second].add(first)
        require(len(adjacency) == 6 and all(len(neighbors) == 3 for neighbors in adjacency.values()), f"block {component_index} omitted-pair graph is not cubic on six vertices")
        colors = {min(adjacency): 0}
        queue = deque(colors)
        while queue:
            vertex = queue.popleft()
            for neighbor in sorted(adjacency[vertex]):
                if neighbor in colors:
                    require(colors[neighbor] != colors[vertex], f"block {component_index} omitted-pair graph is not bipartite")
                else:
                    colors[neighbor] = 1 - colors[vertex]
                    queue.append(neighbor)
        left = tuple(sorted(vertex for vertex, color in colors.items() if color == 0))
        right = tuple(sorted(vertex for vertex, color in colors.items() if color == 1))
        if left > right:
            left, right = right, left
        require(len(left) == len(right) == 3, f"block {component_index} bipartition is not 3+3")
        require(set(omission_edges.values()) == {tuple(sorted(edge)) for edge in itertools.product(left, right)}, f"block {component_index} omitted pairs are not all K3,3 edges")
        line_degrees = []
        local_intersections: Counter[int] = Counter()
        for first in component:
            degree = 0
            for second in component:
                if first == second:
                    continue
                intersection = len(set(moves[first].support) & set(moves[second].support))
                if first < second:
                    local_intersections[intersection] += 1
                    pair_intersections[intersection] += 1
                if intersection == 4:
                    degree += 1
            line_degrees.append(degree)
        require(local_intersections == Counter({3: 18, 4: 18}), f"block {component_index} support intersection pattern changed")
        require(line_degrees == [4] * 9, f"block {component_index} line graph is not 4-regular")
        term_blocks.append(term_set)
        blocks.append({
            "block": component_index,
            "move_indices": component,
            "combinadic_lex_ids": [moves[index].combinadic_lex_id for index in component],
            "term_set": sorted(term_set),
            "hub_term": next(iter(hub)),
            "K3,3_bipartition": [list(left), list(right)],
            "support_as_omitted_edge": [
                {"move": index, "edge": list(omission_edges[index])}
                for index in sorted(component, key=lambda index: omission_edges[index])
            ],
            "support_pair_intersections": {str(key): value for key, value in sorted(local_intersections.items())},
            "line_graph_degree_sequence": sorted(line_degrees),
            "pole_circuit_occurrences": 2 * len(component),
            "unique_pole_factor_circuits": len({endpoint for index in component for endpoint in pole_endpoints[index]}),
        })
    for first, second in itertools.combinations(range(len(term_blocks)), 2):
        require(not (term_blocks[first] & term_blocks[second]), "seven-term blocks are not disjoint")
    require(set().union(*term_blocks) == set(range(RANK)), "seven-term blocks do not cover all 49 terms")
    for first, second in itertools.combinations(range(len(moves)), 2):
        if not (set(moves[first].support) & set(moves[second].support)):
            pair_intersections[0] += 1
    require(pair_intersections == Counter({0: 1701, 3: 126, 4: 126}), "global support intersection histogram changed")
    block_digest_content = [
        {
            "moves": block["move_indices"],
            "terms": block["term_set"],
            "hub": block["hub_term"],
            "parts": block["K3,3_bipartition"],
            "edges": block["support_as_omitted_edge"],
        }
        for block in blocks
    ]
    compact_block_transcript = bytes(
        coordinate
        for block in blocks
        for coordinate in (block["hub_term"], *block["K3,3_bipartition"][0], *block["K3,3_bipartition"][1])
    )
    return {
        "status": "PASS",
        "catalog_scope": CATALOG_SCOPE,
        "definition": "Within the 63 supports supplied by the authenticated artifact, each support is the hub plus four peripheral terms; its omitted peripheral pair is an edge. In every component the nine omitted pairs are exactly the edges of K3,3.",
        "block_count": len(blocks),
        "compact_core_bipartitions_sha256": sha256_bytes(compact_block_transcript),
        "supports_per_block": [len(component) for component in components],
        "term_blocks_pairwise_disjoint": True,
        "term_blocks_cover_all_49_terms": True,
        "global_support_pair_intersection_histogram": {str(key): value for key, value in sorted(pair_intersections.items())},
        "blocks_sha256": sha256_bytes(canonical_json(block_digest_content)),
        "blocks": blocks,
    }


def quadratic_coefficient(terms: tuple[tuple[int, int, int], ...], variation: tuple[tuple[int, int, int], ...]) -> int:
    result = 0
    for (first, second, third), (dfirst, dsecond, dthird) in zip(terms, variation):
        result ^= outer3(dfirst, dsecond, third)
        result ^= outer3(dfirst, second, dthird)
        result ^= outer3(first, dsecond, dthird)
    return result


def mixed_coefficient(
    terms: tuple[tuple[int, int, int], ...],
    first_variation: tuple[tuple[int, int, int], ...],
    second_variation: tuple[tuple[int, int, int], ...],
) -> int:
    result = 0
    for (first, second, third), (dfirst, dsecond, dthird), (efirst, esecond, ethird) in zip(terms, first_variation, second_variation):
        result ^= outer3(dfirst, esecond, third) ^ outer3(efirst, dsecond, third)
        result ^= outer3(dfirst, second, ethird) ^ outer3(efirst, second, dthird)
        result ^= outer3(first, dsecond, ethird) ^ outer3(first, esecond, dthird)
    return result


def replay_linear_structure(
    terms: tuple[tuple[int, int, int], ...], moves: list[Move], generic_artifact: dict[str, Any]
) -> tuple[dict[str, Any], list[int], dict[int, tuple[int, int]], dict[int, int]]:
    jacobian = full_jacobian(terms)
    image_basis, kernel_basis, pivot_columns = echelon_with_tags(jacobian)
    require(len(image_basis) == EXPECTED["jacobian_rank"], "Jacobian rank mismatch")
    require(len(kernel_basis) == EXPECTED["kernel_dimension"], "Jacobian kernel dimension mismatch")
    require(all(apply_columns(jacobian, dependency) == 0 for dependency in kernel_basis), "Jacobian kernel certificate failed")
    gauge = connected_gauge(terms)
    require(all(apply_columns(jacobian, generator) == 0 for generator in gauge), "connected-gauge generator leaves the Jacobian kernel")
    gauge_basis = plain_basis(gauge)
    require(len(gauge_basis) == EXPECTED["gauge_rank"], "connected-gauge rank mismatch")
    tangents = [move.tangent for move in moves]
    sections = [move.section for move in moves]
    require(all(apply_columns(jacobian, tangent) == 0 for tangent in tangents), "canonical move tangent leaves the Jacobian kernel")
    require(all(apply_columns(jacobian, section) == 0 for section in sections), "normal-section representative leaves the Jacobian kernel")
    require(all(normal_form(gauge_basis, move.tangent ^ move.section) == 0 for move in moves), "canonical move and normal section differ outside gauge")
    direction_rank = vector_rank(tangents)
    combined_rank = vector_rank(gauge + tangents)
    intersection_dimension = len(gauge_basis) + direction_rank - combined_rank
    quotient_span_dimension = combined_rank - len(gauge_basis)
    require(direction_rank == EXPECTED["direction_rank"], "canonical direction rank mismatch")
    require(combined_rank == EXPECTED["kernel_dimension"], "gauge plus canonical directions do not span the Jacobian kernel")
    require(intersection_dimension == EXPECTED["direction_gauge_intersection"], "direction/gauge intersection dimension mismatch")
    require(quotient_span_dimension == EXPECTED["normal_dimension"], "canonical quotient span dimension mismatch")
    normal_classes = [normal_form(gauge_basis, tangent) for tangent in tangents]
    require(all(normal_classes) and len(set(normal_classes)) == len(normal_classes), "canonical move classes are not distinct nonzero normal classes")
    artifact_dimensions = generic_artifact.get("claims", {}).get("connected_symmetry_and_sweep", {}).get("tangent_dimensions")
    require(isinstance(artifact_dimensions, dict), "generic-germ tangent dimensions are absent")
    require(
        artifact_dimensions.get("jacobian_kernel") == len(kernel_basis)
        and artifact_dimensions.get("connected_orbit") == len(gauge_basis)
        and artifact_dimensions.get("normal_tangent_quotient") == quotient_span_dimension,
        "generic-germ tangent dimensions disagree with replay",
    )
    support_global = moves[0].artifact_record
    require(support_global is not None, "move catalog is empty")
    claim = {
        "status": "PASS",
        "catalog_scope": CATALOG_SCOPE,
        "scope": "For the 63 directions supplied by the authenticated support artifact, the 54-dimensional object is the vector-space quotient ker(J)/image(dH), not a geometric, formal, or scheme-theoretic normal slice.",
        "ambient_dimensions": {"domain": DOMAIN_DIMENSION, "tensor": TENSOR_DIMENSION},
        "jacobian": {
            "columns": len(jacobian),
            "rank": len(image_basis),
            "kernel_dimension": len(kernel_basis),
            "pivot_column_count": len(pivot_columns),
            "columns_sha256_512le": fixed_width_digest(jacobian, 512),
        },
        "connected_gauge": {"generator_count": len(gauge), "rank": len(gauge_basis)},
        "paired_T3_directions": {
            "count": len(tangents),
            "raw_span_rank": direction_rank,
            "intersection_with_gauge_dimension": intersection_dimension,
            "gauge_plus_directions_rank": combined_rank,
            "span_modulo_gauge_dimension": quotient_span_dimension,
            "equals_full_normal_quotient": combined_rank == len(kernel_basis),
            "raw_vectors_sha256_294le": fixed_width_digest(tangents, 294),
            "normal_classes_sha256_294le": fixed_width_digest(normal_classes, 294),
        },
    }
    return claim, jacobian, image_basis, gauge_basis


def parse_pair_range(value: str | None, total: int) -> tuple[int, int]:
    if value is None:
        return 0, total
    pieces = value.split(":")
    require(len(pieces) == 2 and all(piece.strip() for piece in pieces), "--pair-range must be START:STOP")
    try:
        start, stop = (int(piece) for piece in pieces)
    except ValueError as error:
        raise ReplayFailure("--pair-range endpoints must be integers") from error
    require(0 <= start <= stop <= total, f"--pair-range must lie in 0:{total}")
    return start, stop


def replay_pairs(
    terms: tuple[tuple[int, int, int], ...],
    moves: list[Move],
    jacobian: list[int],
    image_basis: dict[int, tuple[int, int]],
    gauge_basis: dict[int, int],
    requested_range: tuple[int, int],
) -> dict[str, Any]:
    catalog = list(itertools.combinations(range(len(moves)), 2))
    require(len(catalog) == EXPECTED["pair_count"] == math.comb(EXPECTED["move_count"], 2), "move-pair catalog count mismatch")
    start, stop = requested_range
    selected = catalog[start:stop]
    normal_classes = [normal_form(gauge_basis, move.tangent) for move in moves]
    individual_quadratics = [quadratic_coefficient(terms, move.tangent_rows) for move in moves]
    individual_preimages = []
    for index, coefficient in enumerate(individual_quadratics):
        preimage = solve_echelon(image_basis, coefficient)
        require(preimage is not None and apply_columns(jacobian, preimage) == coefficient, f"move {index} has no verified second-order preimage")
        individual_preimages.append(preimage)
    class_sums: list[int] = []
    mixed_values: list[int] = []
    pair_catalog_digest = hashlib.sha256()
    mixed_digest = hashlib.sha256()
    mixed_preimage_digest = hashlib.sha256()
    sum_quadratic_digest = hashlib.sha256()
    sum_preimage_digest = hashlib.sha256()
    class_sum_digest = hashlib.sha256()
    mixed_zero = 0
    mixed_nonzero = 0
    pair_sum_quadratic_zero = 0
    failures = Counter()
    support_intersection_mixed: Counter[tuple[int, bool]] = Counter()
    for catalog_index, (first_index, second_index) in enumerate(selected, start=start):
        first = moves[first_index]
        second = moves[second_index]
        pair_catalog_digest.update(catalog_index.to_bytes(2, "little"))
        pair_catalog_digest.update(first_index.to_bytes(1, "little"))
        pair_catalog_digest.update(second_index.to_bytes(1, "little"))
        pair_vector = first.tangent ^ second.tangent
        if apply_columns(jacobian, pair_vector):
            failures["first_order_sum_not_in_kernel"] += 1
        direct_class = normal_form(gauge_basis, pair_vector)
        additive_class = normal_classes[first_index] ^ normal_classes[second_index]
        if direct_class != additive_class:
            failures["normal_class_not_additive"] += 1
        if not direct_class:
            failures["pair_sum_zero_modulo_gauge"] += 1
        class_sums.append(direct_class)
        class_sum_digest.update(direct_class.to_bytes(294, "little"))
        summed_rows = xor_rows(first.tangent_rows, second.tangent_rows)
        direct_quadratic = quadratic_coefficient(terms, summed_rows)
        mixed = mixed_coefficient(terms, first.tangent_rows, second.tangent_rows)
        polarized = individual_quadratics[first_index] ^ individual_quadratics[second_index] ^ mixed
        if direct_quadratic != polarized:
            failures["quadratic_polarization_identity"] += 1
        mixed_values.append(mixed)
        mixed_digest.update(mixed.to_bytes(512, "little"))
        sum_quadratic_digest.update(direct_quadratic.to_bytes(512, "little"))
        if mixed:
            mixed_nonzero += 1
        else:
            mixed_zero += 1
        if not direct_quadratic:
            pair_sum_quadratic_zero += 1
        intersection = len(set(first.support) & set(second.support))
        support_intersection_mixed[(intersection, bool(mixed))] += 1
        mixed_preimage = solve_echelon(image_basis, mixed)
        if mixed_preimage is None or apply_columns(jacobian, mixed_preimage) != mixed:
            failures["mixed_coefficient_not_in_jacobian_image"] += 1
            mixed_preimage = 0
        mixed_preimage_digest.update(mixed_preimage.to_bytes(294, "little"))
        sum_preimage = solve_echelon(image_basis, direct_quadratic)
        if sum_preimage is None or apply_columns(jacobian, sum_preimage) != direct_quadratic:
            failures["pair_sum_quadratic_not_in_jacobian_image"] += 1
            sum_preimage = 0
        assembled_preimage = individual_preimages[first_index] ^ individual_preimages[second_index] ^ mixed_preimage
        if sum_preimage != assembled_preimage:
            failures["canonical_preimage_not_additive"] += 1
        sum_preimage_digest.update(sum_preimage.to_bytes(294, "little"))
    require(not failures, "move-pair compatibility failures: " + ", ".join(f"{key}={value}" for key, value in sorted(failures.items())))
    complete = start == 0 and stop == len(catalog)
    if complete:
        require(mixed_zero == 1737 and mixed_nonzero == 216, "full mixed-coefficient zero/nonzero counts changed")
        require(support_intersection_mixed[(0, True)] == 0, "disjoint supports have a nonzero mixed coefficient")
        require(len(set(class_sums)) == len(catalog) and vector_rank(class_sums) == EXPECTED["normal_dimension"], "full pair-sum normal classes are not distinct with rank 54")
        nonzero_mixed = [value for value in mixed_values if value]
        require(len(set(nonzero_mixed)) == 216 and vector_rank(nonzero_mixed) == 216, "nonzero mixed coefficients are not 216 distinct independent targets")
    histogram = {
        f"support_intersection={intersection},mixed_nonzero={str(nonzero).lower()}": count
        for (intersection, nonzero), count in sorted(support_intersection_mixed.items())
    }
    return {
        "status": "PASS",
        "replay_extent": "FULL_AUTHENTICATED_MOVE_PAIR_CATALOG" if complete else "REQUESTED_AUTHENTICATED_CATALOG_SHARD",
        "catalog_scope": CATALOG_SCOPE,
        "definition": "For the 63 authenticated-artifact canonical s+t first-order representatives, GF(2) normal classes add canonically; Q(di+dj)=Q(di)+Q(dj)+B(di,dj); and both B(di,dj) and Q(di+dj) have verified deterministic preimages under the source Jacobian.",
        "scope": "This checks the pair catalog induced by the authenticated 63-move list and does not regenerate or certify exhaustive five-support selection. It is first-order class additivity plus unrestricted second-order compatibility, not a claim that coordinatewise sums of Laurent families are simultaneous all-order families.",
        "authenticated_move_pair_count": len(catalog),
        "requested_half_open_range": [start, stop],
        "replayed_pair_count": len(selected),
        "complete_authenticated_move_pair_catalog_replayed": complete,
        "compatibility_failures": 0,
        "pair_sums_nonzero_modulo_gauge": len(selected),
        "distinct_pair_sum_normal_classes": len(set(class_sums)),
        "pair_sum_normal_class_rank": vector_rank(class_sums),
        "polarization_identities_verified": len(selected),
        "mixed_coefficients_in_jacobian_image": len(selected),
        "pair_sum_quadratics_in_jacobian_image": len(selected),
        "mixed_coefficient_counts": {"zero": mixed_zero, "nonzero": mixed_nonzero},
        "distinct_nonzero_mixed_coefficients": len({value for value in mixed_values if value}),
        "nonzero_mixed_coefficient_rank": vector_rank(value for value in mixed_values if value),
        "pair_sum_quadratic_zero_count": pair_sum_quadratic_zero,
        "support_intersection_by_mixed_status": histogram,
        "individual_move_quadratics": {
            "count": len(individual_quadratics),
            "all_in_jacobian_image": True,
            "coefficients_sha256_512le": fixed_width_digest(individual_quadratics, 512),
            "canonical_preimages_sha256_294le": fixed_width_digest(individual_preimages, 294),
        },
        "digests": {
            "selected_pair_catalog": pair_catalog_digest.hexdigest(),
            "normal_class_sums_sha256_294le": class_sum_digest.hexdigest(),
            "mixed_coefficients_sha256_512le": mixed_digest.hexdigest(),
            "mixed_canonical_preimages_sha256_294le": mixed_preimage_digest.hexdigest(),
            "pair_sum_quadratics_sha256_512le": sum_quadratic_digest.hexdigest(),
            "pair_sum_canonical_preimages_sha256_294le": sum_preimage_digest.hexdigest(),
        },
    }


def skipped_claim(reason: str) -> dict[str, Any]:
    return {"status": "SKIP", "reason": reason}


def catalog_boundary_output() -> dict[str, Any]:
    return {
        "scope": CATALOG_SCOPE,
        "conditioned_on_authenticated_support_artifact": True,
        "support_artifact_path": EXPECTED_INVENTORY["support5_census_artifact"]["path"],
        "exhaustive_five_support_catalog_regenerated": False,
        "statement": CATALOG_BOUNDARY,
    }


def validate_output_contract(result: dict[str, Any], mode: str) -> None:
    require(result.get("schema") == SCHEMA, "output schema id mismatch")
    boundary = result.get("catalog_boundary")
    require(isinstance(boundary, dict) and boundary == catalog_boundary_output(), "output catalog boundary is absent or malformed")
    catalog = result.get("catalog")
    require(isinstance(catalog, dict), "output authenticated catalog record is absent")
    require(catalog.get("scope") == CATALOG_SCOPE, "output catalog scope is not artifact-conditioned")
    require(catalog.get("authenticated_artifact_move_count") == EXPECTED["move_count"], "output authenticated move count changed")
    require(catalog.get("induced_move_pair_count") == EXPECTED["pair_count"], "output induced pair count changed")
    require("move_count" not in catalog and "move_pair_count" not in catalog, "output exposes unscoped catalog counts")
    checks = result.get("checks")
    require(isinstance(checks, dict) and "canonical_move_selection" not in checks, "output exposes unconditional canonical-selection language")
    require(checks.get("manifest_base_revision_object_and_ancestor") == "PASS", "output omits manifest base-revision enforcement")
    claims = result.get("claims")
    require(isinstance(claims, dict), "output claims object is absent")
    for claim in claims.values():
        require(isinstance(claim, dict), "output claim is malformed")
        if claim.get("status") != "SKIP":
            require(claim.get("catalog_scope") == CATALOG_SCOPE, "output claim omits authenticated-catalog scope")
    pair_claim = claims.get("canonical_additive_move_pairs")
    require(isinstance(pair_claim, dict), "output pair claim is absent")
    if pair_claim.get("status") != "SKIP":
        require("complete_catalog_replayed" not in pair_claim and "catalog_pair_count" not in pair_claim, "output exposes unscoped pair-catalog completeness")
        require("complete_authenticated_move_pair_catalog_replayed" in pair_claim, "output omits scoped pair-catalog extent")
    require(mode == result.get("mode"), "output mode mismatch")


def run(mode: str, pair_range_text: str | None) -> dict[str, Any]:
    support_artifact, generic_artifact, fixture_raw, observed_inputs = authenticate_inputs()
    terms = parse_fixture(fixture_raw)
    moves, representative_counts = parse_moves(support_artifact, terms)
    move_catalog = [
        {
            "index": move.index,
            "combinadic_lex_id": move.combinadic_lex_id,
            "support": list(move.support),
            "orientation": move.orientation,
            "labels": list(move.labels),
            "middle_leg": move.middle_leg,
        }
        for move in moves
    ]
    linear_claim, jacobian, image_basis, gauge_basis = replay_linear_structure(terms, moves, generic_artifact)
    linear_claim["paired_T3_directions"].update(representative_counts)
    if mode in ("full", "structure"):
        poles_claim, pole_endpoints = replay_poles(terms, moves, support_artifact)
        blocks_claim = replay_blocks(moves, pole_endpoints)
    else:
        poles_claim = skipped_claim("--mode pairs")
        blocks_claim = skipped_claim("--mode pairs")
    if mode in ("full", "pairs"):
        pair_total = math.comb(len(moves), 2)
        requested_range = parse_pair_range(pair_range_text, pair_total)
        pairs_claim = replay_pairs(terms, moves, jacobian, image_basis, gauge_basis, requested_range)
    else:
        require(pair_range_text is None, "--pair-range cannot be used with --mode structure")
        pairs_claim = skipped_claim("--mode structure")
    claims = {
        "normal_space_span": linear_claim,
        "K3,3_incidence_blocks": blocks_claim,
        "Laurent_pole_leading_three_circuits": poles_claim,
        "canonical_additive_move_pairs": pairs_claim,
    }
    failures = [name for name, claim in claims.items() if claim.get("status") == "FAIL"]
    result = {
        "schema": SCHEMA,
        "mode": mode,
        "coefficient_field": "GF(2)",
        "deterministic": True,
        "read_only": True,
        "catalog_boundary": catalog_boundary_output(),
        "inputs": observed_inputs,
        "catalog": {
            "scope": CATALOG_SCOPE,
            "source": "support5_census_artifact.result.positive_normal_supports",
            "authenticated_artifact_move_count": len(moves),
            "induced_move_pair_count": math.comb(len(moves), 2),
            "authenticated_move_catalog_sha256": sha256_bytes(canonical_json(move_catalog)),
        },
        "claims": claims,
        "checks": {
            "input_authentication": "PASS",
            "fixture_Brent_equations": "PASS",
            "authenticated_artifact_move_reconstruction": "PASS",
            "catalog_scope_boundary": "PASS",
            "manifest_base_revision_object_and_ancestor": "PASS",
            "requested_claim_failures": failures,
        },
        "overall": {
            "status": "PASS" if not failures else "FAIL",
            "all_requested_replays_passed_within_authenticated_catalog": not failures,
            "complete_authenticated_move_pair_catalog_replayed": pairs_claim.get("complete_authenticated_move_pair_catalog_replayed", False),
        },
    }
    validate_output_contract(result, mode)
    result["checks"]["targeted_output_schema_contract"] = "PASS"
    return result


def failure_result(mode: str, error: BaseException) -> dict[str, Any]:
    return {
        "schema": SCHEMA,
        "mode": mode,
        "deterministic": True,
        "read_only": True,
        "catalog_boundary": catalog_boundary_output(),
        "overall": {
            "status": "FAIL",
            "error_type": type(error).__name__,
            "error": str(error),
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="explicitly request the read-only replay (the default action)")
    parser.add_argument("--mode", choices=("full", "structure", "pairs"), default="full", help="full replay, structural claims without pairs, or pair compatibility only")
    parser.add_argument("--pair-range", metavar="START:STOP", help="replay a half-open shard of the lexicographically ordered 1,953-pair catalog induced by the 63 authenticated-artifact moves")
    arguments = parser.parse_args()
    try:
        result = run(arguments.mode, arguments.pair_range)
    except (ReplayFailure, FileNotFoundError, KeyError, OSError, TypeError, ValueError, OverflowError) as error:
        result = failure_result(arguments.mode, error)
    print(json.dumps(result, sort_keys=True, indent=2, ensure_ascii=True))
    return 0 if result.get("overall", {}).get("status") == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
