#!/usr/bin/env python3
"""Verify the rank-49 T4 bundle and optionally replay its four lanes."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import resource
import shlex
import signal
import subprocess
import sys
import tempfile
import time
from typing import Any

MANIFEST_NAME = "manifest.json"
MANIFEST_SCHEMA = "rank49-t4-integration-manifest-v2"
MANIFEST_CANONICALIZATION = "UTF-8 JSON, sort_keys=True, indent=2 for file encoding; compact separators=(',', ':') for payload"
EXPECTED_BASE_REVISION = "6866f8be63692dc918e26d75db9414325b03b78c"
BASE_REVISION_ROLE = "generation base recorded by all lane artifacts; it must exist and be an ancestor of current HEAD"
HEAD_POLICY = "later commits are allowed because every delivered bundle file remains authenticated by size and SHA-256"
SUPPORT_BASE_REVISION_POLICY = "fixed generation base; verified present and ancestor of generation/check HEAD"
GENERIC_BASE_VALIDATION = "must exist and be an ancestor of current HEAD"
FIXTURE_PATH = "Programs/BilinearComplexity/rank49_t4/fixtures/4x4x4_m49_c680_iteration65_Z2.txt"
FIXTURE_SHA256 = "5fc92a6bf83fc29d9527ab100bad5d72d769178b616b31a36c3c0c0b8ad9d09d"
FIXTURE_BYTES = 4716
ORIGINAL_EXTERNAL_LOCATOR = "/home/exedev/x/tensor/data/z2/4x4x4_m49_c680_iteration65_Z2.txt"
STATUS_PASS = "PASS"
STATUS_TIMEOUT = "TIMEOUT"
STATUS_RESOURCE = "RESOURCE_EXCEEDED"
STATUS_FAIL = "FAIL"
STATUS_VALUES = (STATUS_PASS, STATUS_TIMEOUT, STATUS_RESOURCE, STATUS_FAIL)
RESOURCE_MARKERS = (
    b"memoryerror", b"cannot allocate memory", b"cannot reserve memory",
    b"failed to map segment", b"mmap failed", b"out of memory",
    b"std::bad_alloc", b"resource temporarily unavailable", b"virtual memory exhausted",
)
PARAMETER_T3_BINDING = {
    "artifact_file_id": "parameter_orbits_artifact",
    "inventory_id": "paired_circuit_lean",
    "path_pointer": "/provenance/t3_lean_provenance",
    "sha256_pointer": "/provenance/t3_lean_provenance_sha256",
}
EXPECTED_LANES = {
    "support5_census": {
        "argv": ("python3", "Programs/BilinearComplexity/rank49_t4/support5_census.py", "--check", "--quiet"),
        "scripts": ("support5_census_script",),
        "artifacts": {
            "support5_census_artifact": ("json", "rank49-t4-support5-census-v4"),
            "support5_orbits_artifact": ("gzip_jsonl", "rank49-t4-support5-singleton-orbits-v3"),
        },
        "limits": (600, 1024),
    },
    "stabilizer": {
        "argv": ("python3", "Programs/BilinearComplexity/rank49_t4/stabilizer.py", "--check"),
        "scripts": ("stabilizer_script", "stabilizer_replayer"),
        "artifacts": {"stabilizer_artifact": ("json", "proofs.rank49_t4.stabilizer.v2")},
        "limits": (300, 1024),
    },
    "generic_germ": {
        "argv": ("python3", "Programs/BilinearComplexity/rank49_t4/generic_germ.py", "--check"),
        "scripts": ("generic_germ_script",),
        "artifacts": {"generic_germ_artifact": ("json", "BilinearComplexity.rank49_t4.generic_germ.v3")},
        "limits": (600, 2048),
    },
    "parameter_orbits": {
        "argv": ("sage", "Programs/BilinearComplexity/rank49_t4/parameter_orbits.sage", "--", "--check"),
        "scripts": ("parameter_orbits_script",),
        "artifacts": {"parameter_orbits_artifact": ("json", "rank49-t4-parameter-orbits-v2")},
        "limits": (60, 4096),
    },
}


class CheckError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CheckError(message)


def reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise CheckError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def load_json_bytes(data: bytes, label: str) -> dict[str, Any]:
    try:
        value = json.loads(data.decode("utf-8"), object_pairs_hook=reject_duplicate_keys)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise CheckError(f"invalid JSON in {label}: {error}") from error
    require(isinstance(value, dict), f"{label} is not a JSON object")
    return value


def canonical_compact(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def canonical_pretty(value: Any) -> bytes:
    return (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=True) + "\n").encode("utf-8")


def canonical_stabilizer(value: Any) -> bytes:
    return (json.dumps(value, sort_keys=True, indent=2, separators=(",", ": ")) + "\n").encode("utf-8")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def hash_file(path: Path) -> tuple[str, int]:
    digest = hashlib.sha256()
    size = 0
    with path.open("rb") as stream:
        while block := stream.read(1024 * 1024):
            digest.update(block)
            size += len(block)
    return digest.hexdigest(), size


def get_pointer(value: Any, pointer: str) -> Any:
    require(isinstance(pointer, str) and pointer.startswith("/"), f"invalid JSON pointer {pointer!r}")
    current = value
    for raw_part in pointer.split("/")[1:]:
        part = raw_part.replace("~1", "/").replace("~0", "~")
        require(isinstance(current, dict) and part in current, f"missing JSON pointer {pointer!r}")
        current = current[part]
    return current


def repository_root() -> Path:
    return Path(__file__).resolve().parents[3]


def authenticate_manifest(root: Path) -> tuple[dict[str, Any], dict[str, dict[str, Any]], str]:
    manifest_path = Path(__file__).resolve().with_name(MANIFEST_NAME)
    raw = manifest_path.read_bytes()
    manifest = load_json_bytes(raw, str(manifest_path))
    require(raw == canonical_pretty(manifest), "manifest is not canonical pretty JSON")
    require(manifest.get("schema") == MANIFEST_SCHEMA, "manifest schema mismatch")
    authentication = manifest.get("authentication")
    require(isinstance(authentication, dict), "manifest authentication is absent")
    require(authentication.get("algorithm") == "SHA-256", "manifest authentication algorithm mismatch")
    require(authentication.get("canonicalization") == MANIFEST_CANONICALIZATION, "manifest canonicalization mismatch")
    require(authentication.get("scope") == "all top-level fields except authentication.payload_sha256", "manifest authentication scope mismatch")
    payload = copy.deepcopy(manifest)
    payload_authentication = payload.get("authentication")
    require(isinstance(payload_authentication, dict), "manifest authentication is malformed")
    recorded_payload_hash = payload_authentication.pop("payload_sha256", None)
    require(isinstance(recorded_payload_hash, str), "manifest payload hash is absent")
    actual_payload_hash = sha256_bytes(canonical_compact(payload))
    require(recorded_payload_hash == actual_payload_hash, f"manifest payload SHA-256 mismatch: recorded={recorded_payload_hash} actual={actual_payload_hash}")

    repository = manifest.get("repository")
    require(isinstance(repository, dict), "manifest repository record is absent")
    require(repository.get("root_resolution") == "resolve check_all.py and take parents[3]", "repository root-resolution declaration mismatch")
    base_revision = repository.get("base_git_revision")
    require(base_revision == EXPECTED_BASE_REVISION, "manifest generation base revision mismatch")
    require(repository.get("base_revision_role") == BASE_REVISION_ROLE, "generation base revision role mismatch")
    require(repository.get("head_policy") == HEAD_POLICY, "repository HEAD policy mismatch")
    require(root == Path(__file__).resolve().parents[3], "derived repository root mismatch")
    base_exists = subprocess.run(
        ["git", "-C", str(root), "cat-file", "-e", f"{base_revision}^{{commit}}"], check=False,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
    )
    require(base_exists.returncode == 0, f"recorded generation base revision does not exist: {base_exists.stderr.strip()}")
    revision = subprocess.run(
        ["git", "-C", str(root), "rev-parse", "--verify", "HEAD^{commit}"], check=False,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
    )
    require(revision.returncode == 0, f"cannot read current HEAD: {revision.stderr.strip()}")
    current_head = revision.stdout.strip()
    ancestry = subprocess.run(
        ["git", "-C", str(root), "merge-base", "--is-ancestor", base_revision, current_head], check=False,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
    )
    require(
        ancestry.returncode == 0,
        f"recorded generation base {base_revision} is not an ancestor of current HEAD {current_head}"
        if ancestry.returncode == 1
        else f"cannot verify generation-base ancestry: {ancestry.stderr.strip()}",
    )

    source = manifest.get("source")
    require(isinstance(source, dict), "manifest source record is absent")
    require(source.get("runtime_fixture_inventory_id") == "canonical_fixture", "runtime fixture inventory id mismatch")
    require(source.get("original_external_locator") == ORIGINAL_EXTERNAL_LOCATOR, "original external locator provenance mismatch")
    require(source.get("original_external_locator_role") == "provenance only; never opened by integration or lane checkers", "external locator role mismatch")
    scope = manifest.get("scope")
    require(isinstance(scope, dict), "manifest scope record is absent")
    require(scope.get("status_values") == list(STATUS_VALUES), "manifest status values mismatch")

    records = manifest.get("files")
    require(isinstance(records, list) and records, "manifest file inventory is absent")
    by_id: dict[str, dict[str, Any]] = {}
    seen_paths: set[str] = set()
    for record in records:
        require(isinstance(record, dict), "manifest file record is not an object")
        file_id = record.get("id")
        path_text = record.get("path")
        require(isinstance(file_id, str) and file_id and file_id not in by_id, f"duplicate or invalid file id {file_id!r}")
        require(isinstance(path_text, str) and path_text and path_text not in seen_paths, f"duplicate or invalid file path {path_text!r}")
        require(record.get("location") == "repository", f"nonrepository runtime inventory entry {file_id!r}")
        relative = Path(path_text)
        require(not relative.is_absolute() and ".." not in relative.parts, f"unsafe repository path: {path_text}")
        path = root / relative
        require(path.resolve().is_relative_to(root), f"repository path escapes root: {path_text}")
        require(path.is_file(), f"manifested file is absent: {path_text}")
        actual_hash, actual_size = hash_file(path)
        require(actual_hash == record.get("sha256"), f"file SHA-256 mismatch for {file_id}: recorded={record.get('sha256')} actual={actual_hash}")
        require(actual_size == record.get("bytes"), f"file size mismatch for {file_id}: recorded={record.get('bytes')} actual={actual_size}")
        normalized = dict(record)
        normalized["resolved_path"] = str(path.resolve())
        by_id[file_id] = normalized
        seen_paths.add(path_text)

    fixture = by_id.get("canonical_fixture")
    require(isinstance(fixture, dict), "vendored canonical fixture record is absent")
    require(fixture.get("path") == FIXTURE_PATH, "vendored fixture path mismatch")
    require(fixture.get("sha256") == FIXTURE_SHA256, "vendored fixture digest mismatch")
    require(fixture.get("bytes") == FIXTURE_BYTES, "vendored fixture byte count mismatch")
    return manifest, by_id, current_head


def authenticate_cross_references(manifest: dict[str, Any], files: dict[str, dict[str, Any]], root: Path) -> None:
    lanes = manifest.get("lanes")
    require(isinstance(lanes, list) and len(lanes) == len(EXPECTED_LANES), "manifest must declare exactly four lanes")
    lane_names = [lane.get("name") for lane in lanes if isinstance(lane, dict)]
    require(lane_names == list(EXPECTED_LANES), "manifest lane order or set mismatch")
    base_revision = manifest["repository"]["base_git_revision"]
    fixture = files["canonical_fixture"]
    fixture_path = fixture["path"]
    fixture_hash = fixture["sha256"]
    loaded: dict[str, dict[str, Any]] = {}
    deferred_schemas: list[tuple[str, str, str]] = []

    for lane in lanes:
        require(isinstance(lane, dict), "lane record is not an object")
        lane_name = lane.get("name")
        expected = EXPECTED_LANES[lane_name]
        require(lane.get("randomness") == {"used": False, "seeds": []}, f"randomness declaration mismatch in {lane_name}")
        require(lane.get("runtime_inputs") == ["canonical_fixture"], f"runtime input declaration mismatch in {lane_name}")
        scripts = lane.get("scripts")
        require(isinstance(scripts, list) and tuple(scripts) == expected["scripts"], f"script declaration mismatch in {lane_name}")
        for script_id in scripts:
            require(script_id in files, f"unknown script inventory id {script_id!r}")
        command = lane.get("acceptance_checker")
        require(isinstance(command, dict), f"acceptance checker missing in {lane_name}")
        require(command.get("working_directory") == "repository root", f"working directory declaration mismatch in {lane_name}")
        argv = command.get("argv")
        require(isinstance(argv, list) and tuple(argv) == expected["argv"], f"checker argv mismatch in {lane_name}")
        require(command.get("shell_command") == shlex.join(argv), f"shell command/argv mismatch in {lane_name}")
        require(argv[1] == files[scripts[0]]["path"], f"checker script path mismatch in {lane_name}")
        limits = command.get("enforced_limits")
        expected_wall, expected_memory = expected["limits"]
        require(
            isinstance(limits, dict) and limits.get("wall_seconds") == expected_wall
            and limits.get("memory_mib") == expected_memory
            and isinstance(limits.get("method"), str) and limits["method"],
            f"invalid or unexpected enforced limits in {lane_name}",
        )
        completion = lane.get("expected_completion")
        require(isinstance(completion, dict) and completion.get("status") == STATUS_PASS, f"expected completion mismatch in {lane_name}")
        artifacts = lane.get("artifacts")
        require(isinstance(artifacts, list), f"artifact list missing in {lane_name}")
        artifact_ids = [item.get("file_id") for item in artifacts if isinstance(item, dict)]
        require(len(artifact_ids) == len(artifacts) and set(artifact_ids) == set(expected["artifacts"]), f"artifact set mismatch in {lane_name}")
        for artifact in artifacts:
            file_id = artifact.get("file_id")
            require(file_id in files, f"unknown artifact inventory id {file_id!r}")
            artifact_format = artifact.get("format")
            artifact_schema = artifact.get("schema")
            require((artifact_format, artifact_schema) == expected["artifacts"][file_id], f"artifact format/schema mismatch for {file_id}")
            if artifact_format == "json":
                pointer = artifact.get("schema_pointer")
                path = Path(files[file_id]["resolved_path"])
                value = load_json_bytes(path.read_bytes(), str(path))
                loaded[file_id] = value
                require(get_pointer(value, pointer) == artifact_schema, f"artifact schema mismatch for {file_id}")
            elif artifact_format == "gzip_jsonl":
                schema_source = artifact.get("schema_source")
                require(isinstance(schema_source, str), f"schema source missing for {file_id}")
                source_id, separator, pointer = schema_source.partition(":")
                require(bool(separator) and source_id and pointer.startswith("/"), f"invalid schema source for {file_id}")
                deferred_schemas.append((source_id, pointer, artifact_schema))
            else:
                raise CheckError(f"unsupported artifact format {artifact_format!r}")
        if lane_name == "parameter_orbits":
            require(lane.get("provenance_inputs") == ["paired_circuit_lean"], "parameter provenance inventory id mismatch")
            require(lane.get("cross_bindings") == [PARAMETER_T3_BINDING], "parameter T3 cross-binding declaration mismatch")
        else:
            require(lane.get("provenance_inputs", []) == [], f"unexpected provenance input in {lane_name}")
            require(lane.get("cross_bindings", []) == [], f"unexpected cross-binding in {lane_name}")

    for source_id, pointer, schema in deferred_schemas:
        require(source_id in loaded, f"schema source artifact is not loaded: {source_id}")
        require(get_pointer(loaded[source_id], pointer) == schema, f"stream schema metadata mismatch from {source_id}{pointer}")

    support = loaded["support5_census_artifact"]
    support_script = files["support5_census_script"]
    support_orbits = files["support5_orbits_artifact"]
    require(support["generator"]["script_path"] == support_script["path"], "support script path cross-binding mismatch")
    require(support["generator"]["script_sha256"] == support_script["sha256"], "support script digest cross-binding mismatch")
    require(support["generator"]["fixture_path"] == fixture_path, "support fixture path cross-binding mismatch")
    require(support["generator"]["fixture_sha256"] == fixture_hash, "support fixture digest cross-binding mismatch")
    support_command = next(lane for lane in manifest["lanes"] if lane["name"] == "support5_census")["acceptance_checker"]["shell_command"]
    require(support["generator"]["check_command"] == support_command, "support internal check command mismatch")
    support_result = support["result"]
    require(support_result["source"]["fixture_path"] == fixture_path, "support source fixture path mismatch")
    require(support_result["source"]["sha256"] == fixture_hash, "support source fixture digest mismatch")
    require(support_result["source"]["external_provenance_locator_opened"] is False, "support external locator must be provenance-only")
    require(support_result["provenance"]["base_revision"] == base_revision, "support base-revision mismatch")
    require(support_result["provenance"]["base_revision_policy"] == SUPPORT_BASE_REVISION_POLICY, "support generation-base policy mismatch")
    require(support_result["provenance"]["exact_check_command"] == support_command, "support provenance check command mismatch")
    require(support_result["provenance"]["owned_code_sha256"] == {support_script["path"]: support_script["sha256"]}, "support owned-code map mismatch")
    orbit = support_result["singleton_orbit_records"]
    require(orbit["relative_path"] == support_orbits["path"], "support orbit path cross-binding mismatch")
    require(orbit["compressed_sha256"] == support_orbits["sha256"], "support orbit digest cross-binding mismatch")
    require(orbit["compressed_byte_count"] == support_orbits["bytes"], "support orbit byte-count cross-binding mismatch")
    require(orbit["content_addressing"] == {"algorithm": "sha256", "digest_of": "complete deterministic gzip bytes", "immutable_filename": True}, "support orbit content-addressing policy mismatch")
    require(Path(orbit["relative_path"]).name == f"support5_orbits-{orbit['compressed_sha256']}.jsonl.gz", "support orbit filename is not its payload digest")
    certificate = support_result["census_content_certificate"]
    require(sha256_bytes(canonical_compact(certificate["content"])) == certificate["content_sha256"], "support certificate content digest mismatch")
    require(certificate["content"]["fixture_path"] == fixture_path, "support certificate fixture path mismatch")
    require(certificate["content"]["source_sha256"] == fixture_hash, "support certificate fixture digest mismatch")
    require(certificate["content"]["base_revision"] == base_revision, "support certificate generation-base mismatch")
    require(certificate["content"]["base_revision_policy"] == SUPPORT_BASE_REVISION_POLICY, "support certificate generation-base policy mismatch")

    stabilizer = loaded["stabilizer_artifact"]
    producer = stabilizer["provenance"]["producer"]
    source = stabilizer["provenance"]["source"]
    require(producer["base_git_revision"] == base_revision, "stabilizer base-revision mismatch")
    require(source["fixture_repository_relative_path"] == fixture_path, "stabilizer fixture path mismatch")
    require(source["canonical_path"] == fixture_path, "stabilizer canonical fixture path mismatch")
    require(source["sha256"] == fixture_hash, "stabilizer fixture digest mismatch")
    require("provenance only" in source["original_external_locator_usage"], "stabilizer external locator is not provenance-only")
    stabilizer_command = next(lane for lane in manifest["lanes"] if lane["name"] == "stabilizer")["acceptance_checker"]["shell_command"]
    require(producer["commands"]["producer_check_plus_independent_replay"] == stabilizer_command, "stabilizer internal check command mismatch")
    owned = producer["current_owned_code_file_hashes"]
    require(owned == {
        files["stabilizer_script"]["path"]: files["stabilizer_script"]["sha256"],
        files["stabilizer_replayer"]["path"]: files["stabilizer_replayer"]["sha256"],
    }, "stabilizer owned-code map mismatch")
    require(sha256_bytes(canonical_stabilizer(stabilizer["certificate_payload"])) == stabilizer["certificate_payload_sha256"], "stabilizer certificate payload digest mismatch")

    germ = loaded["generic_germ_artifact"]
    germ_source = germ["provenance"]["source_fixture"]
    require(germ["provenance"]["repository"]["base_git_revision"] == base_revision, "generic-germ base-revision mismatch")
    require(germ["provenance"]["repository"]["base_validation"] == GENERIC_BASE_VALIDATION, "generic-germ generation-base policy mismatch")
    require(germ_source["repository_path"] == fixture_path, "generic-germ fixture path mismatch")
    require(germ_source["sha256"] == fixture_hash and germ_source["bytes"] == fixture["bytes"], "generic-germ fixture content mismatch")
    require(germ["provenance"]["original_external_locator"]["accessed"] is False, "generic-germ external locator must not be accessed")
    germ_command = next(lane for lane in manifest["lanes"] if lane["name"] == "generic_germ")["acceptance_checker"]["shell_command"]
    require(germ["provenance"]["commands"]["check"] == germ_command, "generic-germ internal check command mismatch")
    require(germ["provenance"]["owned_script"]["repository_path"] == files["generic_germ_script"]["path"], "generic-germ script path mismatch")
    require(germ["provenance"]["owned_script"]["sha256"] == files["generic_germ_script"]["sha256"], "generic-germ script digest mismatch")
    germ_payload = {key: value for key, value in germ.items() if key != "authentication"}
    require(sha256_bytes(canonical_compact(germ_payload)) == germ["authentication"]["payload_sha256"], "generic-germ payload digest mismatch")
    require(canonical_pretty(germ) == Path(files["generic_germ_artifact"]["resolved_path"]).read_bytes(), "generic-germ artifact encoding mismatch")

    parameter = loaded["parameter_orbits_artifact"]
    provenance = parameter["provenance"]
    require(provenance["base_git_revision"] == base_revision, "parameter base-revision mismatch")
    require(provenance["canonical_source_fixture"] == fixture_path, "parameter fixture path mismatch")
    require(provenance["canonical_source_fixture_sha256"] == fixture_hash, "parameter fixture digest mismatch")
    require(provenance["runtime_file_inputs"] == [fixture_path], "parameter runtime input mismatch")
    require(provenance["original_external_source_runtime_dependency"] is False, "parameter external source must not be a runtime dependency")
    parameter_command = next(lane for lane in manifest["lanes"] if lane["name"] == "parameter_orbits")["acceptance_checker"]["shell_command"]
    require(provenance["check_command"] == parameter_command, "parameter internal check command mismatch")
    require(provenance["checker"] == files["parameter_orbits_script"]["path"], "parameter checker path mismatch")
    require(provenance["checker_sha256"] == files["parameter_orbits_script"]["sha256"], "parameter checker digest mismatch")
    paired = files[PARAMETER_T3_BINDING["inventory_id"]]
    require(get_pointer(parameter, PARAMETER_T3_BINDING["path_pointer"]) == paired["path"], "parameter T3 Lean provenance path is not bound to inventory")
    require(get_pointer(parameter, PARAMETER_T3_BINDING["sha256_pointer"]) == paired["sha256"], "parameter T3 Lean provenance digest is not bound to inventory")


def process_group_pids(group_id: int) -> set[int]:
    members: set[int] = set()
    try:
        entries = tuple(Path("/proc").iterdir())
    except OSError:
        return members
    for entry in entries:
        if not entry.name.isdigit():
            continue
        try:
            suffix = (entry / "stat").read_text(encoding="ascii").rsplit(")", 1)[1].split()
            if len(suffix) > 2 and int(suffix[2]) == group_id:
                members.add(int(entry.name))
        except (FileNotFoundError, ProcessLookupError, PermissionError, OSError, ValueError, IndexError):
            continue
    return members


def rss_bytes(pid: int) -> int:
    try:
        for line in Path(f"/proc/{pid}/status").read_text(encoding="ascii").splitlines():
            if line.startswith("VmRSS:"):
                return int(line.split()[1]) * 1024
    except (FileNotFoundError, ProcessLookupError, PermissionError, ValueError):
        return 0
    return 0


def terminate_group(group_id: int) -> None:
    try:
        os.killpg(group_id, signal.SIGTERM)
    except ProcessLookupError:
        return
    deadline = time.monotonic() + 2.0
    while time.monotonic() < deadline:
        try:
            os.killpg(group_id, 0)
        except ProcessLookupError:
            return
        time.sleep(0.05)
    try:
        os.killpg(group_id, signal.SIGKILL)
    except ProcessLookupError:
        pass


def limit_child(memory_bytes: int) -> None:
    resource.setrlimit(resource.RLIMIT_AS, (memory_bytes, memory_bytes))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def classify_failure(returncode: int, output: bytes, peak_rss: int, memory_bytes: int) -> str:
    lowered = output.lower()
    if any(marker in lowered for marker in RESOURCE_MARKERS):
        return STATUS_RESOURCE
    if returncode in (-signal.SIGXCPU, -signal.SIGXFSZ):
        return STATUS_RESOURCE
    if returncode == -signal.SIGKILL and peak_rss >= int(memory_bytes * 0.9):
        return STATUS_RESOURCE
    return STATUS_FAIL


def run_lane(lane: dict[str, Any], root: Path) -> dict[str, Any]:
    checker = lane["acceptance_checker"]
    argv = checker["argv"]
    limits = checker["enforced_limits"]
    wall_seconds = limits["wall_seconds"]
    memory_bytes = limits["memory_mib"] * 1024 * 1024
    started = time.monotonic()
    timed_out = False
    memory_exceeded = False
    peak_rss = 0
    with tempfile.TemporaryFile() as stdout_file, tempfile.TemporaryFile() as stderr_file:
        try:
            process = subprocess.Popen(
                argv, cwd=root, stdin=subprocess.DEVNULL, stdout=stdout_file, stderr=stderr_file,
                start_new_session=True, preexec_fn=lambda: limit_child(memory_bytes),
            )
        except (OSError, ValueError) as error:
            return {
                "lane": lane["name"], "status": STATUS_FAIL, "returncode": None,
                "elapsed_seconds": time.monotonic() - started, "peak_rss_mib": 0.0,
                "error": str(error), "stdout": b"", "stderr": b"",
            }
        while True:
            returncode = process.poll()
            group_pids = process_group_pids(process.pid)
            if returncode is not None and not group_pids:
                break
            elapsed = time.monotonic() - started
            current_rss = sum(rss_bytes(pid) for pid in group_pids)
            peak_rss = max(peak_rss, current_rss)
            if current_rss > memory_bytes:
                memory_exceeded = True
                terminate_group(process.pid)
                break
            if elapsed > wall_seconds:
                timed_out = True
                terminate_group(process.pid)
                break
            time.sleep(0.1)
        returncode = process.wait()
        peak_rss = max(peak_rss, sum(rss_bytes(pid) for pid in process_group_pids(process.pid)))
        stdout_file.seek(0)
        stderr_file.seek(0)
        stdout = stdout_file.read()
        stderr = stderr_file.read()
    if timed_out:
        status = STATUS_TIMEOUT
    elif memory_exceeded:
        status = STATUS_RESOURCE
    elif returncode == 0:
        status = STATUS_PASS
    else:
        status = classify_failure(returncode, stdout + b"\n" + stderr, peak_rss, memory_bytes)
    return {
        "lane": lane["name"], "status": status, "returncode": returncode,
        "elapsed_seconds": time.monotonic() - started,
        "peak_rss_mib": peak_rss / (1024 * 1024), "error": None,
        "stdout": stdout, "stderr": stderr,
    }


def print_lane_result(result: dict[str, Any]) -> None:
    print(
        f"[{result['lane']}] {result['status']} returncode={result['returncode']} "
        f"elapsed_seconds={result['elapsed_seconds']:.3f} peak_rss_mib={result['peak_rss_mib']:.3f}"
    )
    if result.get("error"):
        print(result["error"], file=sys.stderr)
    stdout = result.get("stdout", b"")
    stderr = result.get("stderr", b"")
    if stdout:
        print(f"--- {result['lane']} stdout ---")
        sys.stdout.flush()
        sys.stdout.buffer.write(stdout)
        if not stdout.endswith(b"\n"):
            sys.stdout.buffer.write(b"\n")
        sys.stdout.flush()
    if stderr:
        print(f"--- {result['lane']} stderr ---", file=sys.stderr)
        sys.stderr.flush()
        sys.stderr.buffer.write(stderr)
        if not stderr.endswith(b"\n"):
            sys.stderr.buffer.write(b"\n")
        sys.stderr.flush()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--quick", action="store_true", help="verify inventory, fixture, schemas, payloads, and cross-bindings without recomputation")
    mode.add_argument("--full", action="store_true", help="perform quick verification and run all four deterministic acceptance checkers under limits")
    arguments = parser.parse_args()
    root = repository_root()
    try:
        manifest, files, current_head = authenticate_manifest(root)
        authenticate_cross_references(manifest, files, root)
    except (CheckError, FileNotFoundError, KeyError, OSError, subprocess.SubprocessError, TypeError, ValueError, AttributeError) as error:
        print(f"[authentication] {STATUS_FAIL}: {error}", file=sys.stderr)
        return 1
    print(
        f"[authentication] {STATUS_PASS} files={len(files)} "
        f"manifest_payload_sha256={manifest['authentication']['payload_sha256']} "
        f"generation_base_revision={manifest['repository']['base_git_revision']} "
        f"current_head={current_head}"
    )
    if arguments.quick:
        print(f"[overall] {STATUS_PASS} mode=quick acceptance_checkers_run=0")
        return 0
    results = []
    for lane in manifest["lanes"]:
        result = run_lane(lane, root)
        results.append(result)
        print_lane_result(result)
    counts = {status: sum(result["status"] == status for result in results) for status in STATUS_VALUES}
    overall = STATUS_PASS if counts[STATUS_PASS] == len(results) else STATUS_FAIL
    print(
        f"[overall] {overall} mode=full lanes={len(results)} "
        f"PASS={counts[STATUS_PASS]} TIMEOUT={counts[STATUS_TIMEOUT]} "
        f"RESOURCE_EXCEEDED={counts[STATUS_RESOURCE]} FAIL={counts[STATUS_FAIL]}"
    )
    return 0 if overall == STATUS_PASS else 1


if __name__ == "__main__":
    raise SystemExit(main())
