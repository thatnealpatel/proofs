"""Static validator for the authenticated c659 inverse-Plus oracle artifact."""

import argparse
import hashlib
import itertools
import json
import os
import stat
import struct
import sys


SCRIPT_ID = "Programs/BilinearComplexity/c659_fixed_child_inverse_plus_oracle.sage"
ARTIFACT_ID = "Programs/BilinearComplexity/c659_fixed_child_inverse_plus_oracle.json"
ROOT_ID = "cmd/c659-plusflip-cert/testdata/4x4x4_m47_c659_iteration5551_Z2.txt"
SCHEMA = "c659-fixed-child-inverse-plus-oracle-v3"
PINNED_SAGE_BYTES = 43716
PINNED_ARTIFACT_BYTES = 206895
PINNED_ROOT_RAW_BYTES = 4524
PINNED_SAGE_SHA256 = "1dd78a71e4206936656e542d6b4c1f8e347f4c647dd77cfb25d68178dec61f8e"
PINNED_ARTIFACT_SHA256 = "9616ca07d92a9fe70ae8a522bb13cd46bf9d77ea5f61b658beda8840a9b7e553"
PINNED_ROOT_RAW_SHA256 = "25f47b5f37d2b7351dd5a2c5da65ff8ef5ba80ce53239d46cdfdef37e6eef403"
PINNED_ROOT_ORDERED_SHA256 = "f61518b4864995fe5ba43f1b52819cc563c4c74326442ae12bbc338a491027cb"
PINNED_ROOT_UNORDERED_SHA256 = "f2edf6735401e203b532cc85e0783fb47684815a3207b3ec601f8503c48956d1"
PINNED_TENSOR_SHA256 = "1ae43419be8f86b7063141475bb207725b43bc4d1c6cae2c11a948b7359863bd"
PINNED_CHILD_ORDERED_SHA256 = "913109f1ab4662db336696a853ecb5bf77f60ea5a0b051117c4359469660e24a"
PINNED_CHILD_UNORDERED_SHA256 = "0001430818e501c6964f6bf666e52a72cd0514605b3c69460e0d09cf80ec48e9"
FORWARD_METHOD_LABEL = "plus_three_term_identity_gf2_v1"
INVERSE_METHOD_LABEL = "closed_form_first_two_outputs_then_all_named_equations_v1"
ACCEPTED_CLASS = "accepted_exact_parent_lineage"
REJECTED_CLASS = "inverse_equation_inconsistent"
ORIENTATIONS = (
    ("ijk", (0, 1, 2)),
    ("ikj", (0, 2, 1)),
    ("jik", (1, 0, 2)),
    ("jki", (1, 2, 0)),
    ("kij", (2, 0, 1)),
    ("kji", (2, 1, 0)),
)
FORMULAS = {
    "0": "(a1,b1+b2,c1);(a1+a2,b2,c2);(a1,b2,c1+c2)",
    "1": "(a1,b1,c1+c2);(a2,b1+b2,c2);(a1+a2,b1,c2)",
    "2": "(a1+a2,b1,c1);(a2,b2,c1+c2);(a2,b1+b2,c1)",
}
EQUATION_NAMES = {
    0: (
        "output0.factor_i=a1", "output0.factor_j=b1+b2", "output0.factor_k=c1",
        "output1.factor_i=a1+a2", "output1.factor_j=b2", "output1.factor_k=c2",
        "output2.factor_i=a1", "output2.factor_j=b2", "output2.factor_k=c1+c2",
    ),
    1: (
        "output0.factor_i=a1", "output0.factor_j=b1", "output0.factor_k=c1+c2",
        "output1.factor_i=a2", "output1.factor_j=b1+b2", "output1.factor_k=c2",
        "output2.factor_i=a1+a2", "output2.factor_j=b1", "output2.factor_k=c2",
    ),
    2: (
        "output0.factor_i=a1+a2", "output0.factor_j=b1", "output0.factor_k=c1",
        "output1.factor_i=a2", "output1.factor_j=b2", "output1.factor_k=c1+c2",
        "output2.factor_i=a2", "output2.factor_j=b1+b2", "output2.factor_k=c1",
    ),
}
ACCEPTED_FULL_SEMANTIC_COORDINATES = (
    (0, 2, 46, 45, 47),
    (1, 0, 45, 46, 47),
    (2, 1, 45, 46, 47),
    (3, 1, 46, 45, 47),
    (4, 0, 46, 45, 47),
    (5, 2, 45, 46, 47),
)
ACCEPTED_COMPACT_DESCRIPTORS = (
    (46, 45, 0, 2),
    (45, 46, 1, 0),
    (45, 46, 2, 1),
    (46, 45, 3, 1),
    (46, 45, 4, 0),
    (45, 46, 5, 2),
)
EXPECTED_COUNTS = {
    "descriptor_total_count": 108,
    "accepted_descriptor_count": 6,
    "rejected_descriptor_count": 102,
    "inverse_equation_consistent_count": 6,
    "inverse_equation_inconsistent_count": 102,
    "accepted_exact_parent_lineage_count": 6,
    "accepted_alternate_exact_parent_count": 0,
    "accepted_local_tensor_replay_count": 6,
    "accepted_scatter_fixed_child_replay_count": 6,
    "accepted_parent_tensor_replay_count": 6,
    "accepted_parent_nonzero_count": 6,
    "accepted_parent_complete_term_distinct_count": 6,
    "accepted_source_precondition_legal_count": 6,
    "accepted_unique_reconstructed_parent_ordered_payload_count": 2,
    "accepted_unique_reconstructed_parent_unordered_payload_count": 1,
    "accepted_unique_reconstructed_source_pair_ordered_count": 2,
}
EXPECTED_STREAMS = {
    "compact_descriptor_streams": {
        "encoding": "canonical ASCII [slotX,slotY,orientationIndex,variant] plus LF per descriptor; slotZ/formula output 2 is the remaining member of {45,46,47}",
        "all_bytes": 1296,
        "all_sha256": "e05ef47fc81d499b850748e1c1193280fd622c257b5a82ac5487491175cf4d94",
        "accepted_bytes": 72,
        "accepted_sha256": "73fbb5130da5027c305ea14a8e18815d01fc8c7e7413737c69c8337bf330b5fc",
    },
    "full_semantic_record_streams": {
        "encoding": "one complete canonical JSON semantic record plus LF, in descriptor enumeration order",
        "all_bytes": 171217,
        "all_sha256": "85578bcb1f46796677c62c97261c6724ebd8b4f21424e63dbaaacac87569e48d",
        "accepted_bytes": 65038,
        "accepted_sha256": "c2e1d98c809cc14f6a0c00e5b755f6a8fafe1e5b2a9fb2dbb0f3c04a2c86e1f0",
    },
}
EXPECTED_DEDUPLICATION = {
    "domain": "the six accepted semantic records, retaining multiplicity before unique-key counting",
    "accepted_record_count_before_deduplication": 6,
    "reconstructed_parent_ordered_key": "ordered factor-major binary payload including header",
    "reconstructed_parent_unordered_key": "lexicographically sorted complete-term binary payload including header",
    "reconstructed_source_pair_ordered_key": "ordered pair of three-factor source terms",
}


class ValidationError(Exception):
    pass


def check(condition, message):
    if not condition:
        raise ValidationError(message)


def sha256(value):
    return hashlib.sha256(value).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii")


def read_regular(path, role, expected_bytes):
    path_metadata = os.lstat(path)
    check(stat.S_ISREG(path_metadata.st_mode), "%s must be a regular non-symlink file: %s" % (role, path))
    flags = os.O_RDONLY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(path, flags)
    with os.fdopen(descriptor, "rb") as source:
        metadata = os.fstat(source.fileno())
        check(stat.S_ISREG(metadata.st_mode), "%s must be a regular non-symlink file: %s" % (role, path))
        check((metadata.st_dev, metadata.st_ino) == (path_metadata.st_dev, path_metadata.st_ino), "%s changed between lstat and open: %s" % (role, path))
        check(metadata.st_size == expected_bytes, "%s has %d bytes, expected exactly %d" % (role, metadata.st_size, expected_bytes))
        value = source.read(expected_bytes + 1)
    check(len(value) >= expected_bytes, "%s short read: got %d bytes, expected exactly %d" % (role, len(value), expected_bytes))
    check(len(value) <= expected_bytes, "%s extra read: got more than the expected %d bytes" % (role, expected_bytes))
    return value


def parse_root(raw):
    check(len(raw) == PINNED_ROOT_RAW_BYTES and sha256(raw) == PINNED_ROOT_RAW_SHA256, "root raw byte authentication failed")
    lines = raw.decode("ascii").splitlines()
    check(len(lines) == 4 and lines[0].split() == ["4", "4", "4", "47"], "root native header failed")
    factors = []
    for line in lines[1:]:
        tokens = line.split()
        check(len(tokens) == 47 * 16 and all(token in ("0", "1") for token in tokens), "root factor payload failed")
        factors.append([sum(int(tokens[slot * 16 + bit]) << bit for bit in range(16)) for slot in range(47)])
    return tuple(tuple(factors[mode][slot] for mode in range(3)) for slot in range(47))


def outer_tensor(term):
    value = 0
    for first in range(16):
        if term[0] & (1 << first):
            for second in range(16):
                if term[1] & (1 << second):
                    for third in range(16):
                        if term[2] & (1 << third):
                            value |= 1 << ((first * 16 + second) * 16 + third)
    return value


def tensor(terms):
    value = 0
    for term in terms:
        value ^= outer_tensor(term)
    return value


def multiplication_tensor():
    value = 0
    for i in range(4):
        for j in range(4):
            for k in range(4):
                value |= 1 << ((((4 * i + j) * 16) + (4 * j + k)) * 16 + (4 * k + i))
    return value


def ordered_bytes(terms):
    return struct.pack("<4H", 4, 4, 4, len(terms)) + b"".join(struct.pack("<H", term[mode]) for mode in range(3) for term in terms)


def unordered_bytes(terms):
    return struct.pack("<4H", 4, 4, 4, len(terms)) + b"".join(struct.pack("<HHH", *term) for term in sorted(terms))


def plus_local(first, second, positions, variant):
    i, j, k = positions
    a1, b1, c1 = first[i], first[j], first[k]
    a2, b2, c2 = second[i], second[j], second[k]
    if variant == 0:
        oriented = ((a1, b1 ^ b2, c1), (a1 ^ a2, b2, c2), (a1, b2, c1 ^ c2))
    elif variant == 1:
        oriented = ((a1, b1, c1 ^ c2), (a2, b1 ^ b2, c2), (a1 ^ a2, b1, c2))
    else:
        oriented = ((a1 ^ a2, b1, c1), (a2, b2, c1 ^ c2), (a2, b1 ^ b2, c1))
    result = []
    for oriented_term in oriented:
        term = [0, 0, 0]
        term[i], term[j], term[k] = oriented_term
        result.append(tuple(term))
    return tuple(result)


def inverse_plus(outputs, positions, variant):
    oriented_outputs = tuple(tuple(term[position] for position in positions) for term in outputs)
    first_output, second_output, actual_third = oriented_outputs
    if variant == 0:
        a1, b2, c1 = first_output[0], second_output[1], first_output[2]
        a2, b1, c2 = second_output[0] ^ a1, first_output[1] ^ b2, second_output[2]
    elif variant == 1:
        a1, b1, c2 = first_output[0], first_output[1], second_output[2]
        c1, a2, b2 = first_output[2] ^ c2, second_output[0], second_output[1] ^ b1
    else:
        a2, b1, c1 = second_output[0], first_output[1], first_output[2]
        a1, b2, c2 = first_output[0] ^ a2, second_output[1], second_output[2] ^ c1
    oriented_sources = ((a1, b1, c1), (a2, b2, c2))
    sources = []
    for oriented_source in oriented_sources:
        source = [0, 0, 0]
        for oriented_mode, original_mode in enumerate(positions):
            source[original_mode] = oriented_source[oriented_mode]
        sources.append(tuple(source))
    replayed = plus_local(sources[0], sources[1], positions, variant)
    replayed_oriented = tuple(tuple(term[position] for position in positions) for term in replayed)
    named_results = {}
    coordinate = 0
    for output_index in range(3):
        for factor_index in range(3):
            named_results[EQUATION_NAMES[variant][coordinate]] = replayed_oriented[output_index][factor_index] == oriented_outputs[output_index][factor_index]
            coordinate += 1
    return tuple(sources), oriented_outputs, replayed, replayed_oriented, named_results


def term_hex(term):
    return ["%04x" % word for word in term]


def all_strings(value):
    if isinstance(value, str):
        yield value
    elif isinstance(value, dict):
        for key, child in value.items():
            yield from all_strings(key)
            yield from all_strings(child)
    elif isinstance(value, list):
        for child in value:
            yield from all_strings(child)


def build_expected_descriptors():
    descriptors = []
    full_semantic_coordinates = []
    compact_descriptors = []
    for orientation_index, (name, positions) in enumerate(ORIENTATIONS):
        for variant in range(3):
            for assignment in itertools.permutations((45, 46, 47)):
                full_semantic_coordinate = (orientation_index, variant) + assignment
                compact_descriptor = (assignment[0], assignment[1], orientation_index, variant)
                accepted = full_semantic_coordinate in ACCEPTED_FULL_SEMANTIC_COORDINATES
                descriptors.append({
                    "descriptor_index": len(descriptors),
                    "orientation_index": orientation_index,
                    "orientation": name,
                    "positions": list(positions),
                    "variant": variant,
                    "formula": FORMULAS[str(variant)],
                    "assignment": list(assignment),
                    "accepted": accepted,
                    "classification": ACCEPTED_CLASS if accepted else REJECTED_CLASS,
                })
                full_semantic_coordinates.append(full_semantic_coordinate)
                compact_descriptors.append(compact_descriptor)
    return descriptors, full_semantic_coordinates, compact_descriptors


def validate_records(document, root_terms, child, expected_descriptors, full_semantic_coordinates, compact_descriptors):
    accepted = document["accepted_descriptors"]
    rejected = document["rejected_descriptors"]
    check(len(accepted) == 6 and len(rejected) == 102, "record partition lengths failed")
    by_index = {}
    for record in accepted + rejected:
        index = record.get("descriptor_index")
        check(isinstance(index, int) and index not in by_index and 0 <= index < 108, "record index uniqueness failed")
        by_index[index] = record
    check(set(by_index) == set(range(108)), "full record index coverage failed")
    all_records = [by_index[index] for index in range(108)]
    accepted_indices = [index for index, descriptor in enumerate(expected_descriptors) if descriptor["accepted"]]
    rejected_indices = [index for index in range(108) if index not in accepted_indices]
    check([record["descriptor_index"] for record in accepted] == accepted_indices, "accepted record order failed")
    check([record["descriptor_index"] for record in rejected] == rejected_indices, "rejected record order failed")
    survivors = child[:45]
    ordered_parents = set()
    unordered_parents = set()
    source_pairs = set()
    for descriptor, record in zip(expected_descriptors, all_records):
        assignment = tuple(descriptor["assignment"])
        positions = tuple(descriptor["positions"])
        variant = descriptor["variant"]
        outputs = tuple(child[slot] for slot in assignment)
        sources, oriented_outputs, replayed, replayed_oriented, named_results = inverse_plus(outputs, positions, variant)
        equation_consistent = all(named_results.values())
        check(equation_consistent == descriptor["accepted"], "independent inverse partition mismatch at %d" % descriptor["descriptor_index"])
        common = {
            "accepted": descriptor["accepted"],
            "classification": descriptor["classification"],
            "descriptor_index": descriptor["descriptor_index"],
            "assignment": list(assignment),
            "orientation": descriptor["orientation"],
            "orientation_index": descriptor["orientation_index"],
            "positions": list(positions),
            "variant": variant,
            "formula": FORMULAS[str(variant)],
            "forward_method_label": FORWARD_METHOD_LABEL,
            "inverse_method_label": INVERSE_METHOD_LABEL,
            "output_slots": list(assignment),
            "output_terms_hex": [term_hex(term) for term in outputs],
        }
        if not descriptor["accepted"]:
            expected_record = dict(common)
            expected_record["inverse_equations"] = {
                "all_named_equations_hold": False,
                "named_results": named_results,
                "oriented_actual_outputs": [list(term) for term in oriented_outputs],
                "oriented_replayed_outputs": [list(term) for term in replayed_oriented],
            }
            expected_record["rejection_class"] = REJECTED_CLASS
            check(record == expected_record, "exact rejected semantic record mismatch at %d" % descriptor["descriptor_index"])
            continue
        replayed_child = list(survivors) + [None, None, None]
        for output_index, child_slot in enumerate(assignment):
            replayed_child[child_slot] = replayed[output_index]
        replayed_child = tuple(replayed_child)
        parent_list = []
        survivor_index = 0
        for parent_slot in range(47):
            if parent_slot == 7:
                parent_list.append(sources[0])
            elif parent_slot == 13:
                parent_list.append(sources[1])
            else:
                parent_list.append(survivors[survivor_index])
                survivor_index += 1
        parent = tuple(parent_list)
        identity = list(range(47))
        transposition = list(identity)
        transposition[7], transposition[13] = transposition[13], transposition[7]
        exact_root = parent == root_terms
        swapped_root = all(parent[parent_slot] == root_terms[transposition[parent_slot]] for parent_slot in range(47))
        check(exact_root != swapped_root, "accepted parent does not have unique c659 lineage")
        mapping = identity if exact_root else transposition
        factor_witnesses = []
        for parent_slot, root_slot in enumerate(mapping):
            parent_factors = parent[parent_slot]
            root_factors = root_terms[root_slot]
            equalities = [parent_factors[mode] == root_factors[mode] for mode in range(3)]
            factor_witnesses.append({
                "parent_slot": parent_slot,
                "root_slot": root_slot,
                "parent_factors_hex": term_hex(parent_factors),
                "root_factors_hex": term_hex(root_factors),
                "factor_equalities": equalities,
                "complete_term_equal": all(equalities),
            })
        zero_slots = [slot for slot, term in enumerate(parent) if any(word == 0 for word in term)]
        grouped_slots = {}
        for slot, term in enumerate(parent):
            grouped_slots.setdefault(term, []).append(slot)
        duplicate_slots = [slots for slots in grouped_slots.values() if len(slots) > 1]
        source_zero_slots = [slot for slot, term in enumerate(sources) if any(word == 0 for word in term)]
        source_collision_modes = [mode for mode in range(3) if sources[0][mode] == sources[1][mode]]
        literal_equality = all(witness["complete_term_equal"] for witness in factor_witnesses)
        generating_alias = (exact_root or swapped_root) and literal_equality
        expected_record = dict(common)
        expected_record.update({
            "inverse_equations": {
                "all_named_equations_hold": True,
                "named_results": named_results,
                "oriented_actual_outputs": [list(term) for term in oriented_outputs],
            },
            "forward_plus_local_exact": replayed == outputs,
            "scatter_replayed_fixed_child_exactly": replayed_child == child,
            "local_tensor_replayed_exactly": tensor(sources) == tensor(outputs),
            "generating_alias": generating_alias,
            "alternate_exact_parent": not generating_alias,
            "ordered_parent_lineage": "c659_identity" if exact_root else "c659_transposition_(7 13)",
            "parent_lineage_witness": {
                "root_id": ROOT_ID,
                "parent_slot_to_root_slot": mapping,
                "literal_factor_equality": literal_equality,
                "literal_factor_equality_witnesses": factor_witnesses,
                "source_parent_slots": [7, 13],
                "source_terms_equal_mapped_root_slots": all(sources[index] == root_terms[mapping[slot]] for index, slot in enumerate((7, 13))),
            },
            "parent_exact_root_order_match": exact_root,
            "parent_all_47_nonzero": not zero_slots,
            "parent_all_47_complete_terms_distinct": not duplicate_slots,
            "parent_zero_factor_terms": zero_slots,
            "parent_duplicate_complete_term_groups": duplicate_slots,
            "parent_tensor_replayed_exactly": tensor(parent) == multiplication_tensor(),
            "parent_ordered_factor_major_sha256": sha256(ordered_bytes(parent)),
            "parent_unordered_canonical_sha256": sha256(unordered_bytes(parent)),
            "reconstructed_parent_term_count": len(parent),
            "source_pair": [list(term) for term in sources],
            "source_pair_hex": [term_hex(term) for term in sources],
            "source_zero_factor_terms": source_zero_slots,
            "source_factor_collision_modes": source_collision_modes,
            "source_precondition_legal": not source_zero_slots and not source_collision_modes,
        })
        check(record == expected_record, "exact accepted semantic record mismatch at %d" % descriptor["descriptor_index"])
        check(generating_alias and not record["alternate_exact_parent"], "accepted lineage flags failed")
        check(replayed == outputs and replayed_child == child and tensor(sources) == tensor(outputs), "accepted local/scatter/tensor replay failed")
        check(tensor(parent) == multiplication_tensor(), "accepted parent tensor replay failed")
        check(len(factor_witnesses) == 47 and all(witness["complete_term_equal"] for witness in factor_witnesses), "literal factor witness coverage failed")
        ordered_parents.add(ordered_bytes(parent))
        unordered_parents.add(unordered_bytes(parent))
        source_pairs.add(sources)
    check((len(ordered_parents), len(unordered_parents), len(source_pairs)) == (2, 1, 2), "parent/source deduplication counts failed")
    compact_all = b"".join(canonical(list(descriptor)) + bytes((10,)) for descriptor in compact_descriptors)
    compact_accepted = b"".join(canonical(list(descriptor)) + bytes((10,)) for descriptor in ACCEPTED_COMPACT_DESCRIPTORS)
    full_all = b"".join(canonical(record) + bytes((10,)) for record in all_records)
    full_accepted = b"".join(canonical(record) + bytes((10,)) for record in accepted)
    streams = document["streams"]
    check(streams == EXPECTED_STREAMS, "frozen stream metadata failed")
    for value, byte_key, hash_key, section in (
        (compact_all, "all_bytes", "all_sha256", "compact_descriptor_streams"),
        (compact_accepted, "accepted_bytes", "accepted_sha256", "compact_descriptor_streams"),
        (full_all, "all_bytes", "all_sha256", "full_semantic_record_streams"),
        (full_accepted, "accepted_bytes", "accepted_sha256", "full_semantic_record_streams"),
    ):
        check(len(value) == streams[section][byte_key] and sha256(value) == streams[section][hash_key], "recomputed stream digest failed: %s/%s" % (section, hash_key))


def run_validator_self_tests():
    positive = ((1, 1, 1),)
    check(tensor(positive) == outer_tensor((1, 1, 1)), "validator positive tensor self-test failed")
    check(tensor(((1, 1, 2),)) != outer_tensor((1, 1, 1)), "validator synthetic tensor negative failed")
    check([slot for slot, term in enumerate(((1, 2, 3), (0, 2, 3))) if any(word == 0 for word in term)] == [1], "validator synthetic zero-factor negative failed")
    groups = {}
    for slot, term in enumerate(((1, 2, 3), (4, 5, 6), (1, 2, 3))):
        groups.setdefault(term, []).append(slot)
    check([slots for slots in groups.values() if len(slots) > 1] == [[0, 2]], "validator synthetic duplicate-term negative failed")


def validate(source_path, artifact_path, root_path):
    run_validator_self_tests()
    source = read_regular(source_path, "Sage source", PINNED_SAGE_BYTES)
    artifact = read_regular(artifact_path, "artifact", PINNED_ARTIFACT_BYTES)
    root_raw = read_regular(root_path, "root fixture", PINNED_ROOT_RAW_BYTES)
    check(sha256(source) == PINNED_SAGE_SHA256, "Sage source SHA-256 does not match static pin")
    check(sha256(artifact) == PINNED_ARTIFACT_SHA256, "artifact SHA-256 does not match static pin")
    try:
        document = json.loads(artifact.decode("ascii"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValidationError("artifact JSON decoding failed: %s" % error)
    check(artifact == canonical(document) + bytes((10,)), "artifact is not exact canonical JSON plus one LF")
    check(set(document) == {"accepted_descriptors", "authentication", "counts", "deduplication", "enumeration", "field", "fixed_child", "implementation", "inverse_method", "rejected_descriptors", "root", "schema", "self_checks", "status", "streams"}, "top-level schema fields failed")
    check(document["schema"] == SCHEMA and document["status"] == "complete", "schema or completion status failed")
    check(document["field"] == {"name": "GF(2)", "characteristic": 2, "addition": "bitwise XOR"}, "field metadata failed")
    check(not any(os.path.isabs(value) for value in all_strings(document)), "artifact contains an absolute path string")
    expected_source_binding = {"bytes": PINNED_SAGE_BYTES, "sha256": PINNED_SAGE_SHA256}
    check(document["implementation"] == {
        "repository_relative_id": SCRIPT_ID,
        "artifact_repository_relative_id": ARTIFACT_ID,
        "source_bytes_read_at_oracle_start": expected_source_binding,
        "source_bytes_read_at_report_time": expected_source_binding,
        "source_binding_statement": "hashes report actual source-file bytes read at oracle start and again at report time; equality is required",
        "runtime_guard_statement": "generation requires the sage.all execution namespace and the Sage -- argv delimiter; this ordinary-runtime guard is not attestation against a malicious in-process caller able to forge globals",
    }, "stable implementation IDs, runtime limits, or actual-byte source binding failed")
    unauthenticated = dict(document)
    authentication = unauthenticated.pop("authentication")
    check(authentication == {
        "algorithm": "SHA-256",
        "canonicalization": "ASCII JSON with sorted keys and compact separators",
        "scope": "all top-level fields except authentication",
        "semantic_and_source_binding_sha256": sha256(canonical(unauthenticated)),
    }, "artifact internal authentication failed")
    root_terms = parse_root(root_raw)
    root_ordered, root_unordered = ordered_bytes(root_terms), unordered_bytes(root_terms)
    expected_tensor = multiplication_tensor()
    check(len(root_ordered) == 290 and sha256(root_ordered) == PINNED_ROOT_ORDERED_SHA256, "root ordered payload pin failed")
    check(len(root_unordered) == 290 and sha256(root_unordered) == PINNED_ROOT_UNORDERED_SHA256, "root unordered payload pin failed")
    check(tensor(root_terms) == expected_tensor and sha256(expected_tensor.to_bytes(512, "little")) == PINNED_TENSOR_SHA256, "root tensor replay or pin failed")
    check(document["root"] == {
        "repository_relative_id": ROOT_ID,
        "fixture_name": "c659_iteration5551_Z2",
        "dimensions": [4, 4, 4],
        "rank": 47,
        "raw_bytes": PINNED_ROOT_RAW_BYTES,
        "raw_sha256": PINNED_ROOT_RAW_SHA256,
        "ordered_factor_major_bytes": 290,
        "ordered_factor_major_sha256": PINNED_ROOT_ORDERED_SHA256,
        "unordered_canonical_bytes": 290,
        "unordered_canonical_sha256": PINNED_ROOT_UNORDERED_SHA256,
        "tensor_sha256": PINNED_TENSOR_SHA256,
        "tensor_replayed_exactly": True,
        "zero_factor_terms": [],
        "duplicate_complete_term_groups": [],
    }, "exact authenticated root metadata failed")
    inserted = plus_local(root_terms[7], root_terms[13], (0, 2, 1), 0)
    child = tuple(term for slot, term in enumerate(root_terms) if slot not in (7, 13)) + inserted
    child_ordered, child_unordered = ordered_bytes(child), unordered_bytes(child)
    check(len(child_ordered) == 296 and sha256(child_ordered) == PINNED_CHILD_ORDERED_SHA256, "child ordered payload pin failed")
    check(len(child_unordered) == 296 and sha256(child_unordered) == PINNED_CHILD_UNORDERED_SHA256, "child unordered payload pin failed")
    check(tensor(child) == expected_tensor, "fixed child tensor replay failed")
    check(document["fixed_child"] == {
        "construction": "remove root slots 7 and 13; Plus variant 0 under ikj=(0,2,1); append outputs in formula order at child slots 45,46,47",
        "source_root_slots": [7, 13],
        "orientation": "ikj",
        "positions": [0, 2, 1],
        "variant": 0,
        "formula": FORMULAS["0"],
        "forward_method_label": FORWARD_METHOD_LABEL,
        "term_count": 48,
        "insertion_slots": [45, 46, 47],
        "slot_to_term_hex": {str(slot): term_hex(child[slot]) for slot in (45, 46, 47)},
        "inserted_terms_hex_in_formula_order": [term_hex(term) for term in inserted],
        "ordered_factor_major_bytes": 296,
        "ordered_factor_major_sha256": PINNED_CHILD_ORDERED_SHA256,
        "unordered_canonical_bytes": 296,
        "unordered_canonical_sha256": PINNED_CHILD_UNORDERED_SHA256,
        "tensor_replayed_exactly": True,
        "all_terms_nonzero": True,
        "all_complete_terms_distinct": True,
    }, "exact ordered/unordered fixed-child authentication or slot mapping failed")
    check(document["inverse_method"] == {
        "method_label": INVERSE_METHOD_LABEL,
        "forward_method_label": FORWARD_METHOD_LABEL,
        "enumeration_order": "orientation-major, variant-major, lexicographic assignment-major",
        "assignment_semantics": "assignment is the child-slot triple assigned respectively to formula outputs 0,1,2",
        "orientation_order": [name for name, _ in ORIENTATIONS],
        "orientation_positions": [list(positions) for _, positions in ORIENTATIONS],
        "variant_order": [0, 1, 2],
        "formulas": FORMULAS,
        "named_equations_by_variant": {str(variant): list(EQUATION_NAMES[variant]) for variant in range(3)},
        "parent_reconstruction": "retain child slots 0..44 as survivors and insert the ordered reconstructed source pair at parent slots 7 and 13",
    }, "exact orientation/formula/method/equation tables failed")
    expected_descriptors, full_semantic_coordinates, compact_descriptors = build_expected_descriptors()
    accepted_indices = [descriptor["descriptor_index"] for descriptor in expected_descriptors if descriptor["accepted"]]
    rejected_indices = [descriptor["descriptor_index"] for descriptor in expected_descriptors if not descriptor["accepted"]]
    frozen_accepted = [descriptor for descriptor in expected_descriptors if descriptor["accepted"]]
    check(document["enumeration"] == {
        "full_semantic_coordinate_schema": ["orientation_index", "variant", "formula_output0_child_slot", "formula_output1_child_slot", "formula_output2_child_slot"],
        "compact_descriptor_schema": ["slotX", "slotY", "orientationIndex", "variant"],
        "compact_descriptor_semantics": "slotX and slotY are the child slots assigned to formula outputs 0 and 1; slotZ/formula output 2 is the remaining member of {45,46,47}",
        "descriptors": expected_descriptors,
        "frozen_accepted_descriptors": frozen_accepted,
        "frozen_accepted_full_semantic_coordinates": [list(value) for value in ACCEPTED_FULL_SEMANTIC_COORDINATES],
        "frozen_accepted_compact_descriptors": [list(value) for value in ACCEPTED_COMPACT_DESCRIPTORS],
        "accepted_descriptor_indices_in_enumeration_order": accepted_indices,
        "rejected_descriptor_indices_in_enumeration_order": rejected_indices,
    }, "exact descriptor order, six-descriptor freeze, or ordered partition failed")
    check(len(full_semantic_coordinates) == len(set(full_semantic_coordinates)) == 108, "validator full semantic coordinates are not 108 unique values")
    check(len(compact_descriptors) == len(set(compact_descriptors)) == 108, "validator compact descriptors are not 108 unique values")
    check(document["counts"] == EXPECTED_COUNTS, "exact counts failed")
    check(document["deduplication"] == EXPECTED_DEDUPLICATION, "deduplication names or domain failed")
    check(document["self_checks"] == {
        "orientation_permutations_and_order_frozen": True,
        "formula_text_and_method_labels_frozen": True,
        "all_108_full_semantic_coordinates_unique_and_ordered": True,
        "all_108_compact_descriptors_unique_and_ordered": True,
        "accepted_rejected_sequence_partition_frozen": True,
        "accepted_full_semantic_coordinates_frozen": True,
        "accepted_compact_descriptors_frozen": True,
        "six_accepted_descriptors_frozen": True,
        "literal_factor_equality_witnesses_complete": True,
        "compact_stream_digests_frozen": True,
        "full_semantic_stream_digests_frozen": True,
        "synthetic_tensor_negative_passed": True,
        "synthetic_zero_factor_negative_passed": True,
        "synthetic_duplicate_term_negative_passed": True,
    }, "oracle self-check declarations failed")
    validate_records(document, root_terms, child, expected_descriptors, full_semantic_coordinates, compact_descriptors)


def parse_arguments():
    directory = os.path.dirname(os.path.abspath(__file__))
    repository = os.path.realpath(os.path.join(directory, "..", ".."))
    parser = argparse.ArgumentParser(description="Validate the pinned c659 inverse-Plus oracle artifact.")
    parser.add_argument("--sage-source", default=os.path.join(repository, SCRIPT_ID))
    parser.add_argument("--artifact", default=os.path.join(repository, ARTIFACT_ID))
    parser.add_argument("--root", default=os.path.join(repository, ROOT_ID))
    return parser.parse_args()


def main():
    try:
        args = parse_arguments()
        validate(args.sage_source, args.artifact, args.root)
        print("validated c659 inverse-Plus oracle: sage=%s artifact=%s root=%s" % (PINNED_SAGE_SHA256, PINNED_ARTIFACT_SHA256, PINNED_ROOT_RAW_SHA256))
        return 0
    except (OSError, ValueError, ValidationError) as error:
        print("validation error: %s" % error, file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
