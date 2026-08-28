import argparse
import collections
import hashlib
import itertools
import json
import os
import stat
import struct
import sys

SCHEMA = "c659-all-child-wedge-inverse-plus-oracle-v1"
SOURCE_ID = "Programs/BilinearComplexity/c659_all_child_wedge_inverse_plus_oracle.sage"
SUMMARY_ID = "Programs/BilinearComplexity/c659_all_child_wedge_inverse_plus_oracle.json"
CORPUS_ID = "Programs/BilinearComplexity/c659_all_child_wedge_inverse_plus_oracle.bin"
VALIDATOR_ID = "Programs/BilinearComplexity/validate_c659_all_child_wedge_inverse_plus_oracle.py"
ROOT_ID = "cmd/c659-plusflip-cert/testdata/4x4x4_m47_c659_iteration5551_Z2.txt"
SOURCE_SIZE = 38923
SOURCE_SHA256 = "f1bdfe82af6d080468fbafdeafb49dcf1fe75d5f1652475d2dd088bc31dec285"
SUMMARY_SIZE = 11232
SUMMARY_SHA256 = "d92f72aafec5435985b1a000e25224d7e27f1126b898ee03563e7e836511fcf1"
CORPUS_SIZE = 7775908
CORPUS_SHA256 = "eac882916c80e3617e542434625c999d3177ed3d1d5fd67204d1152b50ee19a2"
ROOT_SIZE = 4524
ROOT_SHA256 = "25f47b5f37d2b7351dd5a2c5da65ff8ef5ba80ce53239d46cdfdef37e6eef403"
ROOT_ORDERED_SHA256 = "f61518b4864995fe5ba43f1b52819cc563c4c74326442ae12bbc338a491027cb"
ROOT_CANONICAL_SHA256 = "f2edf6735401e203b532cc85e0783fb47684815a3207b3ec601f8503c48956d1"
TENSOR_SHA256 = "1ae43419be8f86b7063141475bb207725b43bc4d1c6cae2c11a948b7359863bd"
CHILD_STREAM_SIZE = 1919856
CHILD_STREAM_SHA256 = "855b7242ed561ecffc9f636929e3f6171d2d8d1f7863ee1391f8b506a8fa5443"
ORIENTATION_NAMES = ("ijk", "ikj", "jik", "jki", "kij", "kji")
ORIENTATIONS = ((0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0))
FORMULAS = ("(a1,b1+b2,c1);(a1+a2,b2,c2);(a1,b2,c1+c2)", "(a1,b1,c1+c2);(a2,b1+b2,c2);(a1+a2,b1,c2)", "(a1+a2,b1,c1);(a2,b2,c1+c2);(a2,b1+b2,c1)")
SECTION_ORDER = ("forward_descriptors", "child_payloads", "child_aliases", "ordered_realizations", "raw_wedges", "derived_descriptors", "accepted_records", "source_classes", "parent_classes", "alias_inverse_coverage")
SECTION_RECORD_SIZES = (8, 296, 8, 444, 13, 28, 28, 14, 296, 8)
EXPECTED_COUNTS = (12972, 6486, 6486, 6486, 7758, 46548, 38916, 1081, 1, 38916)
TERMINALS = ("residual_failure", "source_policy_failure", "inverse_equation_failure", "invalid_parent", "exact_c659_parent", "alternate_valid_parent")
VALIDATION_FLAGS = 0x1f
VALIDATION_FLAGS_FIELD = "validation_flags:u8;bit0=all_nine_equations_and_formula_replay,bit1=source_policy,bit2=local_tensor,bit3=child_scatter,bit4=parent_tensor_nonzero_distinct"
SECTION_CONTRACTS = (
    ("forward_descriptors", "<HHBBH", 8, ("source_first_root_slot:u16", "source_second_root_slot:u16", "orientation_index:u8", "variant:u8", "child_index:u16")),
    ("child_payloads", "296-byte canonical child: <4H header then 48 lexicographic <HHH terms", 296, ("canonical_child_payload",)),
    ("child_aliases", "<II", 8, ("least_forward_descriptor_index:u32", "other_forward_descriptor_index:u32")),
    ("ordered_realizations", "<I then 296 bytes then 48B then 48B then 48B", 444, ("least_descriptor:u32", "ordered_factor_major_child:296B", "ordered_to_canonical:48xu8", "canonical_to_ordered:48xu8", "ordered_provenance:48xu8;0..46=root slot,128=X,129=Y,130=Z")),
    ("raw_wedges", "<H7BI", 13, ("child_index:u16", "center:u8", "color_a:u8", "color_b:u8", "leg_a:u8", "leg_b:u8", "residual_leg:u8", "residual_pass:u8", "first_descriptor_index:u32")),
    ("derived_descriptors", "<IH10BHHII", 28, ("wedge_index:u32", "child_index:u16", "assignment:u8", "variant:u8", "X:u8", "Y:u8", "Z:u8", "i:u8", "j:u8", "k:u8", "residual_pass:u8", "terminal:u8", "source_class:u16", "parent_class:u16", "accepted_index:u32", "forward_alias_index:u32")),
    ("accepted_records", "<IH6HHHIBB", 28, ("descriptor_index:u32", "nine_equation_mask:u16", "ordered_sources:6xu16", "source_class:u16", "parent_class:u16", "forward_alias_index:u32", VALIDATION_FLAGS_FIELD, "terminal:u8")),
    ("source_classes", "6H plus H", 14, ("lexicographically_sorted_source_pair:6xu16", "multiplicity:u16")),
    ("parent_classes", "290-byte canonical parent plus <IBB", 296, ("canonical_parent_payload:290B", "multiplicity:u32", "classification:u8;0=root,1=alternate", "orbit_status:u8;0=known_root,1=unknown")),
    ("alias_inverse_coverage", "<II", 8, ("forward_alias_index:u32", "accepted_record_index:u32")),
)

class ValidationError(Exception):
    pass

def require(value, message):
    if not value:
        raise ValidationError(message)

def digest(value):
    return hashlib.sha256(value).hexdigest()

def canonical_json(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii")

def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValidationError("duplicate JSON key: " + key)
        result[key] = value
    return result

def read_pinned(path, role, size, sha256):
    require(hasattr(os, "O_NOFOLLOW"), "runtime lacks required nofollow file support")
    metadata = os.lstat(path)
    require(not stat.S_ISLNK(metadata.st_mode) and stat.S_ISREG(metadata.st_mode), role + " must be a nofollow regular file")
    require(metadata.st_size == size, role + " external size pin mismatch")
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    try:
        opened = os.fstat(descriptor)
        require(stat.S_ISREG(opened.st_mode) and opened.st_size == size, role + " changed before bounded read")
        require((opened.st_dev, opened.st_ino) == (metadata.st_dev, metadata.st_ino), role + " identity changed before open")
        value = bytearray()
        while len(value) <= size:
            part = os.read(descriptor, min(65536, size + 1 - len(value)))
            if not part:
                break
            value.extend(part)
        require(len(value) == size, role + " changed or violated exact-size bound")
    finally:
        os.close(descriptor)
    value = bytes(value)
    require(digest(value) == sha256, role + " external SHA-256 pin mismatch")
    return value

def parse_root(raw):
    try:
        lines = raw.decode("ascii").splitlines()
    except UnicodeDecodeError as error:
        raise ValidationError("root is not ASCII: %s" % error)
    require(len(lines) == 4 and lines[0].split() == ["4", "4", "4", "47"], "root header mismatch")
    modes = []
    for line in lines[1:]:
        tokens = line.split()
        require(len(tokens) == 752 and all(token in ("0", "1") for token in tokens), "root token encoding mismatch")
        modes.append(tuple(sum(int(tokens[slot * 16 + coordinate]) << coordinate for coordinate in range(16)) for slot in range(47)))
    return tuple(tuple(modes[mode][slot] for mode in range(3)) for slot in range(47))

def header(rank):
    return struct.pack("<4H", 4, 4, 4, rank)

def ordered_payload(terms):
    value = bytearray(header(len(terms)))
    for mode in range(3):
        for term in terms:
            value.extend(struct.pack("<H", term[mode]))
    return bytes(value)

def canonical_payload(terms):
    terms = tuple(sorted(terms))
    return header(len(terms)) + b"".join(struct.pack("<HHH", *term) for term in terms)

def decode_canonical(value, rank):
    require(len(value) == 8 + 6 * rank and struct.unpack_from("<4H", value) == (4, 4, 4, rank), "canonical payload header/length mismatch")
    return tuple(struct.unpack_from("<HHH", value, 8 + 6 * slot) for slot in range(rank))

def bit_positions(word):
    while word:
        low = word & -word
        yield low.bit_length() - 1
        word -= low

_outer_cache = {}
def outer(term):
    if term in _outer_cache:
        return _outer_cache[term]
    value = 0
    for a in bit_positions(term[0]):
        for b in bit_positions(term[1]):
            base = (a * 16 + b) * 16
            for c in bit_positions(term[2]):
                value |= 1 << (base + c)
    _outer_cache[term] = value
    return value

def tensor(terms):
    value = 0
    for term in terms:
        value ^= outer(term)
    return value

def target_tensor():
    value = 0
    for i in range(4):
        for j in range(4):
            for k in range(4):
                value |= 1 << ((((4 * i + j) * 16) + (4 * j + k)) * 16 + (4 * k + i))
    return value

def valid_terms(terms):
    return all(all(term) for term in terms) and len(set(terms)) == len(terms)

def source_legal(sources):
    return all(all(source) for source in sources) and all(sources[0][mode] != sources[1][mode] for mode in range(3))

def plus(first, second, positions, variant):
    i, j, k = positions
    a1, b1, c1 = first[i], first[j], first[k]
    a2, b2, c2 = second[i], second[j], second[k]
    if variant == 0:
        oriented = ((a1, b1 ^ b2, c1), (a1 ^ a2, b2, c2), (a1, b2, c1 ^ c2))
    elif variant == 1:
        oriented = ((a1, b1, c1 ^ c2), (a2, b1 ^ b2, c2), (a1 ^ a2, b1, c2))
    elif variant == 2:
        oriented = ((a1 ^ a2, b1, c1), (a2, b2, c1 ^ c2), (a2, b1 ^ b2, c1))
    else:
        raise ValidationError("invalid Plus variant")
    result = []
    for values in oriented:
        term = [0, 0, 0]
        for index, mode in enumerate(positions):
            term[mode] = values[index]
        result.append(tuple(term))
    return tuple(result)

def inverse(outputs, positions, variant):
    oriented = tuple(tuple(term[mode] for mode in positions) for term in outputs)
    first, second, third = oriented
    if variant == 0:
        a1, b2, c1 = first[0], second[1], first[2]
        a2, b1, c2 = second[0] ^ a1, first[1] ^ b2, second[2]
    elif variant == 1:
        a1, b1, c2 = first[0], first[1], second[2]
        c1, a2, b2 = first[2] ^ c2, second[0], second[1] ^ b1
    elif variant == 2:
        a2, b1, c1 = second[0], first[1], first[2]
        a1, b2, c2 = first[0] ^ a2, second[1], second[2] ^ c1
    else:
        raise ValidationError("invalid inverse variant")
    sources = []
    for values in ((a1, b1, c1), (a2, b2, c2)):
        term = [0, 0, 0]
        for index, mode in enumerate(positions):
            term[mode] = values[index]
        sources.append(tuple(term))
    replay = plus(sources[0], sources[1], positions, variant)
    replay_oriented = tuple(tuple(term[mode] for mode in positions) for term in replay)
    mask = 0
    coordinate = 0
    for output in range(3):
        for factor in range(3):
            if replay_oriented[output][factor] == oriented[output][factor]:
                mask |= 1 << coordinate
            coordinate += 1
    return tuple(sources), replay, mask

def exact_classes(values, role, hash_function=hashlib.sha256):
    buckets = {}
    for index, value in enumerate(values):
        key = hash_function(value).digest()
        bucket = buckets.get(key)
        if bucket is None:
            buckets[key] = [value, [index]]
        else:
            require(bucket[0] == value, role + " hash collision on differing exact bytes")
            bucket[1].append(index)
    classes = sorted((bucket[0], bucket[1]) for bucket in buckets.values())
    return classes, {value: index for index, (value, members) in enumerate(classes)}

def section_digest(name, value):
    return digest(SCHEMA.encode("ascii") + b"\0section\0" + name.encode("ascii") + b"\0" + value)

def compare_sections(expected, actual):
    require(tuple(expected) == SECTION_ORDER and tuple(actual) == SECTION_ORDER, "binary section omitted or reordered")
    for name in SECTION_ORDER:
        require(expected[name] == actual[name], "binary section byte mismatch: " + name)

def classify_parent(value, root_value):
    return 0 if value == root_value else 1

def validate_ordered_record(value):
    require(len(value) == 444, "ordered realization record length mismatch")
    require(struct.unpack_from("<4H", value, 4) == (4, 4, 4, 48), "ordered realization payload header mismatch")
    ordered_to_canonical = tuple(value[300:348])
    canonical_to_ordered = tuple(value[348:396])
    provenance = tuple(value[396:444])
    require(sorted(ordered_to_canonical) == list(range(48)) and sorted(canonical_to_ordered) == list(range(48)), "ordered realization permutation is incomplete")
    require(all(canonical_to_ordered[ordered_to_canonical[index]] == index for index in range(48)), "ordered realization permutations are not inverse")
    require(all(code < 47 or code in (128, 129, 130) for code in provenance), "ordered realization provenance code mismatch")

def rejected(action):
    try:
        action()
    except ValidationError:
        return True
    return False

def guard_alias_multiplicity(groups, expected_count):
    flattened = [index for group in groups for index in group]
    require(len(groups) == expected_count and all(len(group) == 2 for group in groups), "forward child alias multiplicity mismatch")
    require(sorted(flattened) == list(range(2 * expected_count)), "forward aliases do not partition the descriptor indices")

def guard_typed_wedge(terms, center, color_a, color_b, leg_a, leg_b):
    require(center != color_a and center != color_b and color_a < color_b and leg_a != leg_b, "typed wedge indices/legs mismatch")
    shared_a = tuple(mode for mode in range(3) if terms[color_a][mode] == terms[center][mode])
    shared_b = tuple(mode for mode in range(3) if terms[color_b][mode] == terms[center][mode])
    require(shared_a == (leg_a,) and shared_b == (leg_b,), "typed wedge colors do not have the claimed unique legs")

def guard_local_replay(outputs, sources, replay, mask):
    require(mask == 511 and replay == outputs and tensor(sources) == tensor(outputs), "inverse equations/formula/local tensor replay failed")

def guard_scatter(expected_child, survivors, replay):
    require(canonical_payload(tuple(survivors) + tuple(replay)) == expected_child, "accepted child scatter failed")

def guard_parent_terms(terms, target, rank):
    require(len(terms) == rank and valid_terms(terms) and tensor(terms) == target, "parent tensor/nonzero/distinct failed")

def compute_validation_flags(mask, sources, outputs, replay, survivors, child_payload, parent_terms, target, rank=47):
    flags = 0
    if mask == 511 and replay == outputs:
        flags |= 1
    if source_legal(sources):
        flags |= 2
    if tensor(sources) == tensor(outputs):
        flags |= 4
    if canonical_payload(tuple(survivors) + tuple(replay)) == child_payload:
        flags |= 8
    if len(parent_terms) == rank and valid_terms(parent_terms) and tensor(parent_terms) == target:
        flags |= 16
    return flags

def guard_reciprocal(key, lookup):
    require(key in lookup, "inverse witness lacks reciprocal forward alias")
    return lookup[key]

def guard_coverage(coverage, alias_count, accepted_count, witnesses_per_alias):
    require(tuple(coverage) == tuple(sorted(coverage)), "reciprocal coverage is not sorted")
    require(all(0 <= alias < alias_count for alias, accepted_index in coverage), "reciprocal coverage alias out of range")
    require(sorted(accepted_index for alias, accepted_index in coverage) == list(range(accepted_count)), "reciprocal coverage does not partition accepted records")
    counts = collections.Counter(alias for alias, accepted_index in coverage)
    require(len(coverage) == accepted_count, "reciprocal coverage omitted an accepted witness")
    require(set(counts) == set(range(alias_count)), "reciprocal coverage misses a forward alias")
    require(collections.Counter(counts.values()) == {witnesses_per_alias: alias_count}, "reciprocal coverage multiplicity mismatch")
    return counts

def classify_terminal(residual_pass, equations_pass, sources_pass, parent_pass, exact_root):
    if not residual_pass:
        return 0
    if not equations_pass:
        return 2
    if not sources_pass:
        return 1
    if not parent_pass:
        return 3
    return 4 if exact_root else 5

def derive_outcome(terminal_partition, expected_total):
    require(set(terminal_partition) == set(TERMINALS) and all(type(value) is int and value >= 0 for value in terminal_partition.values()), "terminal partition keys/counts mismatch")
    require(sum(terminal_partition.values()) == expected_total, "terminal partition total mismatch")
    integrity_failures = sum(terminal_partition[name] for name in ("source_policy_failure", "inverse_equation_failure", "invalid_parent"))
    alternate_count = terminal_partition["alternate_valid_parent"]
    status = "complete" if integrity_failures == 0 else "incomplete"
    result = "complete_counterexample_found" if status == "complete" and alternate_count else "complete_no_counterexample_found" if status == "complete" else "incomplete"
    return status, result, integrity_failures, alternate_count

def guard_semantic(actual, expected):
    require(canonical_json(actual) == canonical_json(expected), "summary semantic contract mismatch")

def build_manifest(sections):
    require(tuple(sections) == SECTION_ORDER and tuple(contract[0] for contract in SECTION_CONTRACTS) == SECTION_ORDER, "section contract order mismatch")
    records = []
    offset = 0
    for name, layout, record_size, fields in SECTION_CONTRACTS:
        value = sections[name]
        require(len(value) % record_size == 0, "section record size mismatch: " + name)
        records.append({"id": name, "offset": offset, "size": len(value), "count": len(value) // record_size, "record_size": record_size, "endianness": "little", "layout": layout, "fields": list(fields), "payload_sha256": digest(value), "domain_separated_sha256": section_digest(name, value)})
        offset += len(value)
    return records

def domain_contract():
    return {"field": "GF(2) with bitwise-XOR addition", "forward": "all exact 47x46 ordered source-slot pairs, then orientations in the frozen order, variant 0 only", "orientation_order": list(ORIENTATION_NAMES), "orientation_positions": [list(positions) for positions in ORIENTATIONS], "forward_enumeration": "source_first_root_slot major, source_second_root_slot major skipping equality, orientation major", "forward_formula": FORMULAS[0], "child_canonicalization": "<4H dimensions/rank followed by 48 complete numeric <A,B,C> tuples sorted lexicographically by their unsigned 16-bit values, each then encoded as exact little-endian <HHH> bytes", "wedge_enumeration": "child byte order, center canonical slot, unordered color slots color_a<color_b; each color must share the center factor on exactly one leg and the two unique legs must differ", "factor_buckets": "for every child and mode, map each exact 16-bit factor word to every canonical color occurrence; no color or occurrence is discarded", "derived_enumeration": "wedge major, color assignment 0 then 1, variant 0 then 1 then 2", "assignment_semantics": "assignment 0 is X=color_a,Y=color_b and assignment 1 swaps them; Z is center", "orientation_table": {"variant_0": ["leg_X", "leg_Y", "residual_leg"], "variant_1": ["residual_leg", "leg_X", "leg_Y"], "variant_2": ["leg_Y", "residual_leg", "leg_X"]}, "formulas": list(FORMULAS), "residual_closure": "direct 16-bit XOR equality Z[residual_leg]=X[residual_leg] XOR Y[residual_leg]; no matrix or rank factorization", "inverse": "recover from formula outputs X and Y, record all nine factor equations, replay the executable formula, enforce both sources nonzero and unequal factorwise, replace X/Y/Z by the sources, and validate exact tensor/nonzero/distinct/scatter bytes", "parent_classification": "exact equality of the 290-byte canonical parent payload with the frozen c659 canonical payload; every other valid exact payload is retained as alternate with unknown orbit status"}

def negative_scope_contract():
    return {"statement": "No alternate exact parent occurs in the enumerated domain when result is complete_no_counterexample_found.", "included": "the exact frozen c659 root, fixed variant-0 all-forward-child domain, and all-term typed-wedge descriptors described here", "excluded": ["other roots", "other forward variants", "nonliteral equivalence", "the c680 bridge", "rank 46", "global orbit classification", "tensor-rank minimality"]}

def replay_checks(child_terms, members, realization, accepted, parent_classes, target, coverage_counts, forward_count):
    ordered_complete = len(realization) == 444 * len(child_terms)
    if ordered_complete:
        for offset in range(0, len(realization), 444):
            validate_ordered_record(realization[offset:offset + 444])
    class Collision:
        def digest(self):
            return b"x"
    checks = {"all_forward_children_exact_tensor_nonzero_distinct": all(valid_terms(terms) and tensor(terms) == target for terms in child_terms), "digest_collisions_on_differing_exact_bytes_fatal": rejected(lambda: exact_classes([b"a", b"b"], "replay-check", lambda value: Collision())), "every_child_has_two_forward_aliases": all(len(group) == 2 for group in members), "ordered_maps_complete_and_inverse": ordered_complete, "all_nine_inverse_equations_recorded": all(row[1] == 511 and row[6] & 1 for row in accepted), "accepted_sources_nonzero_and_factorwise_different": all(source_legal(row[2]) and row[6] & 2 for row in accepted), "accepted_parents_exact_tensor_nonzero_distinct": all(valid_terms(decode_canonical(value, 47)) and tensor(decode_canonical(value, 47)) == target for value, group in parent_classes) and all(row[6] & 16 for row in accepted), "accepted_forward_scatter_exact": all(row[6] & 8 for row in accepted), "reciprocal_alias_coverage_complete": len(coverage_counts) == forward_count and all(count == 3 for count in coverage_counts.values())}
    require(all(checks.values()), "reconstructed semantic check is false")
    return checks

def build_expected_document(semantic):
    semantic_digest = digest(SCHEMA.encode("ascii") + b"\0semantic\0" + canonical_json(semantic))
    implementation_statement = "These integrity checksums report regular source-file bytes read at start and report time and require equality; they are not loaded-code attestation or authentication, and runtime/path diagnostics are outside the semantic digest."
    return {"schema": SCHEMA, "semantic": semantic, "implementation": {"source_repository_relative_id": SOURCE_ID, "source_at_start": {"bytes": SOURCE_SIZE, "sha256": SOURCE_SHA256}, "source_at_report": {"bytes": SOURCE_SIZE, "sha256": SOURCE_SHA256}, "statement": implementation_statement}, "integrity": {"algorithm": "SHA-256", "classification": "integrity/checksums, not authentication", "semantic_digest_scope": "domain-separated canonical ASCII JSON encoding of the semantic object only", "semantic_sha256": semantic_digest}}

def regenerate(root, raw):
    target = target_tensor()
    require(digest(target.to_bytes(512, "little")) == TENSOR_SHA256, "target tensor encoding mismatch")
    require(tensor(root) == target and valid_terms(root), "root tensor/nonzero/distinct replay failed")
    require(digest(ordered_payload(root)) == ROOT_ORDERED_SHA256 and digest(canonical_payload(root)) == ROOT_CANONICAL_SHA256, "root payload checksum mismatch")
    root_ordered = ordered_payload(root)
    root_canonical = canonical_payload(root)
    forward_rows = []
    child_values = []
    ordered_values = []
    provenance_values = []
    for first in range(47):
        for second in range(47):
            if first == second:
                continue
            survivors = tuple(root[slot] for slot in range(47) if slot not in (first, second))
            survivor_provenance = tuple(slot for slot in range(47) if slot not in (first, second))
            for orientation_index, positions in enumerate(ORIENTATIONS):
                outputs = plus(root[first], root[second], positions, 0)
                require(tensor(outputs) == tensor((root[first], root[second])), "forward local tensor identity failed")
                terms = survivors + outputs
                require(valid_terms(terms), "forward child nonzero/distinct failed")
                child_values.append(canonical_payload(terms))
                ordered_values.append(terms)
                provenance_values.append(survivor_provenance + (128, 129, 130))
                forward_rows.append([first, second, orientation_index, 0, None])
    child_classes, child_lookup = exact_classes(child_values, "child")
    members = [[] for unused in child_classes]
    for descriptor_index, value in enumerate(child_values):
        child_index = child_lookup[value]
        forward_rows[descriptor_index][4] = child_index
        members[child_index].append(descriptor_index)
    guard_alias_multiplicity(members, 6486)
    sections = collections.OrderedDict()
    sections["forward_descriptors"] = b"".join(struct.pack("<HHBBH", *row) for row in forward_rows)
    sections["child_payloads"] = b"".join(value for value, group in child_classes)
    require(len(sections["child_payloads"]) == CHILD_STREAM_SIZE and digest(sections["child_payloads"]) == CHILD_STREAM_SHA256, "child payload stream freeze mismatch")
    sections["child_aliases"] = b"".join(struct.pack("<II", *group) for group in members)
    realization = bytearray()
    child_terms = []
    for child_index, (value, group) in enumerate(child_classes):
        least = group[0]
        terms = ordered_values[least]
        canonical_terms = tuple(sorted(terms))
        ordered_to_canonical = tuple(canonical_terms.index(term) for term in terms)
        canonical_to_ordered = tuple(terms.index(term) for term in canonical_terms)
        require(all(canonical_to_ordered[ordered_to_canonical[index]] == index for index in range(48)), "ordered map inverse failed")
        realization.extend(struct.pack("<I", least))
        realization.extend(ordered_payload(terms))
        realization.extend(bytes(ordered_to_canonical))
        realization.extend(bytes(canonical_to_ordered))
        realization.extend(bytes(provenance_values[least]))
        child_terms.append(canonical_terms)
    sections["ordered_realizations"] = bytes(realization)
    wedges = []
    descriptors = []
    accepted = []
    source_values = []
    parent_values = []
    for child_index, terms in enumerate(child_terms):
        buckets = tuple(collections.defaultdict(list) for unused in range(3))
        for color, term in enumerate(terms):
            for mode in range(3):
                buckets[mode][term[mode]].append(color)
        for center, center_term in enumerate(terms):
            colors = []
            for color in range(48):
                if color == center:
                    continue
                legs = tuple(mode for mode in range(3) if color in buckets[mode][center_term[mode]])
                if len(legs) == 1:
                    colors.append((color, legs[0]))
            for (color_a, leg_a), (color_b, leg_b) in itertools.combinations(colors, 2):
                if leg_a == leg_b:
                    continue
                residual = 3 - leg_a - leg_b
                guard_typed_wedge(terms, center, color_a, color_b, leg_a, leg_b)
                residual_pass = center_term[residual] == (terms[color_a][residual] ^ terms[color_b][residual])
                wedge_index = len(wedges)
                wedges.append((child_index, center, color_a, color_b, leg_a, leg_b, residual, int(residual_pass), len(descriptors)))
                for assignment in range(2):
                    if assignment == 0:
                        x, leg_x, y, leg_y = color_a, leg_a, color_b, leg_b
                    else:
                        x, leg_x, y, leg_y = color_b, leg_b, color_a, leg_a
                    for variant, positions in enumerate(((leg_x, leg_y, residual), (residual, leg_x, leg_y), (leg_y, residual, leg_x))):
                        descriptor_index = len(descriptors)
                        terminal = classify_terminal(residual_pass, False, False, False, False)
                        source_class = 65535
                        parent_class = 65535
                        accepted_index = 4294967295
                        alias_index = 4294967295
                        if residual_pass:
                            outputs = (terms[x], terms[y], terms[center])
                            sources, replay, mask = inverse(outputs, positions, variant)
                            if mask != 511:
                                terminal = classify_terminal(True, False, False, False, False)
                            elif not source_legal(sources):
                                terminal = classify_terminal(True, True, False, False, False)
                            else:
                                guard_local_replay(outputs, sources, replay, mask)
                                survivors = tuple(term for slot, term in enumerate(terms) if slot not in (x, y, center))
                                parent_terms = survivors + sources
                                parent_payload = canonical_payload(parent_terms)
                                guard_scatter(child_classes[child_index][0], survivors, replay)
                                parent_pass = len(parent_terms) == 47 and valid_terms(parent_terms)
                                terminal = classify_terminal(True, True, True, parent_pass, parent_payload == root_canonical)
                                if parent_pass:
                                    flags = compute_validation_flags(mask, sources, outputs, replay, survivors, child_classes[child_index][0], parent_terms, target)
                                    require(flags == VALIDATION_FLAGS, "accepted validation flags incomplete")
                                    source_values.append(b"".join(struct.pack("<HHH", *term) for term in sorted(sources)))
                                    parent_values.append(parent_payload)
                                    accepted_index = len(accepted)
                                    accepted.append([descriptor_index, mask, sources, None, None, None, flags, terminal])
                        descriptors.append([wedge_index, child_index, assignment, variant, x, y, center, positions[0], positions[1], positions[2], int(residual_pass), terminal, source_class, parent_class, accepted_index, alias_index])
    source_classes, source_lookup = exact_classes(source_values, "source")
    parent_classes, parent_lookup = exact_classes(parent_values, "parent")
    for value, group in parent_classes:
        guard_parent_terms(decode_canonical(value, 47), target, 47)
    alias_lookup = {(row[4], root[row[0]], root[row[1]]): index for index, row in enumerate(forward_rows)}
    for accepted_index, row in enumerate(accepted):
        descriptor_index, mask, sources, unused_a, unused_b, unused_c, flags, terminal = row
        source_class = source_lookup[source_values[accepted_index]]
        parent_class = parent_lookup[parent_values[accepted_index]]
        child_index = descriptors[descriptor_index][1]
        key = (child_index, sources[0], sources[1])
        alias_index = guard_reciprocal(key, alias_lookup)
        row[3], row[4], row[5] = source_class, parent_class, alias_index
        descriptors[descriptor_index][12] = source_class
        descriptors[descriptor_index][13] = parent_class
        descriptors[descriptor_index][15] = alias_index
    sections["raw_wedges"] = b"".join(struct.pack("<H7BI", *row) for row in wedges)
    sections["derived_descriptors"] = b"".join(struct.pack("<IH10BHHII", *row) for row in descriptors)
    sections["accepted_records"] = b"".join(struct.pack("<IH6HHHIBB", row[0], row[1], *(row[2][0] + row[2][1]), row[3], row[4], row[5], row[6], row[7]) for row in accepted)
    sections["source_classes"] = b"".join(value + struct.pack("<H", len(group)) for value, group in source_classes)
    sections["parent_classes"] = b"".join(value + struct.pack("<IBB", len(group), classify_parent(value, root_canonical), classify_parent(value, root_canonical)) for value, group in parent_classes)
    coverage = sorted((row[5], accepted_index) for accepted_index, row in enumerate(accepted))
    coverage_counts = guard_coverage(coverage, len(forward_rows), len(accepted), 3)
    sections["alias_inverse_coverage"] = b"".join(struct.pack("<II", *row) for row in coverage)
    terminal_counts = collections.Counter()
    for row in descriptors:
        code = row[11]
        require(type(code) is int and 0 <= code < len(TERMINALS), "terminal code out of range")
        terminal_counts[TERMINALS[code]] += 1
    terminal_partition = {name: terminal_counts[name] for name in TERMINALS}
    child_wedges = collections.Counter(row[0] for row in wedges)
    wedge_profile = collections.Counter(child_wedges[index] for index in range(len(child_classes)))
    coverage_profile = collections.Counter(collections.Counter(alias for alias, accepted_index in coverage).values())
    source_profile = collections.Counter(len(group) for value, group in source_classes)
    require(len(forward_rows) == 12972 and len(child_classes) == 6486, "forward census freeze mismatch")
    require(len(wedges) == 7758 and wedge_profile == {1: 5652, 2: 476, 3: 278, 4: 80}, "raw wedge census/profile freeze mismatch")
    require(len(descriptors) == 46548 and terminal_counts == {"residual_failure": 7632, "exact_c659_parent": 38916}, "descriptor terminal partition freeze mismatch")
    require(sum(row[10] for row in descriptors) == 38916, "residual admissible freeze mismatch")
    require(len(accepted) == 38916 and all(row[1] == 511 and row[6] == VALIDATION_FLAGS and row[7] == 4 for row in accepted), "accepted replay freeze mismatch")
    require(len(source_classes) == 1081 and source_profile == {36: 1081}, "source class freeze mismatch")
    require(len(parent_classes) == 1 and parent_classes[0][0] == root_canonical, "parent class/alternate freeze mismatch")
    status, result, integrity_failures, alternate_count = derive_outcome(terminal_partition, len(descriptors))
    manifest = build_manifest(sections)
    require(tuple(record["count"] for record in manifest) == EXPECTED_COUNTS and tuple(record["record_size"] for record in manifest) == SECTION_RECORD_SIZES, "section count/record-size freeze mismatch")
    corpus = b"".join(sections.values())
    counts = {"forward_descriptors": len(forward_rows), "unique_children": len(child_classes), "forward_alias_multiplicity_profile": {str(size): count for size, count in sorted(collections.Counter(map(len, members)).items())}, "child_payload_stream_bytes": len(sections["child_payloads"]), "raw_wedges": len(wedges), "child_raw_wedge_profile": {str(size): count for size, count in sorted(wedge_profile.items())}, "derived_descriptors": len(descriptors), "terminal_partition": {name: terminal_counts[name] for name in TERMINALS}, "residual_failures": sum(not row[10] for row in descriptors), "residual_admissible": sum(row[10] for row in descriptors), "accepted_records": len(accepted), "source_classes": len(source_classes), "source_class_multiplicity_profile": {str(size): count for size, count in sorted(source_profile.items())}, "parent_payload_classes": len(parent_classes), "exact_c659_parent_classes": sum(value == root_canonical for value, group in parent_classes), "alternate_parent_classes": sum(value != root_canonical for value, group in parent_classes), "forward_aliases_covered": len(coverage_counts), "inverse_witnesses_per_forward_alias_profile": {str(size): count for size, count in sorted(collections.Counter(coverage_counts.values()).items())}}
    root_nonzero = all(all(term) for term in root)
    root_distinct = len(set(root)) == len(root)
    root_tensor_exact = tensor(root) == target
    reconstructed_checks = replay_checks(child_terms, members, sections["ordered_realizations"], accepted, parent_classes, target, coverage_counts, len(forward_rows))
    semantic = {
        "schema": SCHEMA,
        "status": status,
        "result": result,
        "stable_ids": {"source": SOURCE_ID, "summary": SUMMARY_ID, "corpus": CORPUS_ID, "root": ROOT_ID},
        "root": {"raw_bytes": len(raw), "raw_sha256": digest(raw), "ordered_factor_major_bytes": len(root_ordered), "ordered_factor_major_sha256": digest(root_ordered), "unordered_canonical_bytes": len(root_canonical), "unordered_canonical_sha256": digest(root_canonical), "tensor_bytes": 512, "tensor_sha256": digest(target.to_bytes(512, "little")), "tensor_exact": root_tensor_exact, "nonzero": root_nonzero, "distinct": root_distinct},
        "domain": domain_contract(),
        "counts": counts,
        "outcome": {"complete_partition": sum(terminal_partition.values()) == len(descriptors), "integrity_or_replay_failure_count": integrity_failures, "exact_c659_parent_witnesses": terminal_partition["exact_c659_parent"], "alternate_valid_parent_witnesses": alternate_count, "alternate_orbit_status": "unknown" if alternate_count else "not_applicable"},
        "negative_scope": negative_scope_contract(),
        "corpus": {"repository_relative_id": CORPUS_ID, "bytes": len(corpus), "sha256": digest(corpus), "section_digest_domain": "SHA-256(schema ASCII || NUL || 'section' || NUL || section id ASCII || NUL || exact section bytes)", "strict_section_order": list(SECTION_ORDER), "sections": manifest, "sentinels": {"missing_u16": 65535, "missing_u32": 4294967295}, "terminal_codes": {name: index for index, name in enumerate(TERMINALS)}},
        "checks": reconstructed_checks,
    }
    return sections, semantic

def synthetic_tests():
    require(outer((1, 1, 1)) != outer((1, 1, 2)), "tensor negative selftest failed")
    require(tensor(((1, 1, 2),)) != outer((1, 1, 1)), "wrong-tensor replay selftest failed")
    require(not source_legal(((0, 1, 1), (1, 2, 2))), "zero-source selftest failed")
    require(not source_legal(((1, 2, 3), (1, 4, 5))), "equal-source-factor selftest failed")
    guard_alias_multiplicity(((0, 1), (2, 3)), 2)
    require(rejected(lambda: guard_alias_multiplicity(((0,), (1, 2)), 2)), "weak child-alias multiplicity selftest failed")
    require(rejected(lambda: guard_alias_multiplicity(((0, 1, 2),), 1)), "excess child-alias multiplicity selftest failed")
    require(rejected(lambda: guard_alias_multiplicity(((0, 1), (1, 3)), 2)), "duplicate alias partition selftest failed")
    wedge_terms = ((1, 2, 4), (1, 8, 16), (32, 2, 64), (1, 2, 128))
    guard_typed_wedge(wedge_terms, 0, 1, 2, 0, 1)
    require(rejected(lambda: guard_typed_wedge(wedge_terms, 0, 1, 3, 0, 1)), "nonunique typed-wedge leg selftest failed")
    require(rejected(lambda: guard_typed_wedge(((1, 2, 4), (1, 8, 16), (1, 32, 64)), 0, 1, 2, 0, 0)), "equal typed-wedge legs selftest failed")
    sources = ((1, 2, 4), (8, 16, 32))
    outputs = plus(sources[0], sources[1], (0, 1, 2), 0)
    guard_local_replay(outputs, sources, outputs, 511)
    require(rejected(lambda: guard_local_replay(outputs, sources, outputs[:-1] + ((1, 1, 1),), 511)), "wrong formula replay selftest failed")
    require(rejected(lambda: guard_local_replay(outputs, ((1, 2, 4), (8, 16, 64)), outputs, 511)), "wrong local tensor selftest failed")
    require(rejected(lambda: guard_local_replay(outputs, sources, outputs, 510)), "incomplete equation-mask selftest failed")
    survivors = ((64, 128, 256),)
    expected_child = canonical_payload(survivors + outputs)
    guard_scatter(expected_child, survivors, outputs)
    require(rejected(lambda: guard_scatter(canonical_payload(survivors + ((1, 1, 1),)), survivors, outputs)), "wrong scatter selftest failed")
    parent_terms = ((1, 2, 4), (8, 16, 32))
    guard_parent_terms(parent_terms, tensor(parent_terms), 2)
    require(rejected(lambda: guard_parent_terms((parent_terms[0], parent_terms[0]), tensor(parent_terms), 2)), "duplicate parent selftest failed")
    require(rejected(lambda: guard_parent_terms(((0, 2, 4), parent_terms[1]), tensor(parent_terms), 2)), "zero parent selftest failed")
    require(rejected(lambda: guard_parent_terms(parent_terms, tensor(((1, 2, 8),)), 2)), "wrong parent tensor selftest failed")
    flag_parent = survivors + sources
    flag_target = tensor(flag_parent)
    require(compute_validation_flags(511, sources, outputs, outputs, survivors, expected_child, flag_parent, flag_target, 3) == VALIDATION_FLAGS, "validation-flags positive selftest failed")
    require(compute_validation_flags(510, sources, outputs, outputs, survivors, expected_child, flag_parent, flag_target, 3) & 1 == 0, "equation/formula flag selftest failed")
    require(compute_validation_flags(511, ((0, 2, 4), sources[1]), outputs, outputs, survivors, expected_child, flag_parent, flag_target, 3) & 2 == 0, "source-policy flag selftest failed")
    require(compute_validation_flags(511, ((1, 2, 4), (8, 16, 64)), outputs, outputs, survivors, expected_child, flag_parent, flag_target, 3) & 4 == 0, "local-tensor flag selftest failed")
    require(compute_validation_flags(511, sources, outputs, outputs, survivors, canonical_payload(survivors + ((1, 1, 1),)), flag_parent, flag_target, 3) & 8 == 0, "scatter flag selftest failed")
    require(compute_validation_flags(511, sources, outputs, outputs, survivors, expected_child, flag_parent, tensor(((1, 2, 8),)), 3) & 16 == 0, "parent flag selftest failed")
    lookup = {(7, sources[0], sources[1]): 3}
    require(guard_reciprocal((7, sources[0], sources[1]), lookup) == 3, "reciprocal lookup positive selftest failed")
    require(rejected(lambda: guard_reciprocal((8, sources[0], sources[1]), lookup)), "missing reciprocal lookup selftest failed")
    coverage = tuple((alias, alias * 3 + witness) for alias in range(2) for witness in range(3))
    guard_coverage(coverage, 2, 6, 3)
    require(rejected(lambda: guard_coverage(coverage[:-1], 2, 6, 3)), "missing coverage selftest failed")
    require(rejected(lambda: guard_coverage(((0, 0), (0, 1), (1, 2), (1, 3)), 2, 4, 3)), "wrong coverage profile selftest failed")
    require(tuple(classify_terminal(*case) for case in ((False, False, False, False, False), (True, False, False, False, False), (True, True, False, False, False), (True, True, True, False, False), (True, True, True, True, True), (True, True, True, True, False))) == (0, 2, 1, 3, 4, 5), "terminal classification selftest failed")
    require(classify_parent(b"alternate", b"root") == 1 and classify_parent(b"root", b"root") == 0, "alternate-parent classifier selftest failed")
    positive_partition = {name: 0 for name in TERMINALS}
    positive_partition["residual_failure"] = 1
    positive_partition["exact_c659_parent"] = 3
    alternate_partition = {name: 0 for name in TERMINALS}
    alternate_partition["alternate_valid_parent"] = 1
    incomplete_partition = {name: 0 for name in TERMINALS}
    incomplete_partition["invalid_parent"] = 1
    positive_outcome = derive_outcome(positive_partition, 4)
    alternate_outcome = derive_outcome(alternate_partition, 1)
    incomplete_outcome = derive_outcome(incomplete_partition, 1)
    require(positive_outcome == ("complete", "complete_no_counterexample_found", 0, 0), "positive status/result selftest failed")
    require(alternate_outcome == ("complete", "complete_counterexample_found", 0, 1), "alternate status/result selftest failed")
    require(incomplete_outcome == ("incomplete", "incomplete", 1, 0), "incomplete status/result selftest failed")
    require(rejected(lambda: derive_outcome({"exact_c659_parent": 1}, 1)), "missing terminal partition key selftest failed")
    require(rejected(lambda: derive_outcome(positive_partition, 5)), "terminal partition total selftest failed")
    metadata = {"corpus": {"sentinels": {"missing_u16": 65535}, "sections": [{"layout": "<I", "fields": ["value:u32"], "endianness": "little"}]}, "status": "complete", "result": "complete_no_counterexample_found"}
    malformed = json.loads(json.dumps(metadata))
    malformed["corpus"]["sections"][0]["layout"] = ">I"
    guard_semantic(metadata, metadata)
    require(rejected(lambda: guard_semantic(malformed, metadata)), "malformed semantic metadata selftest failed")
    require(rejected(lambda: validate_ordered_record(b"\x00" * 443)), "truncated ordered-map selftest failed")
    class Collision:
        def digest(self):
            return b"x"
    require(rejected(lambda: exact_classes([b"a", b"b"], "synthetic", lambda value: Collision())), "hash-collision seam selftest failed")
    correct = collections.OrderedDict((name, bytes([index])) for index, name in enumerate(SECTION_ORDER))
    omitted = collections.OrderedDict(list(correct.items())[:-1])
    reordered = collections.OrderedDict(reversed(list(correct.items())))
    require(rejected(lambda: compare_sections(correct, omitted)), "omission selftest failed")
    require(rejected(lambda: compare_sections(correct, reordered)), "record-order selftest failed")

def parse_summary(value):
    try:
        text = value.decode("ascii")
    except UnicodeDecodeError as error:
        raise ValidationError("summary is not ASCII: %s" % error)
    require(text.endswith("\n") and "\r" not in text, "summary newline encoding mismatch")
    try:
        document = json.loads(text, object_pairs_hook=unique_object)
    except (json.JSONDecodeError, UnicodeDecodeError) as error:
        raise ValidationError("summary JSON parse failed: %s" % error)
    require(canonical_json(document) + b"\n" == value, "summary is not canonical compact ASCII JSON")
    require(document.get("schema") == SCHEMA, "summary schema mismatch")
    semantic = document.get("semantic")
    require(isinstance(semantic, dict), "summary semantic object missing")
    expected_semantic = digest(SCHEMA.encode("ascii") + b"\0semantic\0" + canonical_json(semantic))
    integrity = document.get("integrity")
    require(integrity.get("semantic_sha256") == expected_semantic and integrity.get("classification") == "integrity/checksums, not authentication", "semantic integrity checksum mismatch")
    implementation = document.get("implementation")
    require(implementation.get("source_repository_relative_id") == SOURCE_ID, "implementation source ID mismatch")
    require(implementation.get("source_at_start") == {"bytes": SOURCE_SIZE, "sha256": SOURCE_SHA256} and implementation.get("source_at_report") == {"bytes": SOURCE_SIZE, "sha256": SOURCE_SHA256}, "reported source bytes mismatch external source pin")
    return document

def validate_manifest(document, corpus, expected_semantic, expected_sections):
    metadata = document["semantic"]["corpus"]
    expected_metadata = expected_semantic["corpus"]
    require(metadata == expected_metadata, "corpus semantic metadata contract mismatch")
    require(metadata["repository_relative_id"] == CORPUS_ID and metadata["bytes"] == CORPUS_SIZE and metadata["sha256"] == CORPUS_SHA256, "corpus summary binding mismatch")
    require(tuple(metadata["strict_section_order"]) == SECTION_ORDER, "strict section order mismatch")
    records = metadata["sections"]
    require(len(records) == len(SECTION_ORDER), "section manifest length mismatch")
    actual = collections.OrderedDict()
    offset = 0
    for name, expected_value in expected_sections.items():
        size = len(expected_value)
        require(offset + size <= len(corpus), "section exceeds corpus: " + name)
        value = corpus[offset:offset + size]
        require(digest(value) == digest(expected_value) and section_digest(name, value) == section_digest(name, expected_value), "section checksum mismatch: " + name)
        actual[name] = value
        offset += size
    require(offset == len(corpus), "corpus has omitted or trailing bytes")
    return actual

def main():
    try:
        synthetic_tests()
        invoked = os.path.abspath(__file__)
        require(os.path.basename(invoked) == os.path.basename(VALIDATOR_ID), "validator basename mismatch")
        require(not stat.S_ISLNK(os.lstat(invoked).st_mode), "validator must not be invoked through a symbolic link")
        repository = os.path.realpath(os.path.join(os.path.dirname(invoked), "..", ".."))
        require(os.path.samefile(invoked, os.path.join(repository, VALIDATOR_ID)), "validator is not at stable repository-relative ID")
        parser = argparse.ArgumentParser()
        parser.add_argument("--source", default=os.path.join(repository, SOURCE_ID))
        parser.add_argument("--summary", default=os.path.join(repository, SUMMARY_ID))
        parser.add_argument("--corpus", default=os.path.join(repository, CORPUS_ID))
        parser.add_argument("--root", default=os.path.join(repository, ROOT_ID))
        options = parser.parse_args()
        read_pinned(options.source, "producer source", SOURCE_SIZE, SOURCE_SHA256)
        summary = read_pinned(options.summary, "summary", SUMMARY_SIZE, SUMMARY_SHA256)
        corpus = read_pinned(options.corpus, "corpus", CORPUS_SIZE, CORPUS_SHA256)
        raw = read_pinned(options.root, "root", ROOT_SIZE, ROOT_SHA256)
        document = parse_summary(summary)
        root = parse_root(raw)
        expected, expected_semantic = regenerate(root, raw)
        expected_document = build_expected_document(expected_semantic)
        guard_semantic(document, expected_document)
        actual = validate_manifest(document, corpus, expected_semantic, expected)
        compare_sections(expected, actual)
        print("validated %s: source=%s summary=%s corpus=%s root=%s" % (SCHEMA, SOURCE_SHA256, SUMMARY_SHA256, CORPUS_SHA256, ROOT_SHA256))
        return 0
    except (ValidationError, OSError, ValueError, struct.error) as error:
        print("validation error: %s" % error, file=sys.stderr)
        return 2

sys.exit(main())
