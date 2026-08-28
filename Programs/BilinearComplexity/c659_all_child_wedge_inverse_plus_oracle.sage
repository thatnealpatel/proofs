CODE = r'''
import argparse
import collections
import errno
import hashlib
import itertools
import json
import operator
import os
import secrets
import stat
import struct
import sys

SCHEMA = "c659-all-child-wedge-inverse-plus-oracle-v1"
SCRIPT_BASENAME = "c659_all_child_wedge_inverse_plus_oracle.sage"
SUMMARY_BASENAME = "c659_all_child_wedge_inverse_plus_oracle.json"
CORPUS_BASENAME = "c659_all_child_wedge_inverse_plus_oracle.bin"
SCRIPT_ID = "Programs/BilinearComplexity/" + SCRIPT_BASENAME
SUMMARY_ID = "Programs/BilinearComplexity/" + SUMMARY_BASENAME
CORPUS_ID = "Programs/BilinearComplexity/" + CORPUS_BASENAME
ROOT_ID = "cmd/c659-plusflip-cert/testdata/4x4x4_m47_c659_iteration5551_Z2.txt"
ROOT_SIZE = 4524
ROOT_SHA256 = "25f47b5f37d2b7351dd5a2c5da65ff8ef5ba80ce53239d46cdfdef37e6eef403"
ROOT_ORDERED_SHA256 = "f61518b4864995fe5ba43f1b52819cc563c4c74326442ae12bbc338a491027cb"
ROOT_CANONICAL_SHA256 = "f2edf6735401e203b532cc85e0783fb47684815a3207b3ec601f8503c48956d1"
TENSOR_SHA256 = "1ae43419be8f86b7063141475bb207725b43bc4d1c6cae2c11a948b7359863bd"
ORIENTATIONS = (("ijk", (0, 1, 2)), ("ikj", (0, 2, 1)), ("jik", (1, 0, 2)), ("jki", (1, 2, 0)), ("kij", (2, 0, 1)), ("kji", (2, 1, 0)))
FORMULAS = ("(a1,b1+b2,c1);(a1+a2,b2,c2);(a1,b2,c1+c2)", "(a1,b1,c1+c2);(a2,b1+b2,c2);(a1+a2,b1,c2)", "(a1+a2,b1,c1);(a2,b2,c1+c2);(a2,b1+b2,c1)")
TERMINALS = ("residual_failure", "source_policy_failure", "inverse_equation_failure", "invalid_parent", "exact_c659_parent", "alternate_valid_parent")
MAX_SOURCE_BYTES = 1048576
bxor = operator.xor

class OracleError(Exception):
    pass

def require(value, message):
    if not value:
        raise OracleError(message)

def digest(value):
    return hashlib.sha256(value).hexdigest()

def canonical_json(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True, default=int).encode("ascii")

def read_exact_regular(path, role, expected_size=None, maximum=MAX_SOURCE_BYTES, reject_symlink=True):
    require(hasattr(os, "O_NOFOLLOW") and hasattr(os, "O_DIRECTORY"), "runtime lacks required nofollow file support")
    before = os.lstat(path)
    if reject_symlink:
        require(not stat.S_ISLNK(before.st_mode), role + " must not be a symbolic link")
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    try:
        metadata = os.fstat(descriptor)
        require((metadata.st_dev, metadata.st_ino) == (before.st_dev, before.st_ino), role + " identity changed before open")
        require(stat.S_ISREG(metadata.st_mode), role + " is not a regular file")
        require(metadata.st_size <= maximum, role + " exceeds its size bound")
        if expected_size is not None:
            require(metadata.st_size == expected_size, role + " size mismatch")
        value = bytearray()
        while len(value) <= metadata.st_size:
            part = os.read(descriptor, min(65536, metadata.st_size + 1 - len(value)))
            if not part:
                break
            value.extend(part)
        require(len(value) == metadata.st_size, role + " changed during read")
        return bytes(value)
    finally:
        os.close(descriptor)

def discover(argv):
    require(__name__ == "sage.all" and sys.modules.get("sage.all") is not None and globals() is vars(sys.modules["sage.all"]), "supported runtime is sage -- " + SCRIPT_ID)
    require(len(argv) >= 2 and argv[0] == "--", "supported invocation is sage -- " + SCRIPT_ID)
    invoked = os.path.abspath(argv[1])
    require(os.path.basename(invoked) == SCRIPT_BASENAME, "script basename mismatch")
    source = read_exact_regular(invoked, "executing source", maximum=MAX_SOURCE_BYTES)
    repository = os.path.realpath(os.path.join(os.path.dirname(invoked), "..", ".."))
    expected = os.path.join(repository, SCRIPT_ID)
    require(os.path.samefile(invoked, expected), "script is not at stable repository-relative ID")
    return invoked, repository, source, argv[2:]

def parse_root(raw):
    require(len(raw) == ROOT_SIZE and digest(raw) == ROOT_SHA256, "root integrity checksum mismatch")
    try:
        lines = raw.decode("ascii").splitlines()
    except UnicodeDecodeError as error:
        raise OracleError("root is not ASCII: %s" % error)
    require(len(lines) == 4 and lines[0].split() == ["4", "4", "4", "47"], "root header mismatch")
    modes = []
    for line in lines[1:]:
        tokens = line.split()
        require(len(tokens) == 752 and all(token in ("0", "1") for token in tokens), "root factor encoding mismatch")
        modes.append(tuple(int(sum((int(tokens[slot * 16 + coordinate]) << int(coordinate)) for coordinate in range(16))) for slot in range(47)))
    return tuple(tuple(modes[mode][slot] for mode in range(3)) for slot in range(47))

def header(rank):
    return struct.pack("<4H", 4, 4, 4, rank)

def ordered_payload(terms):
    output = bytearray(header(len(terms)))
    for mode in range(3):
        for term in terms:
            output.extend(struct.pack("<H", term[mode]))
    return bytes(output)

def canonical_payload(terms):
    ordered = tuple(sorted(terms))
    return header(len(ordered)) + b"".join(struct.pack("<HHH", *term) for term in ordered)

def bits(word):
    while word:
        low = word & -word
        yield low.bit_length() - 1
        word -= low

_outer_cache = {}
def outer(term):
    cached = _outer_cache.get(term)
    if cached is not None:
        return cached
    value = int(0)
    for a in bits(term[0]):
        for b in bits(term[1]):
            base = (a * 16 + b) * 16
            for c in bits(term[2]):
                value |= 1 << (base + c)
    _outer_cache[term] = value
    return value

def tensor(terms):
    value = int(0)
    for term in terms:
        value = bxor(value, outer(term))
    return value

def target_tensor():
    value = int(0)
    for i in range(4):
        for j in range(4):
            for k in range(4):
                value |= 1 << ((((4 * i + j) * 16) + (4 * j + k)) * 16 + (4 * k + i))
    return value

def valid_terms(terms):
    return all(all(term) for term in terms) and len(set(terms)) == len(terms)

def plus(first, second, positions, variant):
    i, j, k = positions
    a1, b1, c1 = first[i], first[j], first[k]
    a2, b2, c2 = second[i], second[j], second[k]
    if variant == 0:
        oriented = ((a1, bxor(b1, b2), c1), (bxor(a1, a2), b2, c2), (a1, b2, bxor(c1, c2)))
    elif variant == 1:
        oriented = ((a1, b1, bxor(c1, c2)), (a2, bxor(b1, b2), c2), (bxor(a1, a2), b1, c2))
    elif variant == 2:
        oriented = ((bxor(a1, a2), b1, c1), (a2, b2, bxor(c1, c2)), (a2, bxor(b1, b2), c1))
    else:
        raise OracleError("invalid Plus variant")
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
        a2, b1, c2 = bxor(second[0], a1), bxor(first[1], b2), second[2]
    elif variant == 1:
        a1, b1, c2 = first[0], first[1], second[2]
        c1, a2, b2 = bxor(first[2], c2), second[0], bxor(second[1], b1)
    elif variant == 2:
        a2, b1, c1 = second[0], first[1], first[2]
        a1, b2, c2 = bxor(first[0], a2), second[1], bxor(second[2], c1)
    else:
        raise OracleError("invalid inverse variant")
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

def exact_classes(values, role):
    buckets = {}
    for index, value in enumerate(values):
        key = hashlib.sha256(value).digest()
        bucket = buckets.get(key)
        if bucket is None:
            buckets[key] = [value, [index]]
        else:
            require(bucket[0] == value, role + " SHA-256 collision on differing exact bytes")
            bucket[1].append(index)
    classes = sorted((bucket[0], bucket[1]) for bucket in buckets.values())
    index_by_value = {value: index for index, (value, members) in enumerate(classes)}
    return classes, index_by_value

def section_digest(name, data):
    return digest(SCHEMA.encode("ascii") + b"\0section\0" + name.encode("ascii") + b"\0" + data)

def build(root, raw):
    target = target_tensor()
    require(digest(target.to_bytes(512, "little")) == TENSOR_SHA256, "tensor encoding checksum mismatch")
    require(tensor(root) == target and valid_terms(root), "root exact tensor/nonzero/distinct validation failed")
    root_ordered = ordered_payload(root)
    root_canonical = canonical_payload(root)
    require(digest(root_ordered) == ROOT_ORDERED_SHA256 and digest(root_canonical) == ROOT_CANONICAL_SHA256, "root payload checksum mismatch")
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
            for orientation_index, pair in enumerate(ORIENTATIONS):
                outputs = plus(root[first], root[second], pair[1], 0)
                terms = survivors + outputs
                require(len(terms) == 48 and valid_terms(terms) and tensor(outputs) == tensor((root[first], root[second])), "forward child validation failed")
                child_values.append(canonical_payload(terms))
                ordered_values.append(terms)
                provenance_values.append(survivor_provenance + (128, 129, 130))
                forward_rows.append([first, second, orientation_index, 0, None])
    child_classes, child_index_by_payload = exact_classes(child_values, "child")
    descriptor_members = [[] for unused in child_classes]
    for descriptor_index, value in enumerate(child_values):
        child_index = child_index_by_payload[value]
        forward_rows[descriptor_index][4] = child_index
        descriptor_members[child_index].append(descriptor_index)
    require(all(len(members) == 2 for members in descriptor_members), "a child does not have exactly two exact replayed forward aliases")
    sections = collections.OrderedDict()
    sections["forward_descriptors"] = b"".join(struct.pack("<HHBBH", *row) for row in forward_rows)
    sections["child_payloads"] = b"".join(value for value, members in child_classes)
    sections["child_aliases"] = b"".join(struct.pack("<II", *members) for members in descriptor_members)
    realization = bytearray()
    child_terms = []
    for child_index, (value, members) in enumerate(child_classes):
        least = members[0]
        terms = ordered_values[least]
        canonical_terms = tuple(sorted(terms))
        ordered_to_canonical = tuple(canonical_terms.index(term) for term in terms)
        canonical_to_ordered = tuple(terms.index(term) for term in canonical_terms)
        require(all(canonical_to_ordered[ordered_to_canonical[index]] == index for index in range(48)), "ordered permutation inverse failed")
        realization.extend(struct.pack("<I", least))
        realization.extend(ordered_payload(terms))
        realization.extend(bytes(ordered_to_canonical))
        realization.extend(bytes(canonical_to_ordered))
        realization.extend(bytes(provenance_values[least]))
        child_terms.append(canonical_terms)
    sections["ordered_realizations"] = bytes(realization)
    wedges = []
    descriptors = []
    accepted_work = []
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
                residual_pass = center_term[residual] == bxor(terms[color_a][residual], terms[color_b][residual])
                wedge_index = len(wedges)
                first_descriptor = len(descriptors)
                wedges.append((child_index, center, color_a, color_b, leg_a, leg_b, residual, int(residual_pass), first_descriptor))
                for assignment in range(2):
                    if assignment == 0:
                        x, leg_x, y, leg_y = color_a, leg_a, color_b, leg_b
                    else:
                        x, leg_x, y, leg_y = color_b, leg_b, color_a, leg_a
                    position_table = ((leg_x, leg_y, residual), (residual, leg_x, leg_y), (leg_y, residual, leg_x))
                    for variant, positions in enumerate(position_table):
                        descriptor_index = len(descriptors)
                        terminal = 0
                        source_class = 65535
                        parent_class = 65535
                        accepted_index = 4294967295
                        alias_index = 4294967295
                        if residual_pass:
                            outputs = (terms[x], terms[y], terms[center])
                            sources, replay, equation_mask = inverse(outputs, positions, variant)
                            if equation_mask != 511:
                                terminal = 2
                            elif not all(all(source) for source in sources) or not all(sources[0][mode] != sources[1][mode] for mode in range(3)):
                                terminal = 1
                            else:
                                require(replay == outputs, "inverse replay disagrees after nine equations")
                                require(tensor(sources) == tensor(outputs), "inverse local tensor replay failed")
                                survivors = tuple(term for slot, term in enumerate(terms) if slot not in (x, y, center))
                                parent_terms = survivors + sources
                                parent_payload = canonical_payload(parent_terms)
                                scattered = canonical_payload(survivors + replay)
                                require(scattered == child_classes[child_index][0], "forward scatter does not exactly replay child")
                                if len(parent_terms) != 47 or not valid_terms(parent_terms):
                                    terminal = 3
                                else:
                                    terminal = 4 if parent_payload == root_canonical else 5
                                    source_payload = b"".join(struct.pack("<HHH", *term) for term in sorted(sources))
                                    source_values.append(source_payload)
                                    parent_values.append(parent_payload)
                                    accepted_index = len(accepted_work)
                                    accepted_work.append([descriptor_index, equation_mask, sources, None, None, None, 31, terminal])
                        descriptors.append([wedge_index, child_index, assignment, variant, x, y, center, positions[0], positions[1], positions[2], int(residual_pass), terminal, source_class, parent_class, accepted_index, alias_index])
    source_classes, source_index_by_value = exact_classes(source_values, "source class")
    parent_classes, parent_index_by_value = exact_classes(parent_values, "parent class")
    for value, members in parent_classes:
        terms = tuple(struct.unpack_from("<HHH", value, 8 + 6 * slot) for slot in range(47))
        require(valid_terms(terms) and tensor(terms) == target, "accepted parent class exact tensor/nonzero/distinct validation failed")
    alias_lookup = {(row[4], root[row[0]], root[row[1]]): index for index, row in enumerate(forward_rows)}
    for accepted_index, work in enumerate(accepted_work):
        descriptor_index, equation_mask, sources, unused_a, unused_b, unused_c, flags, terminal = work
        source_payload = source_values[accepted_index]
        parent_payload = parent_values[accepted_index]
        source_class = source_index_by_value[source_payload]
        parent_class = parent_index_by_value[parent_payload]
        child_index = descriptors[descriptor_index][1]
        alias_index = alias_lookup.get((child_index, sources[0], sources[1]))
        require(alias_index is not None, "accepted inverse witness has no exact forward alias")
        work[3], work[4], work[5] = source_class, parent_class, alias_index
        descriptors[descriptor_index][12] = source_class
        descriptors[descriptor_index][13] = parent_class
        descriptors[descriptor_index][15] = alias_index
    sections["raw_wedges"] = b"".join(struct.pack("<H7BI", *row) for row in wedges)
    sections["derived_descriptors"] = b"".join(struct.pack("<IH10BHHII", *row) for row in descriptors)
    sections["accepted_records"] = b"".join(struct.pack("<IH6HHHIBB", row[0], row[1], *(row[2][0] + row[2][1]), row[3], row[4], row[5], row[6], row[7]) for row in accepted_work)
    sections["source_classes"] = b"".join(value + struct.pack("<H", len(members)) for value, members in source_classes)
    parent_records = bytearray()
    for value, members in parent_classes:
        classification = 0 if value == root_canonical else 1
        orbit = 0 if classification == 0 else 1
        parent_records.extend(value)
        parent_records.extend(struct.pack("<IBB", len(members), classification, orbit))
    sections["parent_classes"] = bytes(parent_records)
    coverage = sorted((row[5], accepted_index) for accepted_index, row in enumerate(accepted_work))
    sections["alias_inverse_coverage"] = b"".join(struct.pack("<II", *row) for row in coverage)
    require(len(coverage) == len(accepted_work), "reciprocal coverage omitted an accepted witness")
    coverage_counts = collections.Counter(alias for alias, accepted_index in coverage)
    require(set(coverage_counts) == set(range(len(forward_rows))), "not every forward alias is recovered")
    offset = 0
    layouts = collections.OrderedDict((
        ("forward_descriptors", ("<HHBBH", 8, ["source_first_root_slot:u16", "source_second_root_slot:u16", "orientation_index:u8", "variant:u8", "child_index:u16"])),
        ("child_payloads", ("296-byte canonical child: <4H header then 48 lexicographic <HHH terms", 296, ["canonical_child_payload"])),
        ("child_aliases", ("<II", 8, ["least_forward_descriptor_index:u32", "other_forward_descriptor_index:u32"])),
        ("ordered_realizations", ("<I then 296 bytes then 48B then 48B then 48B", 444, ["least_descriptor:u32", "ordered_factor_major_child:296B", "ordered_to_canonical:48xu8", "canonical_to_ordered:48xu8", "ordered_provenance:48xu8;0..46=root slot,128=X,129=Y,130=Z"])),
        ("raw_wedges", ("<H7BI", 13, ["child_index:u16", "center:u8", "color_a:u8", "color_b:u8", "leg_a:u8", "leg_b:u8", "residual_leg:u8", "residual_pass:u8", "first_descriptor_index:u32"])),
        ("derived_descriptors", ("<IH10BHHII", 28, ["wedge_index:u32", "child_index:u16", "assignment:u8", "variant:u8", "X:u8", "Y:u8", "Z:u8", "i:u8", "j:u8", "k:u8", "residual_pass:u8", "terminal:u8", "source_class:u16", "parent_class:u16", "accepted_index:u32", "forward_alias_index:u32"])),
        ("accepted_records", ("<IH6HHHIBB", 28, ["descriptor_index:u32", "nine_equation_mask:u16", "ordered_sources:6xu16", "source_class:u16", "parent_class:u16", "forward_alias_index:u32", "validation_flags:u8;bit0=all_nine_equations_and_formula_replay,bit1=source_policy,bit2=local_tensor,bit3=child_scatter,bit4=parent_tensor_nonzero_distinct", "terminal:u8"])),
        ("source_classes", ("6H plus H", 14, ["lexicographically_sorted_source_pair:6xu16", "multiplicity:u16"])),
        ("parent_classes", ("290-byte canonical parent plus <IBB", 296, ["canonical_parent_payload:290B", "multiplicity:u32", "classification:u8;0=root,1=alternate", "orbit_status:u8;0=known_root,1=unknown"])),
        ("alias_inverse_coverage", ("<II", 8, ["forward_alias_index:u32", "accepted_record_index:u32"])),
    ))
    manifest = []
    for name, data in sections.items():
        layout, record_size, fields = layouts[name]
        require(len(data) % record_size == 0, "section record size mismatch")
        manifest.append({"id": name, "offset": offset, "size": len(data), "count": len(data) // record_size, "record_size": record_size, "endianness": "little", "layout": layout, "fields": fields, "payload_sha256": digest(data), "domain_separated_sha256": section_digest(name, data)})
        offset += len(data)
    corpus = b"".join(sections.values())
    terminal_counts = collections.Counter(TERMINALS[row[11]] for row in descriptors)
    child_wedge_counts = collections.Counter(row[0] for row in wedges)
    wedge_profile = collections.Counter(child_wedge_counts[index] for index in range(len(child_classes)))
    source_multiplicity = collections.Counter(len(members) for value, members in source_classes)
    coverage_multiplicity = collections.Counter(coverage_counts.values())
    alternate_count = terminal_counts["alternate_valid_parent"]
    integrity_failures = sum(terminal_counts[name] for name in ("source_policy_failure", "inverse_equation_failure", "invalid_parent"))
    status = "complete" if integrity_failures == 0 else "incomplete"
    result = "complete_counterexample_found" if status == "complete" and alternate_count else "complete_no_counterexample_found" if status == "complete" else "incomplete"
    semantic = {
        "schema": SCHEMA,
        "status": status,
        "result": result,
        "stable_ids": {"source": SCRIPT_ID, "summary": SUMMARY_ID, "corpus": CORPUS_ID, "root": ROOT_ID},
        "root": {"raw_bytes": len(raw), "raw_sha256": digest(raw), "ordered_factor_major_bytes": len(root_ordered), "ordered_factor_major_sha256": digest(root_ordered), "unordered_canonical_bytes": len(root_canonical), "unordered_canonical_sha256": digest(root_canonical), "tensor_bytes": 512, "tensor_sha256": digest(target.to_bytes(512, "little")), "tensor_exact": True, "nonzero": True, "distinct": True},
        "domain": {"field": "GF(2) with bitwise-XOR addition", "forward": "all exact 47x46 ordered source-slot pairs, then orientations in the frozen order, variant 0 only", "orientation_order": [name for name, positions in ORIENTATIONS], "orientation_positions": [list(positions) for name, positions in ORIENTATIONS], "forward_enumeration": "source_first_root_slot major, source_second_root_slot major skipping equality, orientation major", "forward_formula": FORMULAS[0], "child_canonicalization": "<4H dimensions/rank followed by 48 complete numeric <A,B,C> tuples sorted lexicographically by their unsigned 16-bit values, each then encoded as exact little-endian <HHH> bytes", "wedge_enumeration": "child byte order, center canonical slot, unordered color slots color_a<color_b; each color must share the center factor on exactly one leg and the two unique legs must differ", "factor_buckets": "for every child and mode, map each exact 16-bit factor word to every canonical color occurrence; no color or occurrence is discarded", "derived_enumeration": "wedge major, color assignment 0 then 1, variant 0 then 1 then 2", "assignment_semantics": "assignment 0 is X=color_a,Y=color_b and assignment 1 swaps them; Z is center", "orientation_table": {"variant_0": ["leg_X", "leg_Y", "residual_leg"], "variant_1": ["residual_leg", "leg_X", "leg_Y"], "variant_2": ["leg_Y", "residual_leg", "leg_X"]}, "formulas": list(FORMULAS), "residual_closure": "direct 16-bit XOR equality Z[residual_leg]=X[residual_leg] XOR Y[residual_leg]; no matrix or rank factorization", "inverse": "recover from formula outputs X and Y, record all nine factor equations, replay the executable formula, enforce both sources nonzero and unequal factorwise, replace X/Y/Z by the sources, and validate exact tensor/nonzero/distinct/scatter bytes", "parent_classification": "exact equality of the 290-byte canonical parent payload with the frozen c659 canonical payload; every other valid exact payload is retained as alternate with unknown orbit status"},
        "counts": {"forward_descriptors": len(forward_rows), "unique_children": len(child_classes), "forward_alias_multiplicity_profile": {str(size): sum(1 for members in descriptor_members if len(members) == size) for size in sorted(set(map(len, descriptor_members)))}, "child_payload_stream_bytes": len(sections["child_payloads"]), "raw_wedges": len(wedges), "child_raw_wedge_profile": {str(size): count for size, count in sorted(wedge_profile.items())}, "derived_descriptors": len(descriptors), "terminal_partition": {name: terminal_counts[name] for name in TERMINALS}, "residual_failures": sum(not row[10] for row in descriptors), "residual_admissible": sum(row[10] for row in descriptors), "accepted_records": len(accepted_work), "source_classes": len(source_classes), "source_class_multiplicity_profile": {str(size): count for size, count in sorted(source_multiplicity.items())}, "parent_payload_classes": len(parent_classes), "exact_c659_parent_classes": sum(value == root_canonical for value, members in parent_classes), "alternate_parent_classes": sum(value != root_canonical for value, members in parent_classes), "forward_aliases_covered": len(coverage_counts), "inverse_witnesses_per_forward_alias_profile": {str(size): count for size, count in sorted(coverage_multiplicity.items())}},
        "outcome": {"complete_partition": True, "integrity_or_replay_failure_count": integrity_failures, "exact_c659_parent_witnesses": terminal_counts["exact_c659_parent"], "alternate_valid_parent_witnesses": alternate_count, "alternate_orbit_status": "unknown" if alternate_count else "not_applicable"},
        "negative_scope": {"statement": "No alternate exact parent occurs in the enumerated domain when result is complete_no_counterexample_found.", "included": "the exact frozen c659 root, fixed variant-0 all-forward-child domain, and all-term typed-wedge descriptors described here", "excluded": ["other roots", "other forward variants", "nonliteral equivalence", "the c680 bridge", "rank 46", "global orbit classification", "tensor-rank minimality"]},
        "corpus": {"repository_relative_id": CORPUS_ID, "bytes": len(corpus), "sha256": digest(corpus), "section_digest_domain": "SHA-256(schema ASCII || NUL || 'section' || NUL || section id ASCII || NUL || exact section bytes)", "strict_section_order": list(sections), "sections": manifest, "sentinels": {"missing_u16": 65535, "missing_u32": 4294967295}, "terminal_codes": {name: index for index, name in enumerate(TERMINALS)}},
        "checks": {"all_forward_children_exact_tensor_nonzero_distinct": True, "digest_collisions_on_differing_exact_bytes_fatal": True, "every_child_has_two_forward_aliases": True, "ordered_maps_complete_and_inverse": True, "all_nine_inverse_equations_recorded": True, "accepted_sources_nonzero_and_factorwise_different": True, "accepted_parents_exact_tensor_nonzero_distinct": True, "accepted_forward_scatter_exact": True, "reciprocal_alias_coverage_complete": True}
    }
    return semantic, corpus

def identity(metadata):
    return metadata.st_dev, metadata.st_ino

def open_directory_nofollow(path):
    require(hasattr(os, "O_NOFOLLOW") and hasattr(os, "O_DIRECTORY"), "runtime lacks required nofollow directory support")
    absolute = os.path.abspath(path)
    descriptor = os.open(os.sep, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        for component in [part for part in absolute.split(os.sep) if part]:
            following = os.open(component, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=descriptor)
            os.close(descriptor)
            descriptor = following
        metadata = os.fstat(descriptor)
        require(stat.S_ISDIR(metadata.st_mode), "output parent is not a directory")
        require(metadata.st_uid == os.geteuid() and metadata.st_mode & 0o022 == 0, "output parent must be owned by the effective user and not group/world writable")
        return descriptor
    except Exception:
        os.close(descriptor)
        raise

def leaf_metadata(handle, name=None):
    try:
        return os.stat(handle["leaf"] if name is None else name, dir_fd=handle["directory_fd"], follow_symlinks=False)
    except FileNotFoundError:
        return None

def protected_identities(protected):
    result = []
    for role, path, initial in protected:
        metadata = os.lstat(path)
        require(not stat.S_ISLNK(metadata.st_mode) and stat.S_ISREG(metadata.st_mode), role + " changed to a symlink or nonregular file")
        result.append((role, initial))
        result.append((role, identity(metadata)))
    return result

def validate_output_pair(handles, protected):
    first, second = handles
    require(not (identity(os.fstat(first["directory_fd"])) == identity(os.fstat(second["directory_fd"])) and first["leaf"] == second["leaf"]), "summary and corpus paths alias textually")
    protected_values = protected_identities(protected)
    final_metadata = []
    for handle in handles:
        metadata = leaf_metadata(handle)
        if handle["published"]:
            expected = handle["published_identity"]
        elif handle["initial_final_fd"] is None:
            expected = None
        else:
            expected = identity(os.fstat(handle["initial_final_fd"]))
        if expected is None:
            require(metadata is None, "absent output leaf appeared before publication")
        else:
            require(metadata is not None and not stat.S_ISLNK(metadata.st_mode) and stat.S_ISREG(metadata.st_mode) and identity(metadata) == expected, "output leaf identity changed before publication")
            for role, protected_identity in protected_values:
                require(identity(metadata) != protected_identity, "output aliases " + role)
        final_metadata.append(metadata)
        if not handle["published"]:
            temporary = leaf_metadata(handle, handle["temporary"])
            require(temporary is not None and stat.S_ISREG(temporary.st_mode) and identity(temporary) == identity(os.fstat(handle["temporary_fd"])), "held output temporary path was rebound")
    if final_metadata[0] is not None and final_metadata[1] is not None:
        require(identity(final_metadata[0]) != identity(final_metadata[1]), "summary and corpus are hard-link aliases")

def prepare_output(path):
    output = os.path.abspath(path)
    leaf = os.path.basename(output)
    require(leaf not in ("", ".", ".."), "invalid output leaf name")
    require(hasattr(os, "O_PATH"), "runtime lacks required metadata-only file support")
    directory_fd = open_directory_nofollow(os.path.dirname(output))
    initial_final_fd = None
    temporary = None
    temporary_fd = None
    try:
        try:
            initial_final_fd = os.open(leaf, os.O_PATH | os.O_NOFOLLOW, dir_fd=directory_fd)
        except FileNotFoundError:
            pass
        if initial_final_fd is not None:
            initial_metadata = os.fstat(initial_final_fd)
            require(stat.S_ISREG(initial_metadata.st_mode), "existing output must be a nofollow regular file")
            observed_metadata = os.stat(leaf, dir_fd=directory_fd, follow_symlinks=False)
            require(identity(observed_metadata) == identity(initial_metadata), "existing output identity changed during capture")
        for unused in range(128):
            candidate = "." + leaf + "." + secrets.token_hex(24) + ".tmp"
            try:
                temporary_fd = os.open(candidate, os.O_RDWR | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600, dir_fd=directory_fd)
                temporary = candidate
                break
            except FileExistsError:
                pass
        require(temporary_fd is not None, "could not reserve unique output temporary")
        return {"path": output, "leaf": leaf, "directory_fd": directory_fd, "temporary": temporary, "temporary_fd": temporary_fd, "published": False, "published_identity": None, "initial_final_fd": initial_final_fd}
    except Exception:
        if initial_final_fd is not None:
            os.close(initial_final_fd)
        if temporary_fd is not None:
            os.close(temporary_fd)
        if temporary is not None:
            try:
                os.unlink(temporary, dir_fd=directory_fd)
            except OSError:
                pass
        os.close(directory_fd)
        raise

def prepare_output_pair(summary_path, corpus_path, protected_paths):
    protected = []
    for role, path in protected_paths:
        metadata = os.lstat(path)
        require(not stat.S_ISLNK(metadata.st_mode) and stat.S_ISREG(metadata.st_mode), role + " is not a nofollow regular file")
        protected.append((role, path, identity(metadata)))
    handles = []
    try:
        handles.append(prepare_output(summary_path))
        handles.append(prepare_output(corpus_path))
        validate_output_pair(handles, protected)
        return handles, protected
    except Exception:
        release_outputs(handles)
        raise

def write_temporary(handle, data):
    descriptor = handle["temporary_fd"]
    os.lseek(descriptor, 0, os.SEEK_SET)
    os.ftruncate(descriptor, 0)
    offset = 0
    while offset < len(data):
        offset += os.write(descriptor, data[offset:])
    os.fchmod(descriptor, 0o644)
    os.fsync(descriptor)

def fsync_directory_fd(descriptor):
    try:
        os.fsync(descriptor)
    except OSError as error:
        if error.errno not in (errno.EINVAL, errno.ENOSYS, errno.ENOTSUP, getattr(errno, "EOPNOTSUPP", -1)):
            raise

def commit_pair(handles, summary_data, corpus_data, protected):
    write_temporary(handles[0], summary_data)
    write_temporary(handles[1], corpus_data)
    validate_output_pair(handles, protected)
    for handle in (handles[1], handles[0]):
        validate_output_pair(handles, protected)
        expected = identity(os.fstat(handle["temporary_fd"]))
        os.replace(handle["temporary"], handle["leaf"], src_dir_fd=handle["directory_fd"], dst_dir_fd=handle["directory_fd"])
        handle["published"] = True
        handle["published_identity"] = expected
        handle["temporary"] = None
        published = leaf_metadata(handle)
        require(published is not None and stat.S_ISREG(published.st_mode) and identity(published) == expected, "published output identity mismatch")
        fsync_directory_fd(handle["directory_fd"])

def release_outputs(handles):
    for handle in handles:
        temporary = handle.get("temporary")
        if temporary is not None:
            try:
                metadata = leaf_metadata(handle, temporary)
                if metadata is not None and identity(metadata) == identity(os.fstat(handle["temporary_fd"])):
                    os.unlink(temporary, dir_fd=handle["directory_fd"])
            except OSError:
                pass
        try:
            initial_final_fd = handle.get("initial_final_fd")
            if initial_final_fd is not None:
                os.close(initial_final_fd)
        except OSError:
            pass
        try:
            os.close(handle["temporary_fd"])
        except OSError:
            pass
        try:
            os.close(handle["directory_fd"])
        except OSError:
            pass

def main():
    try:
        program, repository, source_start, arguments = discover(sys.argv)
        parser = argparse.ArgumentParser()
        parser.add_argument("--root", default=os.path.join(repository, ROOT_ID))
        parser.add_argument("--summary", default=os.path.join(os.path.dirname(program), SUMMARY_BASENAME))
        parser.add_argument("--corpus", default=os.path.join(os.path.dirname(program), CORPUS_BASENAME))
        options = parser.parse_args(arguments)
        root_path = os.path.abspath(options.root)
        raw = read_exact_regular(root_path, "frozen c659 root", expected_size=ROOT_SIZE, maximum=ROOT_SIZE)
        handles, protected = prepare_output_pair(options.summary, options.corpus, (("executing source", program), ("frozen root", root_path)))
        try:
            semantic, corpus = build(parse_root(raw), raw)
            source_report = read_exact_regular(program, "executing source at report", expected_size=len(source_start), maximum=MAX_SOURCE_BYTES)
            require(source_report == source_start, "source bytes changed between start and report")
            semantic_digest = digest(SCHEMA.encode("ascii") + b"\0semantic\0" + canonical_json(semantic))
            document = {"schema": SCHEMA, "semantic": semantic, "implementation": {"source_repository_relative_id": SCRIPT_ID, "source_at_start": {"bytes": len(source_start), "sha256": digest(source_start)}, "source_at_report": {"bytes": len(source_report), "sha256": digest(source_report)}, "statement": "These integrity checksums report regular source-file bytes read at start and report time and require equality; they are not loaded-code attestation or authentication, and runtime/path diagnostics are outside the semantic digest."}, "integrity": {"algorithm": "SHA-256", "classification": "integrity/checksums, not authentication", "semantic_digest_scope": "domain-separated canonical ASCII JSON encoding of the semantic object only", "semantic_sha256": semantic_digest}}
            encoded = canonical_json(document) + b"\n"
            commit_pair(handles, encoded, corpus, protected)
        finally:
            release_outputs(handles)
        return 0
    except (OracleError, OSError, ValueError, struct.error) as error:
        print("oracle error: %s" % error, file=sys.stderr)
        return 2

try:
    code = main()
except Exception as error:
    print("oracle error: %s" % error, file=sys.stderr)
    code = 2
sys.stdout.flush()
sys.stderr.flush()
os._exit(int(code))
'''
exec(compile(CODE, __file__, "exec"))
