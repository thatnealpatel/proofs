"""Deterministic inverse-Plus oracle for the authenticated c659 fixed child.

Run only from a Sage command line of the form

  sage -- Programs/BilinearComplexity/c659_fixed_child_inverse_plus_oracle.sage
"""

import argparse
import collections
import errno
import hashlib
import itertools
import json
import operator
import os
import stat
import struct
import sys
import tempfile


SCRIPT_BASENAME = "c659_fixed_child_inverse_plus_oracle.sage"
SCRIPT_ID = "Programs/BilinearComplexity/c659_fixed_child_inverse_plus_oracle.sage"
ARTIFACT_BASENAME = "c659_fixed_child_inverse_plus_oracle.json"
ARTIFACT_ID = "Programs/BilinearComplexity/c659_fixed_child_inverse_plus_oracle.json"
ROOT_ID = "cmd/c659-plusflip-cert/testdata/4x4x4_m47_c659_iteration5551_Z2.txt"
SCHEMA = "c659-fixed-child-inverse-plus-oracle-v3"
N = 4
FACTOR_BITS = 16
ROOT_RANK = 47
CHILD_RANK = 48
TENSOR_BYTES = 512
MAX_INPUT_BYTES = 65536
EXPECTED_RAW_BYTES = 4524
EXPECTED_RAW_SHA256 = "25f47b5f37d2b7351dd5a2c5da65ff8ef5ba80ce53239d46cdfdef37e6eef403"
EXPECTED_ROOT_ORDERED_SHA256 = "f61518b4864995fe5ba43f1b52819cc563c4c74326442ae12bbc338a491027cb"
EXPECTED_ROOT_UNORDERED_SHA256 = "f2edf6735401e203b532cc85e0783fb47684815a3207b3ec601f8503c48956d1"
EXPECTED_TENSOR_SHA256 = "1ae43419be8f86b7063141475bb207725b43bc4d1c6cae2c11a948b7359863bd"
EXPECTED_CHILD_ORDERED_SHA256 = "913109f1ab4662db336696a853ecb5bf77f60ea5a0b051117c4359469660e24a"
EXPECTED_CHILD_UNORDERED_SHA256 = "0001430818e501c6964f6bf666e52a72cd0514605b3c69460e0d09cf80ec48e9"
ROOT_SLOTS = (7, 13)
CHILD_SLOTS = (45, 46, 47)
bxor = operator.xor
EXPECTED_ORIENTATIONS = (
    ("ijk", (0, 1, 2)),
    ("ikj", (0, 2, 1)),
    ("jik", (1, 0, 2)),
    ("jki", (1, 2, 0)),
    ("kij", (2, 0, 1)),
    ("kji", (2, 1, 0)),
)
ORIENTATIONS = collections.OrderedDict(EXPECTED_ORIENTATIONS)
EXPECTED_FORMULAS = (
    ("0", "(a1,b1+b2,c1);(a1+a2,b2,c2);(a1,b2,c1+c2)"),
    ("1", "(a1,b1,c1+c2);(a2,b1+b2,c2);(a1+a2,b1,c2)"),
    ("2", "(a1+a2,b1,c1);(a2,b2,c1+c2);(a2,b1+b2,c1)"),
)
FORMULAS = collections.OrderedDict(EXPECTED_FORMULAS)
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
EXPECTED_ACCEPTED_FULL_SEMANTIC_COORDINATES = (
    (0, 2, 46, 45, 47),
    (1, 0, 45, 46, 47),
    (2, 1, 45, 46, 47),
    (3, 1, 46, 45, 47),
    (4, 0, 46, 45, 47),
    (5, 2, 45, 46, 47),
)
EXPECTED_ACCEPTED_COMPACT_DESCRIPTORS = (
    (46, 45, 0, 2),
    (45, 46, 1, 0),
    (45, 46, 2, 1),
    (46, 45, 3, 1),
    (46, 45, 4, 0),
    (45, 46, 5, 2),
)
EXPECTED_COMPACT_ALL_BYTES = 1296
EXPECTED_COMPACT_ALL_SHA256 = "e05ef47fc81d499b850748e1c1193280fd622c257b5a82ac5487491175cf4d94"
EXPECTED_COMPACT_ACCEPTED_BYTES = 72
EXPECTED_COMPACT_ACCEPTED_SHA256 = "73fbb5130da5027c305ea14a8e18815d01fc8c7e7413737c69c8337bf330b5fc"
EXPECTED_FULL_ALL_BYTES = 171217
EXPECTED_FULL_ALL_SHA256 = "85578bcb1f46796677c62c97261c6724ebd8b4f21424e63dbaaacac87569e48d"
EXPECTED_FULL_ACCEPTED_BYTES = 65038
EXPECTED_FULL_ACCEPTED_SHA256 = "c2e1d98c809cc14f6a0c00e5b755f6a8fafe1e5b2a9fb2dbb0f3c04a2c86e1f0"
FORWARD_METHOD_LABEL = "plus_three_term_identity_gf2_v1"
INVERSE_METHOD_LABEL = "closed_form_first_two_outputs_then_all_named_equations_v1"
ACCEPTED_CLASS = "accepted_exact_parent_lineage"
REJECTED_CLASS = "inverse_equation_inconsistent"


class OracleError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise OracleError(message)


def require_supported_runtime(argv):
    sage_runtime = sys.modules.get("sage.all")
    require(
        globals().get("__name__") == "sage.all"
        and sage_runtime is not None
        and globals() is vars(sage_runtime)
        and hasattr(sage_runtime, "SageObject"),
        "supported runtime is Sage via: sage -- %s [options]" % SCRIPT_ID,
    )
    require(len(argv) >= 2 and argv[0] == "--", "supported invocation is: sage -- %s [options]" % SCRIPT_ID)


def sha256_bytes(value):
    return hashlib.sha256(value).hexdigest()


def canonical_json(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True, default=int).encode("ascii")


def read_bounded_regular(path, role, reject_symlink=False):
    if reject_symlink:
        metadata = os.lstat(path)
        require(not stat.S_ISLNK(metadata.st_mode), "%s must not be a symbolic link: %s" % (role, path))
    flags = os.O_RDONLY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(path, flags)
    with os.fdopen(descriptor, "rb") as source:
        metadata = os.fstat(source.fileno())
        require(stat.S_ISREG(metadata.st_mode), "%s is not a regular file: %s" % (role, path))
        require(metadata.st_size <= MAX_INPUT_BYTES, "%s exceeds the 64 KiB input limit" % role)
        value = source.read(MAX_INPUT_BYTES + 1)
    require(len(value) <= MAX_INPUT_BYTES, "%s changed or exceeds the 64 KiB input limit" % role)
    return value


def discover_invocation(argv):
    program_text = argv[1]
    require(os.path.basename(program_text) == SCRIPT_BASENAME, "invoked program basename is not %s" % SCRIPT_BASENAME)
    program_path = os.path.abspath(program_text)
    script_bytes = read_bounded_regular(program_path, "executing script", reject_symlink=True)
    repository = os.path.realpath(os.path.join(os.path.dirname(program_path), "..", ".."))
    expected_program = os.path.join(repository, SCRIPT_ID)
    require(os.path.samefile(program_path, expected_program), "executing script is not at repository-relative ID %s" % SCRIPT_ID)
    return program_path, repository, script_bytes, argv[2:]


def read_authenticated_root(path):
    real = os.path.realpath(path)
    raw = read_bounded_regular(real, "root")
    require(len(raw) == EXPECTED_RAW_BYTES, "root has %d bytes, expected %d" % (len(raw), EXPECTED_RAW_BYTES))
    digest = sha256_bytes(raw)
    require(digest == EXPECTED_RAW_SHA256, "unauthenticated root SHA-256 %s" % digest)
    return real, raw


def refuse_protected_output(output_path, protected_paths):
    if output_path == "-":
        return
    output_abs = os.path.abspath(output_path)
    try:
        output_metadata = os.lstat(output_abs)
        require(not stat.S_ISLNK(output_metadata.st_mode), "output final entry is a symbolic link and is refused: %s" % output_abs)
    except FileNotFoundError:
        pass
    output_real = os.path.normcase(os.path.realpath(output_abs))
    for role, protected_path in protected_paths:
        protected_real = os.path.normcase(os.path.realpath(os.path.abspath(protected_path)))
        identity_equal = False
        try:
            identity_equal = os.path.samefile(output_abs, protected_path)
        except FileNotFoundError:
            pass
        require(not (output_real == protected_real or identity_equal), "output aliases the %s and is refused: %s" % (role, output_abs))


def parse_native(raw):
    try:
        lines = raw.decode("ascii").splitlines()
    except UnicodeDecodeError as error:
        raise OracleError("native root is not ASCII: %s" % error)
    require(len(lines) == 4, "native root must contain exactly four lines")
    require(lines[0].split() == ["4", "4", "4", "47"], "native header is not exactly 4 4 4 47")
    factors = []
    for mode, line in enumerate(lines[1:]):
        tokens = line.split()
        require(len(tokens) == ROOT_RANK * FACTOR_BITS, "factor line %d token count mismatch" % (mode + 1))
        require(all(token in ("0", "1") for token in tokens), "factor line %d contains a non-binary token" % (mode + 1))
        words = []
        for slot in range(ROOT_RANK):
            words.append(sum((int(tokens[slot * FACTOR_BITS + coordinate]) << coordinate) for coordinate in range(FACTOR_BITS)))
        factors.append(words)
    return tuple(tuple(int(factors[mode][slot]) for mode in range(3)) for slot in range(ROOT_RANK))


def bit_positions(value):
    value = int(value)
    while value:
        low = value & -value
        yield int(low.bit_length() - 1)
        value -= low


def outer_tensor(term):
    result = 0
    for first in bit_positions(term[0]):
        for second in bit_positions(term[1]):
            base = (first * FACTOR_BITS + second) * FACTOR_BITS
            for third in bit_positions(term[2]):
                result |= 1 << (base + third)
    return int(result)


def tensor_of_terms(terms):
    result = 0
    for term in terms:
        result = bxor(result, outer_tensor(term))
    return int(result)


def tensor_matches(terms, expected):
    return tensor_of_terms(terms) == int(expected)


def multiplication_tensor():
    result = 0
    for i in range(N):
        for j in range(N):
            for k in range(N):
                first, second, third = N * i + j, N * j + k, N * k + i
                result |= 1 << ((first * FACTOR_BITS + second) * FACTOR_BITS + third)
    return int(result)


def tensor_sha256(value):
    return sha256_bytes(int(value).to_bytes(TENSOR_BYTES, "little"))


def header(term_count):
    return struct.pack("<4H", N, N, N, int(term_count))


def ordered_factor_major_bytes(terms):
    output = bytearray(header(len(terms)))
    for mode in range(3):
        for term in terms:
            output.extend(struct.pack("<H", int(term[mode])))
    return bytes(output)


def unordered_canonical_bytes(terms):
    output = bytearray(header(len(terms)))
    for term in sorted(tuple(tuple(int(word) for word in term) for term in terms)):
        output.extend(struct.pack("<HHH", *term))
    return bytes(output)


def term_hex(term):
    return ["%04x" % int(word) for word in term]


def plus_local(first, second, positions, variant):
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
    for oriented_term in oriented:
        term = [0, 0, 0]
        term[i], term[j], term[k] = oriented_term
        result.append(tuple(int(word) for word in term))
    return tuple(result)


def inverse_plus(outputs, positions, variant):
    oriented_outputs = tuple(tuple(term[position] for position in positions) for term in outputs)
    first_output, second_output, actual_third = oriented_outputs
    if variant == 0:
        a1, b2, c1 = first_output[0], second_output[1], first_output[2]
        a2, b1, c2 = bxor(second_output[0], a1), bxor(first_output[1], b2), second_output[2]
    elif variant == 1:
        a1, b1, c2 = first_output[0], first_output[1], second_output[2]
        c1, a2, b2 = bxor(first_output[2], c2), second_output[0], bxor(second_output[1], b1)
    elif variant == 2:
        a2, b1, c1 = second_output[0], first_output[1], first_output[2]
        a1, b2, c2 = bxor(first_output[0], a2), second_output[1], bxor(second_output[2], c1)
    else:
        raise OracleError("invalid inverse Plus variant")
    oriented_sources = ((a1, b1, c1), (a2, b2, c2))
    sources = []
    for oriented_source in oriented_sources:
        source = [0, 0, 0]
        for oriented_mode, original_mode in enumerate(positions):
            source[original_mode] = oriented_source[oriented_mode]
        sources.append(tuple(int(word) for word in source))
    replayed = plus_local(sources[0], sources[1], positions, variant)
    replayed_oriented = tuple(tuple(term[position] for position in positions) for term in replayed)
    results = collections.OrderedDict()
    coordinate = 0
    for output_index in range(3):
        for factor_index in range(3):
            results[EQUATION_NAMES[variant][coordinate]] = replayed_oriented[output_index][factor_index] == oriented_outputs[output_index][factor_index]
            coordinate += 1
    return tuple(sources), oriented_outputs, replayed, results


def reconstruct_parent(survivors, sources):
    parent = []
    survivor_index = 0
    for slot in range(ROOT_RANK):
        if slot == ROOT_SLOTS[0]:
            parent.append(sources[0])
        elif slot == ROOT_SLOTS[1]:
            parent.append(sources[1])
        else:
            parent.append(survivors[survivor_index])
            survivor_index += 1
    require(survivor_index == len(survivors), "parent reconstruction did not consume every survivor")
    return tuple(parent)


def zero_factor_terms(terms):
    return [slot for slot, term in enumerate(terms) if any(word == 0 for word in term)]


def duplicate_groups(terms):
    slots_by_term = collections.OrderedDict()
    for slot, term in enumerate(terms):
        slots_by_term.setdefault(term, []).append(slot)
    return [slots for slots in slots_by_term.values() if len(slots) > 1]


def run_synthetic_negative_tests():
    one = ((1, 1, 1),)
    require(tensor_matches(one, outer_tensor((1, 1, 1))), "positive tensor validator self-test failed")
    require(not tensor_matches(((1, 1, 2),), outer_tensor((1, 1, 1))), "tensor validator accepted a synthetic wrong tensor")
    require(zero_factor_terms(((1, 2, 3), (0, 2, 3))) == [1], "zero-factor validator synthetic negative failed")
    require(duplicate_groups(((1, 2, 3), (4, 5, 6), (1, 2, 3))) == [[0, 2]], "duplicate-term validator synthetic negative failed")


def make_fixed_child(root_terms, expected_tensor):
    source_first, source_second = (root_terms[slot] for slot in ROOT_SLOTS)
    inserted = plus_local(source_first, source_second, ORIENTATIONS["ikj"], 0)
    survivors = tuple(term for slot, term in enumerate(root_terms) if slot not in ROOT_SLOTS)
    child = survivors + inserted
    require(len(child) == CHILD_RANK, "fixed child does not have 48 terms")
    require(tensor_matches(child, expected_tensor), "fixed child tensor replay failed")
    ordered = ordered_factor_major_bytes(child)
    unordered = unordered_canonical_bytes(child)
    require(sha256_bytes(ordered) == EXPECTED_CHILD_ORDERED_SHA256, "fixed child ordered SHA-256 mismatch")
    require(sha256_bytes(unordered) == EXPECTED_CHILD_UNORDERED_SHA256, "fixed child unordered SHA-256 mismatch")
    require(not zero_factor_terms(child), "fixed child contains a zero-factor term")
    require(not duplicate_groups(child), "fixed child contains duplicate complete terms")
    return survivors, child, inserted, ordered, unordered


def lineage_for_parent(parent, root_terms):
    identity = tuple(range(ROOT_RANK))
    transposition = list(identity)
    transposition[ROOT_SLOTS[0]], transposition[ROOT_SLOTS[1]] = transposition[ROOT_SLOTS[1]], transposition[ROOT_SLOTS[0]]
    transposition = tuple(transposition)
    exact = parent == root_terms
    swapped = all(parent[parent_slot] == root_terms[transposition[parent_slot]] for parent_slot in range(ROOT_RANK))
    require(exact != swapped, "parent must have exactly one fixed c659 lineage")
    mapping = identity if exact else transposition
    literal_equality = all(parent[parent_slot] == root_terms[mapping[parent_slot]] for parent_slot in range(ROOT_RANK))
    return exact, mapping, literal_equality


def accepted_record(root_terms, child, survivors, descriptor, sources, oriented_outputs, replayed_outputs, equation_results):
    assignment = tuple(descriptor["assignment"])
    positions = tuple(descriptor["positions"])
    variant = descriptor["variant"]
    parent = reconstruct_parent(survivors, sources)
    outputs = tuple(child[slot] for slot in assignment)
    replayed_child = list(survivors) + [None, None, None]
    for output_index, child_slot in enumerate(assignment):
        replayed_child[child_slot] = replayed_outputs[output_index]
    replayed_child = tuple(replayed_child)
    exact_root, mapping, literal_equality = lineage_for_parent(parent, root_terms)
    lineage_recognized = exact_root or all(parent[parent_slot] == root_terms[mapping[parent_slot]] for parent_slot in range(ROOT_RANK))
    generating_alias = lineage_recognized and literal_equality
    alternate_exact_parent = not generating_alias
    literal_factor_equality_witnesses = []
    for parent_slot, root_slot in enumerate(mapping):
        parent_factors = parent[parent_slot]
        root_factors = root_terms[root_slot]
        factor_equalities = [parent_factors[mode] == root_factors[mode] for mode in range(3)]
        literal_factor_equality_witnesses.append({
            "parent_slot": parent_slot,
            "root_slot": root_slot,
            "parent_factors_hex": term_hex(parent_factors),
            "root_factors_hex": term_hex(root_factors),
            "factor_equalities": factor_equalities,
            "complete_term_equal": all(factor_equalities),
        })
    local_tensor = tensor_of_terms(sources) == tensor_of_terms(outputs)
    parent_tensor = tensor_matches(parent, multiplication_tensor())
    parent_zeros = zero_factor_terms(parent)
    parent_duplicates = duplicate_groups(parent)
    source_zeros = zero_factor_terms(sources)
    source_collisions = [mode for mode in range(3) if sources[0][mode] == sources[1][mode]]
    source_legal = not source_zeros and not source_collisions
    require(replayed_child == child, "accepted inverse did not replay the child")
    require(all(equation_results.values()), "accepted inverse has a false named equation")
    require(local_tensor, "accepted inverse failed local tensor replay")
    require(generating_alias and not alternate_exact_parent, "accepted inverse lacks exact lineage witness")
    return {
        "accepted": True,
        "classification": ACCEPTED_CLASS,
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
        "inverse_equations": {
            "all_named_equations_hold": True,
            "named_results": dict(equation_results),
            "oriented_actual_outputs": [list(term) for term in oriented_outputs],
        },
        "forward_plus_local_exact": True,
        "scatter_replayed_fixed_child_exactly": replayed_child == child,
        "local_tensor_replayed_exactly": local_tensor,
        "generating_alias": generating_alias,
        "alternate_exact_parent": alternate_exact_parent,
        "ordered_parent_lineage": "c659_identity" if exact_root else "c659_transposition_(7 13)",
        "parent_lineage_witness": {
            "root_id": ROOT_ID,
            "parent_slot_to_root_slot": list(mapping),
            "literal_factor_equality": literal_equality,
            "literal_factor_equality_witnesses": literal_factor_equality_witnesses,
            "source_parent_slots": list(ROOT_SLOTS),
            "source_terms_equal_mapped_root_slots": all(sources[index] == root_terms[mapping[slot]] for index, slot in enumerate(ROOT_SLOTS)),
        },
        "parent_exact_root_order_match": exact_root,
        "parent_all_47_nonzero": not parent_zeros,
        "parent_all_47_complete_terms_distinct": not parent_duplicates,
        "parent_zero_factor_terms": parent_zeros,
        "parent_duplicate_complete_term_groups": parent_duplicates,
        "parent_tensor_replayed_exactly": parent_tensor,
        "parent_ordered_factor_major_sha256": sha256_bytes(ordered_factor_major_bytes(parent)),
        "parent_unordered_canonical_sha256": sha256_bytes(unordered_canonical_bytes(parent)),
        "reconstructed_parent_term_count": len(parent),
        "source_pair": [list(term) for term in sources],
        "source_pair_hex": [term_hex(term) for term in sources],
        "source_zero_factor_terms": source_zeros,
        "source_factor_collision_modes": source_collisions,
        "source_precondition_legal": source_legal,
    }, parent


def rejected_record(child, descriptor, oriented_outputs, replayed_outputs, equation_results):
    assignment = tuple(descriptor["assignment"])
    outputs = tuple(child[slot] for slot in assignment)
    return {
        "accepted": False,
        "classification": REJECTED_CLASS,
        "descriptor_index": descriptor["descriptor_index"],
        "assignment": list(assignment),
        "orientation": descriptor["orientation"],
        "orientation_index": descriptor["orientation_index"],
        "positions": list(descriptor["positions"]),
        "variant": descriptor["variant"],
        "formula": FORMULAS[str(descriptor["variant"])],
        "forward_method_label": FORWARD_METHOD_LABEL,
        "inverse_method_label": INVERSE_METHOD_LABEL,
        "output_slots": list(assignment),
        "output_terms_hex": [term_hex(term) for term in outputs],
        "inverse_equations": {
            "all_named_equations_hold": False,
            "named_results": dict(equation_results),
            "oriented_actual_outputs": [list(term) for term in oriented_outputs],
            "oriented_replayed_outputs": [[term[position] for position in descriptor["positions"]] for term in replayed_outputs],
        },
        "rejection_class": REJECTED_CLASS,
    }


def record_stream(records):
    return b"".join(canonical_json(record) + b"\n" for record in records)


def compact_descriptor_stream(descriptors):
    return b"".join(canonical_json(list(descriptor)) + b"\n" for descriptor in descriptors)


def enumerate_inverse(root_terms, survivors, child):
    accepted, rejected, all_records, descriptors, parents, sources_seen = [], [], [], [], [], []
    full_semantic_coordinates, accepted_full_semantic_coordinates = [], []
    compact_descriptors, accepted_compact_descriptors = [], []
    assignments = tuple(itertools.permutations(CHILD_SLOTS))
    descriptor_index = 0
    for orientation_index, (orientation_name, positions) in enumerate(ORIENTATIONS.items()):
        for variant in range(3):
            for assignment in assignments:
                outputs = tuple(child[slot] for slot in assignment)
                sources, oriented_outputs, replayed_outputs, equation_results = inverse_plus(outputs, positions, variant)
                accepted_flag = all(equation_results.values())
                classification = ACCEPTED_CLASS if accepted_flag else REJECTED_CLASS
                descriptor = {
                    "descriptor_index": descriptor_index,
                    "orientation_index": orientation_index,
                    "orientation": orientation_name,
                    "positions": list(positions),
                    "variant": variant,
                    "formula": FORMULAS[str(variant)],
                    "assignment": list(assignment),
                    "accepted": accepted_flag,
                    "classification": classification,
                }
                full_semantic_coordinate = (orientation_index, variant) + tuple(assignment)
                compact_descriptor = (assignment[0], assignment[1], orientation_index, variant)
                full_semantic_coordinates.append(full_semantic_coordinate)
                compact_descriptors.append(compact_descriptor)
                descriptors.append(descriptor)
                if accepted_flag:
                    record, parent = accepted_record(root_terms, child, survivors, descriptor, sources, oriented_outputs, replayed_outputs, equation_results)
                    accepted.append(record)
                    accepted_full_semantic_coordinates.append(full_semantic_coordinate)
                    accepted_compact_descriptors.append(compact_descriptor)
                    parents.append(parent)
                    sources_seen.append(sources)
                else:
                    record = rejected_record(child, descriptor, oriented_outputs, replayed_outputs, equation_results)
                    rejected.append(record)
                all_records.append(record)
                descriptor_index += 1
    require(tuple(EXPECTED_ORIENTATIONS) == tuple(ORIENTATIONS.items()), "orientation permutation labels or order changed")
    require(tuple(ORIENTATIONS.values()) == tuple(itertools.permutations((0, 1, 2))), "orientation permutations are not exact lexicographic S3")
    require(tuple(EXPECTED_FORMULAS) == tuple(FORMULAS.items()), "Plus formulas or order changed")
    require(len(descriptors) == 108 and len(set(full_semantic_coordinates)) == 108, "descriptor domain is not exactly 108 unique full semantic coordinates")
    expected_full_semantic_coordinates = tuple((orientation_index, variant) + assignment for orientation_index in range(6) for variant in range(3) for assignment in assignments)
    require(tuple(full_semantic_coordinates) == expected_full_semantic_coordinates, "full semantic coordinate enumeration order changed")
    require(tuple(accepted_full_semantic_coordinates) == EXPECTED_ACCEPTED_FULL_SEMANTIC_COORDINATES, "accepted full semantic coordinates changed")
    require(len(compact_descriptors) == 108 and len(set(compact_descriptors)) == 108, "compact descriptor domain is not exactly 108 unique descriptors")
    require(tuple(accepted_compact_descriptors) == EXPECTED_ACCEPTED_COMPACT_DESCRIPTORS, "accepted compact descriptors changed")
    require(len(accepted) == 6 and len(rejected) == 102, "accepted/rejected descriptor partition count changed")
    require([descriptor["accepted"] for descriptor in descriptors] == [coordinate in EXPECTED_ACCEPTED_FULL_SEMANTIC_COORDINATES for coordinate in full_semantic_coordinates], "accepted/rejected sequence flags changed")
    require(all(descriptor["classification"] == (ACCEPTED_CLASS if descriptor["accepted"] else REJECTED_CLASS) for descriptor in descriptors), "descriptor classification label mismatch")
    require([record["descriptor_index"] for record in all_records] == list(range(108)), "full semantic records were omitted or reordered")
    frozen_accepted_descriptors = [descriptor for descriptor in descriptors if descriptor["accepted"]]
    require(len(frozen_accepted_descriptors) == 6, "frozen accepted descriptor list does not contain six records")
    compact_all = compact_descriptor_stream(compact_descriptors)
    compact_accepted = compact_descriptor_stream(accepted_compact_descriptors)
    full_all = record_stream(all_records)
    full_accepted = record_stream(accepted)
    require(len(compact_all) == EXPECTED_COMPACT_ALL_BYTES and sha256_bytes(compact_all) == EXPECTED_COMPACT_ALL_SHA256, "compact all-descriptor stream changed")
    require(len(compact_accepted) == EXPECTED_COMPACT_ACCEPTED_BYTES and sha256_bytes(compact_accepted) == EXPECTED_COMPACT_ACCEPTED_SHA256, "compact accepted-descriptor stream changed")
    if EXPECTED_FULL_ALL_SHA256 is not None:
        require(len(full_all) == EXPECTED_FULL_ALL_BYTES and sha256_bytes(full_all) == EXPECTED_FULL_ALL_SHA256, "full all-record semantic stream changed")
        require(len(full_accepted) == EXPECTED_FULL_ACCEPTED_BYTES and sha256_bytes(full_accepted) == EXPECTED_FULL_ACCEPTED_SHA256, "full accepted-record semantic stream changed")
    return accepted, rejected, all_records, descriptors, frozen_accepted_descriptors, parents, sources_seen, compact_all, compact_accepted, full_all, full_accepted


def build_semantic(raw, root_terms):
    run_synthetic_negative_tests()
    expected_tensor = multiplication_tensor()
    represented = tensor_of_terms(root_terms)
    require(tensor_sha256(expected_tensor) == EXPECTED_TENSOR_SHA256, "multiplication tensor encoding mismatch")
    require(represented == expected_tensor, "authenticated root does not replay the multiplication tensor")
    ordered_root = ordered_factor_major_bytes(root_terms)
    unordered_root = unordered_canonical_bytes(root_terms)
    require(len(ordered_root) == 290 and len(unordered_root) == 290, "root binary payload length mismatch")
    require(sha256_bytes(ordered_root) == EXPECTED_ROOT_ORDERED_SHA256, "root ordered payload digest mismatch")
    require(sha256_bytes(unordered_root) == EXPECTED_ROOT_UNORDERED_SHA256, "root unordered payload digest mismatch")
    root_zeros, root_duplicates = zero_factor_terms(root_terms), duplicate_groups(root_terms)
    require(not root_zeros and not root_duplicates, "authenticated root fails nonzero/distinct validation")
    survivors, child, inserted, child_ordered, child_unordered = make_fixed_child(root_terms, expected_tensor)
    accepted, rejected, all_records, descriptors, frozen_accepted_descriptors, parents, source_pairs, compact_all, compact_accepted, full_all, full_accepted = enumerate_inverse(root_terms, survivors, child)
    accepted_unique_parent_ordered_payload_count = len(set(ordered_factor_major_bytes(parent) for parent in parents))
    accepted_unique_parent_unordered_payload_count = len(set(unordered_canonical_bytes(parent) for parent in parents))
    accepted_unique_source_pair_ordered_count = len(set(source_pairs))
    counts = {
        "descriptor_total_count": len(descriptors),
        "accepted_descriptor_count": len(accepted),
        "rejected_descriptor_count": len(rejected),
        "inverse_equation_consistent_count": len(accepted),
        "inverse_equation_inconsistent_count": len(rejected),
        "accepted_exact_parent_lineage_count": sum(record["generating_alias"] for record in accepted),
        "accepted_alternate_exact_parent_count": sum(record["alternate_exact_parent"] for record in accepted),
        "accepted_local_tensor_replay_count": sum(record["local_tensor_replayed_exactly"] for record in accepted),
        "accepted_scatter_fixed_child_replay_count": sum(record["scatter_replayed_fixed_child_exactly"] for record in accepted),
        "accepted_parent_tensor_replay_count": sum(record["parent_tensor_replayed_exactly"] for record in accepted),
        "accepted_parent_nonzero_count": sum(record["parent_all_47_nonzero"] for record in accepted),
        "accepted_parent_complete_term_distinct_count": sum(record["parent_all_47_complete_terms_distinct"] for record in accepted),
        "accepted_source_precondition_legal_count": sum(record["source_precondition_legal"] for record in accepted),
        "accepted_unique_reconstructed_parent_ordered_payload_count": accepted_unique_parent_ordered_payload_count,
        "accepted_unique_reconstructed_parent_unordered_payload_count": accepted_unique_parent_unordered_payload_count,
        "accepted_unique_reconstructed_source_pair_ordered_count": accepted_unique_source_pair_ordered_count,
    }
    expected_counts = {
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
    require(counts == expected_counts, "inverse counts, validations, or deduplication witnesses changed")
    return {
        "schema": SCHEMA,
        "status": "complete",
        "field": {"name": "GF(2)", "characteristic": 2, "addition": "bitwise XOR"},
        "root": {
            "repository_relative_id": ROOT_ID,
            "fixture_name": "c659_iteration5551_Z2",
            "dimensions": [N, N, N],
            "rank": len(root_terms),
            "raw_bytes": len(raw),
            "raw_sha256": sha256_bytes(raw),
            "ordered_factor_major_bytes": len(ordered_root),
            "ordered_factor_major_sha256": sha256_bytes(ordered_root),
            "unordered_canonical_bytes": len(unordered_root),
            "unordered_canonical_sha256": sha256_bytes(unordered_root),
            "tensor_sha256": tensor_sha256(represented),
            "tensor_replayed_exactly": True,
            "zero_factor_terms": root_zeros,
            "duplicate_complete_term_groups": root_duplicates,
        },
        "fixed_child": {
            "construction": "remove root slots 7 and 13; Plus variant 0 under ikj=(0,2,1); append outputs in formula order at child slots 45,46,47",
            "source_root_slots": list(ROOT_SLOTS),
            "orientation": "ikj",
            "positions": list(ORIENTATIONS["ikj"]),
            "variant": 0,
            "formula": FORMULAS["0"],
            "forward_method_label": FORWARD_METHOD_LABEL,
            "term_count": len(child),
            "insertion_slots": list(CHILD_SLOTS),
            "slot_to_term_hex": {str(slot): term_hex(child[slot]) for slot in CHILD_SLOTS},
            "inserted_terms_hex_in_formula_order": [term_hex(term) for term in inserted],
            "ordered_factor_major_bytes": len(child_ordered),
            "ordered_factor_major_sha256": sha256_bytes(child_ordered),
            "unordered_canonical_bytes": len(child_unordered),
            "unordered_canonical_sha256": sha256_bytes(child_unordered),
            "tensor_replayed_exactly": True,
            "all_terms_nonzero": True,
            "all_complete_terms_distinct": True,
        },
        "inverse_method": {
            "method_label": INVERSE_METHOD_LABEL,
            "forward_method_label": FORWARD_METHOD_LABEL,
            "enumeration_order": "orientation-major, variant-major, lexicographic assignment-major",
            "assignment_semantics": "assignment is the child-slot triple assigned respectively to formula outputs 0,1,2",
            "orientation_order": list(ORIENTATIONS),
            "orientation_positions": [list(positions) for positions in ORIENTATIONS.values()],
            "variant_order": [0, 1, 2],
            "formulas": dict(FORMULAS),
            "named_equations_by_variant": {str(variant): list(EQUATION_NAMES[variant]) for variant in range(3)},
            "parent_reconstruction": "retain child slots 0..44 as survivors and insert the ordered reconstructed source pair at parent slots 7 and 13",
        },
        "enumeration": {
            "full_semantic_coordinate_schema": ["orientation_index", "variant", "formula_output0_child_slot", "formula_output1_child_slot", "formula_output2_child_slot"],
            "compact_descriptor_schema": ["slotX", "slotY", "orientationIndex", "variant"],
            "compact_descriptor_semantics": "slotX and slotY are the child slots assigned to formula outputs 0 and 1; slotZ/formula output 2 is the remaining member of {45,46,47}",
            "descriptors": descriptors,
            "frozen_accepted_descriptors": frozen_accepted_descriptors,
            "frozen_accepted_full_semantic_coordinates": [list(coordinate) for coordinate in EXPECTED_ACCEPTED_FULL_SEMANTIC_COORDINATES],
            "frozen_accepted_compact_descriptors": [list(descriptor) for descriptor in EXPECTED_ACCEPTED_COMPACT_DESCRIPTORS],
            "accepted_descriptor_indices_in_enumeration_order": [descriptor["descriptor_index"] for descriptor in frozen_accepted_descriptors],
            "rejected_descriptor_indices_in_enumeration_order": [descriptor["descriptor_index"] for descriptor in descriptors if not descriptor["accepted"]],
        },
        "accepted_descriptors": accepted,
        "rejected_descriptors": rejected,
        "counts": counts,
        "deduplication": {
            "domain": "the six accepted semantic records, retaining multiplicity before unique-key counting",
            "accepted_record_count_before_deduplication": len(accepted),
            "reconstructed_parent_ordered_key": "ordered factor-major binary payload including header",
            "reconstructed_parent_unordered_key": "lexicographically sorted complete-term binary payload including header",
            "reconstructed_source_pair_ordered_key": "ordered pair of three-factor source terms",
        },
        "streams": {
            "compact_descriptor_streams": {
                "encoding": "canonical ASCII [slotX,slotY,orientationIndex,variant] plus LF per descriptor; slotZ/formula output 2 is the remaining member of {45,46,47}",
                "all_bytes": len(compact_all),
                "all_sha256": sha256_bytes(compact_all),
                "accepted_bytes": len(compact_accepted),
                "accepted_sha256": sha256_bytes(compact_accepted),
            },
            "full_semantic_record_streams": {
                "encoding": "one complete canonical JSON semantic record plus LF, in descriptor enumeration order",
                "all_bytes": len(full_all),
                "all_sha256": sha256_bytes(full_all),
                "accepted_bytes": len(full_accepted),
                "accepted_sha256": sha256_bytes(full_accepted),
            },
        },
        "self_checks": {
            "orientation_permutations_and_order_frozen": True,
            "formula_text_and_method_labels_frozen": True,
            "all_108_full_semantic_coordinates_unique_and_ordered": True,
            "all_108_compact_descriptors_unique_and_ordered": True,
            "accepted_rejected_sequence_partition_frozen": True,
            "accepted_full_semantic_coordinates_frozen": True,
            "accepted_compact_descriptors_frozen": True,
            "six_accepted_descriptors_frozen": True,
            "literal_factor_equality_witnesses_complete": all(len(record["parent_lineage_witness"]["literal_factor_equality_witnesses"]) == ROOT_RANK for record in accepted),
            "compact_stream_digests_frozen": True,
            "full_semantic_stream_digests_frozen": EXPECTED_FULL_ALL_SHA256 is not None,
            "synthetic_tensor_negative_passed": True,
            "synthetic_zero_factor_negative_passed": True,
            "synthetic_duplicate_term_negative_passed": True,
        },
    }


def authenticate_document(semantic, program_path, source_at_start):
    source_at_report = read_bounded_regular(program_path, "executing script at report time", reject_symlink=True)
    require(source_at_report == source_at_start, "executing script bytes changed between oracle start and report time")
    document = dict(semantic)
    document["implementation"] = {
        "repository_relative_id": SCRIPT_ID,
        "artifact_repository_relative_id": ARTIFACT_ID,
        "source_bytes_read_at_oracle_start": {"bytes": len(source_at_start), "sha256": sha256_bytes(source_at_start)},
        "source_bytes_read_at_report_time": {"bytes": len(source_at_report), "sha256": sha256_bytes(source_at_report)},
        "source_binding_statement": "hashes report actual source-file bytes read at oracle start and again at report time; equality is required",
        "runtime_guard_statement": "generation requires the sage.all execution namespace and the Sage -- argv delimiter; this ordinary-runtime guard is not attestation against a malicious in-process caller able to forge globals",
    }
    payload = canonical_json(document)
    document["authentication"] = {
        "algorithm": "SHA-256",
        "canonicalization": "ASCII JSON with sorted keys and compact separators",
        "scope": "all top-level fields except authentication",
        "semantic_and_source_binding_sha256": sha256_bytes(payload),
    }
    return document


def fsync_containing_directory(directory):
    flags = os.O_RDONLY
    if hasattr(os, "O_DIRECTORY"):
        flags |= os.O_DIRECTORY
    unsupported = {errno.EINVAL, errno.ENOSYS, errno.ENOTSUP}
    if hasattr(errno, "EOPNOTSUPP"):
        unsupported.add(errno.EOPNOTSUPP)
    try:
        descriptor = os.open(directory, flags)
    except OSError as error:
        if error.errno in unsupported:
            return
        raise
    try:
        try:
            os.fsync(descriptor)
        except OSError as error:
            if error.errno not in unsupported:
                raise
    finally:
        os.close(descriptor)


def write_document(path, document):
    encoded = canonical_json(document) + b"\n"
    if path == "-":
        sys.stdout.buffer.write(encoded)
        return
    output_abs = os.path.abspath(path)
    directory = os.path.dirname(output_abs)
    require(os.path.isdir(directory), "output directory does not exist: %s" % directory)
    descriptor, temporary = tempfile.mkstemp(prefix=".%s." % os.path.basename(output_abs), dir=directory)
    try:
        with os.fdopen(descriptor, "wb") as destination:
            os.fchmod(destination.fileno(), 0o644)
            destination.write(encoded)
            destination.flush()
            os.fsync(destination.fileno())
        try:
            metadata = os.lstat(output_abs)
            require(not stat.S_ISLNK(metadata.st_mode), "output final entry became a symbolic link and is refused: %s" % output_abs)
        except FileNotFoundError:
            pass
        os.replace(temporary, output_abs)
        fsync_containing_directory(directory)
    except Exception:
        try:
            os.unlink(temporary)
        except OSError:
            pass
        raise


def parse_arguments(arguments, repository, program_path):
    parser = argparse.ArgumentParser(description="Emit the bounded authenticated c659 inverse-Plus oracle.")
    parser.add_argument("--root", default=os.path.join(repository, ROOT_ID), help="authenticated c659 fixture bytes")
    parser.add_argument("--output", default=os.path.join(os.path.dirname(program_path), ARTIFACT_BASENAME), help="deterministic JSON artifact path, or - for stdout")
    return parser.parse_args(arguments)


def main():
    try:
        program_path, repository, source_at_start, arguments = discover_invocation(sys.argv)
        args = parse_arguments(arguments, repository, program_path)
        root_path, raw = read_authenticated_root(args.root)
        refuse_protected_output(args.output, (("executing script", program_path), ("authenticated root", root_path)))
        semantic = build_semantic(raw, parse_native(raw))
        document = authenticate_document(semantic, program_path, source_at_start)
        write_document(args.output, document)
        return 0
    except (OracleError, OSError, ValueError) as error:
        print("oracle error: %s" % error, file=sys.stderr)
        return 2


try:
    require_supported_runtime(sys.argv)
except (OracleError, OSError, ValueError) as error:
    print("oracle error: %s" % error, file=sys.stderr)
    sys.exit(2)

exit_code = main()
if __name__ == "sage.all":
    sys.stdout.flush()
    sys.stderr.flush()
    os._exit(int(exit_code))
sys.exit(exit_code)
