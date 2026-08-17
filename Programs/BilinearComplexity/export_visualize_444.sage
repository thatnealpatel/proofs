#!/usr/bin/env sage
"""Generate the Tensor Gate Lens <4,4,4> certificates exactly.

Run from the repository root:

  timeout 300 sage Programs/BilinearComplexity/export_visualize_444.sage \
    cmd/visualize/static

The rank-49 factors are loaded from q2_strassen2.sage, including its exact
verification and its (block, inner) -> global row-major permutation.  The
rank-48 parser reads the local paper appendix but emits a self-contained JSON
asset.  It rejects missing/duplicate entries, malformed coefficients, and
non-4x4 matrices before doing an exhaustive exact QQ reconstruction.

Appendix convention: the paper states that vec(O_j), vec(P_j), and vec(Q_j^T)
are the U, V, W rows.  Exact candidate reconstruction confirms that the
visualizer's row-major factors are therefore A = row-major O, B = row-major P,
and C = row-major transpose(Q).  In particular, using Q without the transpose
does not reconstruct the visualizer target.
"""

import itertools
import json
import os
import re
import sys

SCRIPT_DIR = os.path.join(os.getcwd(), "Programs", "BilinearComplexity")
if not os.path.isfile(os.path.join(SCRIPT_DIR, "q2_strassen2.sage")):
    raise SystemExit("run this generator from the repository root")
REPO_ROOT = os.getcwd()
REFERENCE = os.path.join(
    REPO_ROOT,
    "References",
    "BilinearComplexity",
    "arXiv-2602-13171",
    "ArXiv_version.tex",
)
OUTDIR = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
    REPO_ROOT, "cmd", "visualize", "static"
)
if len(sys.argv) > 2:
    raise SystemExit("usage: export_visualize_444.sage [output-directory]")


def target_tensor(n):
    return {
        (i * n + j, j * n + k, i * n + k): QQ(1)
        for i in range(n)
        for j in range(n)
        for k in range(n)
    }


def reconstruct(factors):
    got = {}
    for A, B, C in factors:
        for a, av in enumerate(A):
            if not av:
                continue
            for b, bv in enumerate(B):
                if not bv:
                    continue
                for c, cv in enumerate(C):
                    if cv:
                        key = (a, b, c)
                        got[key] = got.get(key, QQ(0)) + av * bv * cv
    return {key: value for key, value in got.items() if value}


def verify_certificate(factors, n, label):
    expected = target_tensor(n)
    got = reconstruct(factors)
    if got != expected:
        keys = sorted(set(got) | set(expected))
        errors = [
            (key, got.get(key, QQ(0)), expected.get(key, QQ(0)))
            for key in keys
            if got.get(key, QQ(0)) != expected.get(key, QQ(0))
        ]
        raise ValueError(
            "%s: exact reconstruction failed at %d coordinates; first: %s"
            % (label, len(errors), errors[:5])
        )
    # Equality of sparse maps checks every one of the n^6 ambient coordinates:
    # absent coordinates are exactly zero on both sides.
    print("%s: VERIFIED over QQ (rank %d, %d ambient coordinates)" % (
        label, len(factors), n**6
    ), file=sys.stderr)


def rational_string(value):
    value = QQ(value)
    return str(value.numerator()) if value.denominator() == 1 else "%s/%s" % (
        value.numerator(), value.denominator()
    )


def export_certificate(name, source, factors, n, convention, path):
    verify_certificate(factors, n, name)
    products = [
        av * bv * cv
        for A, B, C in factors
        for av in A if av
        for bv in B if bv
        for cv in C if cv
    ]
    scale = lcm([value.denominator() for value in products])
    terms = []
    summed = {}
    for A, B, C in factors:
        entries = []
        for a, av in enumerate(A):
            if not av:
                continue
            for b, bv in enumerate(B):
                if not bv:
                    continue
                for c, cv in enumerate(C):
                    value = scale * av * bv * cv
                    if not value:
                        continue
                    if value not in ZZ:
                        raise AssertionError("scaled term coefficient is not integral")
                    integer = int(value)
                    entries.append([int(a), int(b), int(c), integer])
                    key = (a, b, c)
                    summed[key] = summed.get(key, 0) + integer
        terms.append(entries)
    summed = {key: value for key, value in summed.items() if value}
    scaled_target = {key: int(scale * value) for key, value in target_tensor(n).items()}
    if summed != scaled_target:
        raise AssertionError("scaled term export does not equal the scaled target")
    data = {
        "name": name,
        "n": int(n),
        "r": int(len(factors)),
        "S": int(scale),
        "field": "QQ",
        "source": source,
        "coordinateConvention": convention,
        "T": [[int(a), int(b), int(c), int(value)] for (a, b, c), value in sorted(scaled_target.items())],
        "terms": terms,
        "factors": {
            "A": [[rational_string(x) for x in A] for A, _, _ in factors],
            "B": [[rational_string(x) for x in B] for _, B, _ in factors],
            "C": [[rational_string(x) for x in C] for _, _, C in factors],
        },
    }
    with open(path, "w") as output:
        json.dump(data, output, sort_keys=True, separators=(",", ":"))
        output.write("\n")
    print("Wrote %s (S=%s)" % (path, scale), file=sys.stderr)


# Authoritative rank-49 construction.  Loading this source also runs both exact
# assertions in that file, including the global row permutation verification.
load(os.path.join(SCRIPT_DIR, "q2_strassen2.sage"))
strassen2 = [
    (
        [QQ(U2[row, gate]) for row in range(16)],
        [QQ(V2[row, gate]) for row in range(16)],
        [QQ(W2[row, gate]) for row in range(16)],
    )
    for gate in range(49)
]


ENTRY_RE = re.compile(
    r"\$?\s*j\s*=\s*(\d+)\s*\$?\s*&\s*\$?\s*"
    r"\\begin\{matrix\}(.*?)\\end\{matrix\}\s*\$?\s*&\s*\$?\s*"
    r"\\begin\{matrix\}(.*?)\\end\{matrix\}\s*\$?\s*&\s*\$?\s*"
    r"\\begin\{matrix\}(.*?)\\end\{matrix\}\s*\$?\s*"
    r"\\\\\s*\\hline",
    re.DOTALL,
)


def parse_matrix(source, entry, factor):
    rows = source.split(r"\\")
    if len(rows) != 4:
        raise ValueError("j=%d %s has %d rows, want 4" % (entry, factor, len(rows)))
    matrix = []
    for row_index, row in enumerate(rows):
        cells = row.split("&")
        if len(cells) != 4:
            raise ValueError(
                "j=%d %s row %d has %d columns, want 4"
                % (entry, factor, row_index + 1, len(cells))
            )
        parsed = []
        for cell in cells:
            token = re.sub(r"\s+", "", cell)
            if not re.fullmatch(r"[+-]?\d+(?:/\d+)?", token):
                raise ValueError(
                    "j=%d %s has malformed coefficient %r" % (entry, factor, cell)
                )
            parsed.append(QQ(token))
        matrix.append(parsed)
    return matrix


def flatten(matrix, transpose=False):
    if transpose:
        matrix = [[matrix[row][column] for row in range(4)] for column in range(4)]
    return [matrix[row][column] for row in range(4) for column in range(4)]


def parse_appendix(path):
    with open(path) as source:
        latex = source.read()
    heading = r"\section{A Rational $\langle4,4,4,48\rangle$ Tensor}"
    if latex.count(heading) != 1:
        raise ValueError("expected exactly one rational <4,4,4,48> appendix heading")
    appendix = latex.split(heading, 1)[1].split(r"\end{longtable}", 1)[0]
    matches = list(ENTRY_RE.finditer(appendix))
    textual_indices = [int(x) for x in re.findall(r"\$?\s*j\s*=\s*(\d+)", appendix)]
    matched_indices = [int(match.group(1)) for match in matches]
    if textual_indices != matched_indices:
        raise ValueError(
            "one or more j entries did not match the strict table parser: text=%s parsed=%s"
            % (textual_indices, matched_indices)
        )
    if len(set(matched_indices)) != len(matched_indices):
        raise ValueError("duplicate appendix j entry")
    if matched_indices != list(range(1, 49)):
        raise ValueError("appendix entries are %s, want exactly 1,...,48" % matched_indices)
    return [
        tuple(
            parse_matrix(match.group(offset), entry, factor)
            for offset, factor in zip((2, 3, 4), ("O", "P", "Q"))
        )
        for entry, match in zip(matched_indices, matches)
    ]


appendix = parse_appendix(REFERENCE)
# Test all factor orders and transpose choices exactly.  Cyclic/symmetry-related
# alternatives also describe multiplication tensors, but the direct paper labels
# select (O, P, Q^T), represented by ((0,1,2),(False,False,True)).
valid_conventions = []
for permutation in itertools.permutations(range(3)):
    for transposes in itertools.product((False, True), repeat=3):
        candidate = [
            tuple(flatten(matrices[permutation[mode]], transposes[mode]) for mode in range(3))
            for matrices in appendix
        ]
        if reconstruct(candidate) == target_tensor(4):
            valid_conventions.append((permutation, transposes))
expected_convention = ((0, 1, 2), (False, False, True))
if expected_convention not in valid_conventions:
    raise ValueError(
        "appendix does not reconstruct under documented O, P, transpose(Q) convention; valid=%s"
        % (valid_conventions,)
    )
print("Appendix exact reconstruction conventions: %s" % (valid_conventions,), file=sys.stderr)
rational48 = [
    (flatten(O), flatten(P), flatten(Q, transpose=True))
    for O, P, Q in appendix
]

os.makedirs(OUTDIR, exist_ok=True)
common_convention = (
    "row-major A[i,j], B[j,k], C[i,k]; target "
    "A=(i,j), B=(j,k), C=(i,k)"
)
export_certificate(
    "Strassen squared",
    "Programs/BilinearComplexity/q2_strassen2.sage",
    strassen2,
    4,
    common_convention + "; tensor-product rows permuted from (block,inner) to global 4x4",
    os.path.join(OUTDIR, "strassen-squared.json"),
)
export_certificate(
    "Moran-Schwartz-Yuan rational rank-48",
    "Moran, Schwartz, and Yuan, Complex to Rational Fast Matrix Multiplication, appendix",
    rational48,
    4,
    common_convention + "; appendix mapping A=vec_row_major(O), B=vec_row_major(P), C=vec_row_major(transpose(Q))",
    os.path.join(OUTDIR, "rational-48.json"),
)
