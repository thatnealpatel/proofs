#!/usr/bin/env python3
"""Extract the three printed rank-23 <3,3,3> certificates into visualizer JSON.

Usage:
  python3 Programs/BilinearComplexity/export_visualize_arxiv_333.py \
    TEX_2607_28676 TEX_2601_05272 TEX_2508_03857_V1 OUTPUT_DIRECTORY

The first two papers print U^T, V^T, W^T as 9-by-23 ternary blocks.  The
third prints executable Python; this program parses that function with Python's
AST and symbolically expands its linear forms.  No certificate coefficient is
stored in this generator.
"""

import ast
import json
import re
import sys
from pathlib import Path

N = 3
RANK = 23
WIDTH = N * N


def transpose(rows):
    return [[rows[i][gate] for i in range(WIDTH)] for gate in range(RANK)]


def printed_blocks(tex, anchor):
    section = tex.split(anchor, 1)
    if len(section) != 2:
        raise ValueError(f"missing source anchor {anchor!r}")
    rows = []
    for line in section[1].splitlines():
        values = [int(x) for x in re.findall(r"(?<![A-Za-z0-9_])-?\d+", line)]
        if len(values) == RANK and all(value in (-1, 0, 1) for value in values):
            rows.append(values)
            if len(rows) == 3 * WIDTH:
                break
    if len(rows) != 3 * WIDTH:
        raise ValueError(f"found {len(rows)} certificate rows after {anchor!r}, want 27")
    return tuple(transpose(rows[start : start + WIDTH]) for start in range(0, 27, 9))


class Linear:
    def __init__(self, mode, values):
        self.mode = mode
        self.values = values

    def scale(self, scalar):
        return Linear(self.mode, [scalar * value for value in self.values])


class Products:
    def __init__(self, values):
        self.values = values

    def scale(self, scalar):
        return Products([scalar * value for value in self.values])


def add(left, right, sign=1):
    if type(left) is not type(right):
        raise ValueError("attempt to add unlike symbolic values")
    if isinstance(left, Linear):
        if left.mode != right.mode:
            raise ValueError("attempt to add A and B linear forms")
        return Linear(left.mode, [a + sign * b for a, b in zip(left.values, right.values)])
    return Products([a + sign * b for a, b in zip(left.values, right.values)])


def evaluate(node, env, gates):
    if isinstance(node, ast.Name):
        return env[node.id]
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return node.value
    if isinstance(node, ast.UnaryOp):
        value = evaluate(node.operand, env, gates)
        if isinstance(node.op, ast.USub):
            return -value if isinstance(value, int) else value.scale(-1)
        if isinstance(node.op, ast.UAdd):
            return value
    if isinstance(node, ast.BinOp):
        left, right = evaluate(node.left, env, gates), evaluate(node.right, env, gates)
        if isinstance(node.op, ast.Add):
            return add(left, right)
        if isinstance(node.op, ast.Sub):
            return add(left, right, -1)
        if isinstance(node.op, ast.Mult):
            if isinstance(left, int):
                return right.scale(left)
            if isinstance(right, int):
                return left.scale(right)
            if isinstance(left, Linear) and isinstance(right, Linear) and left.mode != right.mode:
                a, b = (left, right) if left.mode == "A" else (right, left)
                gates.append((a.values, b.values))
                values = [0] * RANK
                values[len(gates) - 1] = 1
                return Products(values)
    raise ValueError(f"unsupported certificate expression: {ast.dump(node)}")


def python_algorithm(tex):
    matches = re.findall(r"\\begin\{lstlisting\}[^\n]*\n(.*?)\\end\{lstlisting\}", tex, re.S)
    blocks = [block for block in matches if "def fast_3x3_rank23" in block]
    if len(blocks) != 1:
        raise ValueError(f"found {len(blocks)} fast_3x3_rank23 listings, want one")
    module = ast.parse(blocks[0])
    function = next(node for node in module.body if isinstance(node, ast.FunctionDef))
    env = {}
    for mode in ("A", "B"):
        for index in range(WIDTH):
            values = [0] * WIDTH
            values[index] = 1
            env[f"{mode}{index}"] = Linear(mode, values)
    gates = []
    outputs = {}
    for statement in function.body:
        if not isinstance(statement, ast.Assign) or len(statement.targets) != 1:
            continue
        target = statement.targets[0]
        if not isinstance(target, ast.Name):
            continue
        name = target.id
        if not re.fullmatch(r"[tu]\d+|v\d+|M\d+|C\d+", name):
            continue
        value = evaluate(statement.value, env, gates)
        env[name] = value
        if name.startswith("C"):
            outputs[int(name[1:])] = value
    if len(gates) != RANK or set(outputs) != set(range(WIDTH)):
        raise ValueError(f"expanded {len(gates)} products and {len(outputs)} outputs")
    c = [[outputs[coordinate].values[gate] for coordinate in range(WIDTH)] for gate in range(RANK)]
    return [a for a, _ in gates], [b for _, b in gates], c


def target():
    return [[i * N + j, j * N + k, i * N + k, 1]
            for i in range(N) for j in range(N) for k in range(N)]


def terms(a, b, c):
    result = []
    for gate in range(RANK):
        entries = []
        for ai, av in enumerate(a[gate]):
            for bi, bv in enumerate(b[gate]):
                for ci, cv in enumerate(c[gate]):
                    coefficient = av * bv * cv
                    if coefficient:
                        entries.append([ai, bi, ci, coefficient])
        result.append(entries)
    return result


def verify(a, b, c):
    if any(len(factor) != RANK for factor in (a, b, c)):
        raise ValueError("factor count is not 23")
    if any(len(row) != WIDTH for factor in (a, b, c) for row in factor):
        raise ValueError("factor width is not 9")
    if any(value not in (-1, 0, 1) for factor in (a, b, c) for row in factor for value in row):
        raise ValueError("certificate is not ternary")
    for ai in range(WIDTH):
        for bi in range(WIDTH):
            for ci in range(WIDTH):
                got = sum(a[g][ai] * b[g][bi] * c[g][ci] for g in range(RANK))
                i, j = divmod(ai, N)
                want = int(bi // N == j and ci == i * N + bi % N)
                if got != want:
                    raise ValueError(f"Brent coordinate {(ai, bi, ci)} is {got}, want {want}")


def write_asset(path, name, source, factors):
    a, b, c = factors
    verify(a, b, c)
    certificate = {
        "name": name,
        "n": N,
        "r": RANK,
        "S": 1,
        "field": "ZZ",
        "source": source,
        "coordinateConvention": "A, B, C are row-major; products and output recombination retain printed order",
        "T": target(),
        "terms": terms(a, b, c),
        "factors": {"A": [[str(x) for x in row] for row in a],
                    "B": [[str(x) for x in row] for row in b],
                    "C": [[str(x) for x in row] for row in c]},
    }
    path.write_text(json.dumps(certificate, separators=(",", ":")) + "\n")


def main():
    if len(sys.argv) != 5:
        raise SystemExit(__doc__)
    source_paths = [Path(value) for value in sys.argv[1:4]]
    out = Path(sys.argv[4])
    out.mkdir(parents=True, exist_ok=True)
    tex2607, tex2601, tex2508 = [path.read_text() for path in source_paths]
    jobs = [
        ("arxiv-2607.28676.json", "arXiv 2607.28676 rank-23",
         "arXiv:2607.28676, Complete ternary factor arrays", printed_blocks(tex2607, "Complete ternary factor arrays")),
        ("arxiv-2601.05272.json", "arXiv 2601.05272 rank-23",
         "arXiv:2601.05272, Appendix: The 59-algorithm in File Format", printed_blocks(tex2601, "The 59-algorithm in File Format")),
        ("arxiv-2508.03857v1.json", "arXiv 2508.03857v1 rank-23",
         "arXiv:2508.03857v1, Appendix Python Verification Script", python_algorithm(tex2508)),
    ]
    for filename, name, source, factors in jobs:
        write_asset(out / filename, name, source, factors)
        print(f"wrote {out / filename}")


if __name__ == "__main__":
    main()
