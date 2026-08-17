#!/usr/bin/env python3
"""Export the exact nealpatel rank-24 presentation for Tensor Gate Lens."""

import argparse
import json
from fractions import Fraction
from pathlib import Path


def q(value):
    return Fraction(str(value))


def text(value):
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def target_entries(n):
    return [[n * i + j, n * j + k, n * i + k, 1]
            for i in range(n) for j in range(n) for k in range(n)]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("candidate", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    source = json.loads(args.candidate.read_text())
    candidate = source["candidate"]
    if len(candidate) != 24:
        raise ValueError(f"candidate has {len(candidate)} terms, want 24")

    factors = {mode: [] for mode in "ABC"}
    terms = []
    total = {}
    for gate, raw in enumerate(candidate):
        coefficient = q(raw["coefficient"])
        parsed = {mode: [q(x) for x in raw[mode]] for mode in "ABC"}
        if any(len(parsed[mode]) != 9 for mode in "ABC"):
            raise ValueError(f"gate {gate + 1} has a factor of incorrect width")
        # Absorb the explicit term coefficient into C, preserving a plain
        # three-factor certificate for the visualizer.
        parsed["C"] = [coefficient * x for x in parsed["C"]]
        for mode in "ABC":
            factors[mode].append([text(x) for x in parsed[mode]])

        expanded = []
        for ai, av in enumerate(parsed["A"]):
            for bi, bv in enumerate(parsed["B"]):
                for ci, cv in enumerate(parsed["C"]):
                    value = av * bv * cv
                    if not value:
                        continue
                    if value.denominator != 1:
                        raise ValueError(f"gate {gate + 1} has nonintegral expanded coefficient {value}")
                    integer = int(value)
                    expanded.append([ai, bi, ci, integer])
                    key = (ai, bi, ci)
                    total[key] = total.get(key, 0) + value
        terms.append(expanded)

    expected = {(3 * i + j, 3 * j + k, 3 * i + k): Fraction(1)
                for i in range(3) for j in range(3) for k in range(3)}
    for ai in range(9):
        for bi in range(9):
            for ci in range(9):
                key = (ai, bi, ci)
                if total.get(key, Fraction(0)) != expected.get(key, Fraction(0)):
                    raise ValueError(f"Brent coordinate {key} is {total.get(key, 0)}, want {expected.get(key, 0)}")

    output = {
        "name": "nealpatel rank-24",
        "n": 3,
        "r": 24,
        "S": 1,
        "field": "QQ",
        "source": "Scratch/laderman_branch_K_length24_candidate.json (one Laderman split plus eight exact flips)",
        "coordinateConvention": "row-major A, B, and C factors; explicit term coefficient absorbed into C",
        "T": target_entries(3),
        "terms": terms,
        "factors": factors,
    }
    args.output.write_text(json.dumps(output, separators=(",", ":")) + "\n")


if __name__ == "__main__":
    main()
