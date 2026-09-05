# Compact binary enumeration: candidate-data provenance

This note accompanies `NormalizedBinaryCompactEnumerationCore.lean`,
`NormalizedBinaryCompactEnumerationChecksSmall.lean`, and
`NormalizedBinaryCompactEnumerationChecks222.lean`. Their literals are local
candidate data, not an external theorem or a semantic orbit classification.
The original literal-writing invocation was not retained; the record below
provides a reproducible reconstruction and a checked candidate-data comparison,
not a claim about that missing invocation.

## Tensor-mask reconstruction

For a canonical profile $(a,b,c)$, enumerate the positive masks
$1\le u<2^a$, $1\le v<2^b$, and $1\le w<2^c$ in lexicographic order, with $w$
varying fastest. The zero-based term index is

$$
(u-1)(2^b-1)(2^c-1)+(v-1)(2^c-1)+(w-1).
$$

Coordinate bit $i$ of $u$ is the $i$-th coordinate of the first binary vector;
the other factors use the same little-endian convention. The tensor-mask
entry is

$$
\sum_{i=0}^{a-1}\sum_{j=0}^{b-1}\sum_{k=0}^{c-1}
\operatorname{bit}_i(u)\operatorname{bit}_j(v)\operatorname{bit}_k(w)
\,2^{(ib+j)c+k}.
$$

Reconstruction by this formula matched every in-range literal entry of
`packed221`, `packed411`, `packed321`, and `packed222`: respectively
9, 15, 21, and 27 entries. The total functions' out-of-range fallback values
are not assigned a normalized-carrier meaning. The separate foundational
bridge also proves each in-range tensor-table entry agrees with the semantic
tensor evaluation of its canonical decoded term.

## Five-code candidate reconstruction

The candidate action artifact is `coverage_actions.json`, SHA-256
`bdb8a983a8cad61c375811e21a5cdb831dac77ceb70e4b9eb832d26df727f0bf`.
Its standalone external generator is `coverage_generate.go`, SHA-256
`f045bc75d5943ce33b47a1fd95ed2dce9a148b733144dcfc3bea7f009f418208`.
Both are retained in the campaign artifact directory
`~/x/binary-5-circuit/`; neither is a runtime or proof dependency of Lean.

For each profile, project every action to its
`target_support_term_indices` field, remove duplicates, and sort the resulting
five-tuples lexicographically. This projection was compared with the actual
Lean `exactCodes221`, `exactCodes411`, `exactCodes321`, and `exactCodes222`
literals and matched them exactly, in order:

| Profile | Distinct candidate five-codes |
|---|---:|
| 221 | 9 |
| 411 | 168 |
| 321 | 210 |
| 222 | 162 |

The bounded comparison and tensor-mask reconstruction are retained as
`~/x/binary-5-circuit/verify_compact_provenance.sage`, run with
`timeout 60 sage ~/x/binary-5-circuit/verify_compact_provenance.sage`.
This computation documents the candidate data; it is not a formal Lean proof.
The external action artifact's ordered pair/triple endpoints are not exchanged
by this projection or by the Lean action checker.

## What Lean checks, and what remains open

The frozen `exactTableCheckSmall` and `exactTableCheck222` theorems use ordinary
kernel reduction. They prove, relative to the compact Boolean `accepts5`:

- all listed codes are strictly increasing, bounded, accepted, and distinct;
- every accepted strictly increasing five-code is present.

These theorems depend only on `propext`, not on file hashes, the external
candidate generator, Sage, or native evaluation. The separate semantic
relation enumerator has its own proved membership characterization.

At this checkpoint, the full acceptance-to-semantic-support equivalence,
decoded-table equality with that semantic enumerator, orbit-label uniqueness,
and the concrete total compiler are still unassembled. Neither the provenance
comparison nor the displayed counts discharge those obligations.

AI disclosure: prepared with AI assistance; see the repository `README`.
