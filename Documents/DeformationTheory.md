# Deformation Theory

This document SHOULD NOT be autonomously
updated: Instead, the USER should drive
changes to this document.

## Claim and corpus provenance

In direct communication, Kauers and Moosbauer told the USER that
`~/x/tensor/data/kauers-moosbauer` contains all `<4,4,4>` schemes they
found. The archive contains both AlphaTensor and Kauers--Moosbauer
constructions.

An independent standalone parser, sharing no code with the existing
classifier, rescanned all 99,101 archive files and computed the ranks of all
141 factor matrices in each 47-term decomposition.

For a decomposition `D`, let

$$
H(D) = (h_1,h_2,h_3,h_4),
$$

where `h_r` is the number of factor matrices of rank `r`. The scan and the
local-scheme audit found:

| Construction | `H(D)` |
|---|---|
| 70,920 archived files | `(50, 48, 42, 1)` |
| 28,181 archived files | `(49, 48, 43, 1)` |
| local c680 | `(48, 45, 48, 0)` |
| local c659 | `(51, 49, 41, 0)` |

Consequently:

- c680 is inequivalent to every scheme represented in the archive;
- c659 is inequivalent to every scheme represented in the archive;
- c680 and c659 are inequivalent to each other.

This conclusion does not require either archive histogram bucket to be a
single orbit. Each bucket may contain one equivalence class or many.

## Why the histogram is invariant

Let `K` be a field. Burichenko's isotropy theorem identifies the small
isotropy subgroup of the `<4,4,4>` matrix-multiplication tensor with

$$
\Gamma^0(\langle 4,4,4\rangle) \cong PGL_4(K)^3
$$

and its full decomposable isotropy group with

$$
\Gamma(\langle 4,4,4\rangle) \cong PGL_4(K)^3 \rtimes S_3.
$$

The `PGL_4(K)^3` part acts by sandwich transformations of the form

$$
(U,V,W) \longmapsto (PUQ^{-1},\;QVR^{-1},\;RWP^{-1}),
$$

and the six `S_3` elements act by the corresponding factor permutations and
transpositions. These tensor automorphisms are distinct from two harmless
presentation redundancies: permutation of the 47 summands and termwise scalar
gauges `(U,V,W) -> (lambda U, mu V, nu W)` with nonzero scalars satisfying
`lambda mu nu = 1`.

Every operation above preserves `H(D)`:

- multiplication by invertible matrices preserves matrix rank;
- transposition preserves matrix rank;
- factor and term permutations only reorder the 141 factors;
- multiplication by a nonzero gauge scalar preserves matrix rank.

Therefore different `H(D)` values obstruct equivalence under the full standard
isomorphism relation for matrix-multiplication decompositions. Burichenko's
theorem has no characteristic-two or field-size exception; over `F_2`,
`PGL_4(2) = GL_4(2)`.

Reference: V. P. Burichenko, *The Isotropy Group of the Matrix Multiplication
Tensor*, arXiv:2210.16565, Proposition 5, Proposition 8, and the main theorem.

## Scalar extension

For every field extension `L/F_2`, the rank of a matrix with entries in `F_2`
is unchanged after viewing it over `L`. Hence the four histograms above are
unchanged by scalar extension. An equivalence over `L` would still have to
preserve `H(D)`, so the same obstruction applies over `L`, including over the
algebraic closure of `F_2`.

## Exact conclusion

> As multisets of 47 nonzero rank-one summand tensors, c680 and c659 are
> inequivalent to every construction represented in the complete 99,101-file
> Kauers--Moosbauer archive and to each other under the full standard
> isomorphism relation for matrix-multiplication decompositions, even after
> scalar extension from `F_2`.

Qualifications:

1. The archive contains all `<4,4,4>` schemes Kauers and Moosbauer told the
   USER they found; this is not an exhaustive classification of all possible
   rank-47 schemes.

2. The two archive histogram buckets are not asserted to be individual
   equivalence classes.

3. The local schemes prove tensor rank at most 47, not minimality of rank 47.

4. Unrestricted transformations of the full 4096-dimensional ambient tensor
   space that do not preserve decomposable tensors are not decomposition
   isomorphisms.

## Evidence status

The aggregate counts were produced by an independent standalone parser and
were reproduced by a second independent rescan during review. That parser and
its output are not currently committed. The committed
`Programs/BilinearComplexity/rank47_local_audit.sage` validates the local
schemes and computes per-input factor-rank counts, but its compact archive
summary does not currently preserve the aggregate histogram above.
