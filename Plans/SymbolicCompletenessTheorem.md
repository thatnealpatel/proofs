# Symbolic Completeness Theorem

## Purpose

Scaffold a proof campaign for a complete symbolic language of exact
matrix-multiplication decompositions. This is a planning document, not a claim
that the proposed formal theorem has landed.

## Why this path

In the rank-at-most-8 `<2,2,2>` flip graph over `F_2`, a rank-8 scheme is an
isolated vertex, although Kauers--Moosbauer prove that the unbounded graph is
weakly connected once reductions may be reversed as splits. Thus fixed-altitude
components can be artifacts of truncation.

For `<2,2,2>`, rank 7 is already optimal. For `<4,4,4>`, rank 47 is only the
best known rank over `F_2`; a path

$$
47 \nearrow 48 \nearrow \cdots \searrow 46
$$

could improve the bound. The c680 and c659 results also show that local search
has reached standard-isomorphism classes absent from the reported corpus.
Orbit classification alone therefore does not describe the useful search
space.

## Proposed objects

Fix `n >= 1` and let

$$
V_n = \operatorname{Mat}_n(\mathbb F_2)^{\otimes 3},
\qquad M_n \in V_n
$$

be the square matrix-multiplication tensor. Let `P_n` be the finite set of
nonzero pure tensors. Over `F_2`, reduced decompositions may be represented by
subsets of `P_n`; define

$$
X_n = \left\{D \subseteq P_n : \sum_{t\in D} t = M_n\right\},
\qquad X_{n,r}=\{D\in X_n:|D|=r\}.
$$

Let atomic relations record individual valid symmetries, flips, reductions,
and splits. Splits are converse reductions. Their typed form is

$$
F_r:X_{n,r}\rightsquigarrow X_{n,r},\quad
R_r:X_{n,r}\rightsquigarrow X_{n,r-1},\quad
S_r=R_{r+1}^{\mathrm{op}}.
$$

The intended semantic object is the graded action groupoid of schemes and
standard isomorphisms, equipped with these noninvertible correspondences. Its
one-object collapse is a relation monoid on `X_n`.

## Candidate theorem

Let `E_n` contain the singleton relations for every concrete split, reduction,
flip, and symmetry move, together with singleton identity tests. Let `Q_n` be
the closure of `E_n` under relational composition and finite union. Then

$$
Q_n = \operatorname{Rel}(X_n).
$$

Equivalently:

1. the unbounded split--reduction move graph on exact decompositions is
   connected;
2. every singleton relation `{(D,E)}` is a composite of atomic moves; and
3. because `X_n` is finite, every relation on schemes is a finite union of
   singleton relations.

With arbitrary unions, `Rel(X_n)` is a unital involutive quantale and a
complete atomic relation algebra. The finite-union formulation is sufficient
over `F_2`.

## Proof sketch

The matrix-multiplication content is weak connectivity.

1. Reduce any scheme `D` to an irreducible scheme.
2. Split one factor of every term into coordinate factors.
3. Reduce until the complementary factor pairs satisfy the needed
   independence condition.
4. Split a second factor into coordinates.
5. Combine matching coordinate factors by reductions to obtain the schoolbook
   decomposition.
6. Connect arbitrary `D` and `E` through schoolbook, reversing the second
   normalization path.

This is the construction behind Kauers--Moosbauer's weak-connectivity theorem.
The abstract algebraic step is then short: compose singleton edge relations
along a path to obtain `{(D,E)}`, and take finite unions.

A coarse bound suggested by the coordinate-splitting proof is that a scheme of
length `r` normalizes below altitude `r n^4`. This bound must be checked against
the final formal definitions; sharpness is not expected.

## Computational implication

The result would justify a complete symbolic search language

$$
P ::= 1 \mid \mathrm{sym} \mid \mathrm{flip} \mid \mathrm{split}
\mid \mathrm{reduce} \mid [\varphi] \mid P;P \mid P+P \mid P^*.
$$

Programs denote relations rather than enumerated paths. Uniform move schemas,
symmetry saturation, tests, composition, and iteration can represent large
families of concrete transitions. Successful symbolic programs can still emit
exact step-by-step certificates.

The full relation algebra must not be materialized. The intended gain is to
search over compact, factored relation expressions and orbit-level schemas.
Weighted semantics should track maximum altitude, splits, flips, and path
length; minimum-altitude search then becomes a min--max relational problem.

Completeness licenses this change of representation: an unbounded endpoint is
not lost merely because search is compiled through the move language. Actual
efficiency will depend on compact schema representations, quotienting, and
normal-form results for useful paths.

## Stronger targets

The proof campaign should separate the foundational theorem from results that
would reduce search complexity:

- equivariance and descent of moves to standard-isomorphism orbits;
- a filtered algebra for `X_{n,<=R}` and connection altitude;
- a weighted/Kleene-algebra semantics for path optimization;
- canonical or bounded split normal forms;
- bounds on ascent--descent alternations;
- commutation laws for symmetries and local moves;
- compact symbolic preimage computation for reducible gateways;
- certificate extraction and independent exact replay.

A normal-form theorem such as

$$
\mathrm{split}^{\le k};\mathrm{flip}^*;\mathrm{reduce}^+
$$

for bounded-altitude descent would be a major algorithmic strengthening, but
is not part of the foundational completeness statement.

## Decisions before orchestration

1. Choose the canonical scheme representation: ordered lists, finite sets, or
   parity-normalized multisets.
2. Pin the exact move definitions and their agreement with
   Kauers--Moosbauer.
3. Decide whether the first formal theorem is unquotiented, orbit-quotiented,
   or stated for an abstract equivariant move system and instantiated later.
4. Distinguish atomic expressive completeness from completeness of a finite
   family of uniform executable schemas; the latter is the computationally
   meaningful strengthening.
5. Audit the weak-connectivity proof over `F_2`, including distinctness during
   splitting and the claimed `r n^4` altitude bound.
6. Fix the theorem boundary between pure relation algebra, exact tensor
   semantics, and the executable symbolic-search layer.

## Primary source

Manuel Kauers and Jakob Moosbauer, *Flip Graphs for Matrix Multiplication*,
arXiv:2212.01175: definition of the flip graph, the weak-connectivity theorem
and its coordinate-splitting proof, and the `<2,2,2>` rank-at-most-8 experiment
over `F_2`.
