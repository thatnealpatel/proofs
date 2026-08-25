# Rank-49 deformation T3 — paired circuits and the characteristic-two G_m identity

**Status.** Proof task. Prove a general sufficient identity motivated by the
certified five-term deformation; do not promote the observed mechanism to a
universal classification.

**Goal.** Isolate an elementary tensor theorem saying when two overlapping
three-circuits produce an exact one-parameter family in characteristic two, and
make the concrete rank-49 certificate reducible to finite closure equalities.

## Certified motivating example

The base object is the ordered 49-term `4 x 4 x 4` matrix-multiplication
presentation over `F_2` with source SHA-256

`5fc92a6bf83fc29d9527ab100bad5d72d769178b616b31a36c3c0c0b8ad9d09d`.

Its certified minimum-support nongauge direction uses zero-based terms

`{1, 14, 29, 37, 42}`.

In the `V` factors the support contains the two three-circuits

`v_1 + v_37 + v_42 = 0`,

`v_14 + v_29 + v_42 = 0`.

These two relations and their minimality were directly verified from the hashed
source: the masks are respectively `(0aa0,1110,1bb0)` and
`(bbb0,a000,1bb0)`, with each triple distinct and nonzero. They are not fields
of `certificate.json`, and the current `check_certificate.py` does not replay
the circuit interpretation. It replays the deformation identities and `A=B=C`.
A future concrete circuit certificate must include the masks, relation
coefficients, minimality checks, and closure equalities explicitly.

They share term 42, so their union has five terms. The exact factor updates
reduce the local tensor difference to

`Delta = s A + t B + s*t C`,

and direct finite calculation gives `A = B = C`. Taking

`s = t/(1+t)`

is equivalently the relation `(1+s)(1+t)=1`; in characteristic two it gives
`s+t+s*t=0`, hence `Delta=0`. With `b=1+t`, the regular parameter space is
`b in G_m`, with `1+s=b^-1`.

The durable external evidence is in
`/home/exedev/x/rank47-fresh-eyes/r49-deformation-poc/`, especially
`REPORT.md`, `certificate.json`, and `check_certificate.py`.

## Distinctions the formalization must preserve

A factor-matroid circuit is a minimal linear dependence among one list of
factors. A derivative circuit is a minimal support dependence among blocks of
Jacobian columns. They are related in this example but are not definitions of
each other.

The proved target is a sufficient construction. The statement that every
integrable five-term direction at this point has this construction is a separate
bounded conjecture. A universal statement about all five-term tensor
deformations is unsupported and likely false.

**Non-universality fixture:** `/home/exedev/x/matmul-schemes/matmul-schemes/z2/4x4x4_m47_c659_iteration5551_Z2.txt` is a fourth audited rank-47 orbit; no paired-circuit conclusion for this separate presentation is implied by the rank-49 construction below.

## Statements to establish

### 1. Scalar torus identity

Over a commutative ring of characteristic two, prove

`(1+s)*(1+t)=1  ->  s+t+s*t=0`.

Conversely prove that `s+t+s*t=0` implies the product identity. When `1+t` is a
unit, prove that the unique solution is `s=t/(1+t)` in the appropriate unit or
localization language.

Package the change of coordinate `b=1+t`, `1+s=b^-1` as an equivalence with
`G_m` where convenient. Do not claim a second `F_2` point: `G_m(F_2)={1}`.

### 2. Abstract tensor cancellation

For an additive tensor module over a characteristic-two ring, prove

`A=B=C` and `(1+s)*(1+t)=1`

imply

`s • A + t • B + (s*t) • C = 0`.

Keep a more general version in which explicit equalities identify `B` and `C`
with `A`; this is the exact interface an external finite certificate can replay.

### 3. Paired-circuit sufficient theorem

Define a three-circuit over a field as a minimal three-element linear
dependence, carrying explicit nonzero relation coefficients in its witness. Over
a general characteristic-two field, a three-circuit need not have the normalized
all-ones relation seen over `F_2`. State the theorem with `[Field k]` and
`[CharP k 2]`, and either carry those coefficients through every update and
closure equation or require an explicit normalized plus-relation as a stronger
hypothesis. If unit term gauges normalize the coefficients, include those gauges
in the witness.

State hypotheses for two such circuits in the same factor position sharing
exactly one term.

Add explicit complementary-factor closure hypotheses sufficient to expand the
five changed rank-one terms as `s A + t B + s*t C` and prove `A=B=C`. Under
these hypotheses, conclude that the five-term local tensor is constant along
the torus relation.

The closure hypotheses should expose the actual finite equalities that need to
be checked; they must not hide the conclusion behind an opaque predicate such
as “is a valid deformation.” Prefer linear factor relations and rank-one tensor
equalities that can be replayed independently.

### 4. Equivariance and transport

Using T1, prove that term permutation, a sandwich transformation, and any of the
six outer orientations transport a paired-circuit witness to another valid
witness. Termwise gauge transport may be included when the coefficient ring has
nontrivial units.

This theorem is what later permits candidate generation and exact checking on
stabilizer-orbit representatives.

## Proof route

1. Prove the scalar identity without tensors.
2. Lift it through scalar multiplication in an additive tensor module.
3. Model the two circuit relations and expand the five-term local difference
   by trilinearity.
4. Isolate the complementary closure equalities as named lemmas.
5. Derive the abstract `A=B=C` interface and invoke the scalar cancellation.
6. Obtain symmetry transport from action linearity rather than repeating the
   expansion in six orientations.

If the exact complementary closure hypotheses are not yet apparent from the
certificate, first formalize the scalar and abstract tensor cancellation. Do
not guess a stronger circuit theorem merely to complete the card.

## Acceptance criteria

- The main sufficient theorem is coefficient-domain explicit and assumes
  characteristic two.
- Its five-term support and two overlapping three-circuits are visible in the
  hypotheses, with explicit relation coefficients or a stated `F_2`
  normalization.
- Every concrete condition is independently checkable.
- The proof yields an exact family, not only first- or second-order vanishing.
- The theorem does not assert integrability of unrelated tangent directions.
- The text surrounding any concrete specialization calls it a length-49
  presentation and not a proof of minimal tensor rank.

## Non-goals

Do not formalize the complete 49-term source table, the Jacobian dimensions, or
an exhaustive support census in this task. Do not claim that the `F_4` fiber is
inequivalent under the full sandwich/gauge/outer action; the current checker
proves exact tensor equality with nonzero factors and non-permutation of the
complete summand-tensor multiset only.
