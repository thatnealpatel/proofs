# T5 — maximal-class rank-defect monotonicity

**Status.** Complete in `Proofs/BilinearComplexity/SharedFactorReduction.lean`.
The public umbrella `Proofs/BilinearComplexity.lean` imports the module. The
former Scratch implementation is now a compatibility/check harness that imports
the public API; public code does not import `Scratch`.

## Guarded natural-number matrix API

The definition itself has the signature-level hypotheses

```lean
{k rows cols ι : Type*} [Field k] [Fintype cols]
```

so its row type is arbitrary. The guarded rank-sum, growth, and monotonicity
theorems additionally assume `[Fintype rows]`. All APIs use finite sets
`Finset ι`. `matrix_rank_sum_growth` exposes `[DecidableEq ι]` because its
statement names `G \ I`; the defect-monotonicity API constructs decidability
internally and does not expose that instance. Zero and duplicate matrices are
permitted.

The public natural-number expression is

```lean
matrixRankDefectNat A s = s.card - Matrix.rank (∑ i ∈ s, A i)
```

This definition uses truncated `Nat` subtraction. Its numerical value has the
usual cardinality-minus-rank defect interpretation only when one has proved

```lean
Matrix.rank (∑ i ∈ s, A i) ≤ s.card.
```

For a family satisfying `∀ i, Matrix.rank (A i) ≤ 1`,
`matrix_rank_sum_le_card` supplies exactly that guard. The same hypothesis is
present in all public monotonicity corollaries.

For `I ⊆ G`, the core results are

```lean
matrix_rank_sum_growth A hA hIG :
  Matrix.rank (∑ i ∈ G, A i) ≤
    Matrix.rank (∑ i ∈ I, A i) + (G \ I).card

matrixRankDefectNat_mono A hA hIG :
  matrixRankDefectNat A I ≤ matrixRankDefectNat A G
```

The operational corollaries are
`matrixRankDefectNat_eq_zero_of_subset` and
`matrixRankDefectNat_pos_of_subset`. The completeness claim is specifically
about the positivity predicate `0 < matrixRankDefectNat A s`: within a fixed
finite rank-at-most-one class `G`, some subset has positive guarded defect if
and only if `G` itself does. The nontrivial direction is
`matrixRankDefectNat_pos_of_subset`; the reverse uses `G` as its own subset.
Thus positivity pruning needs no support cutoff or enumeration of proper
subsets. No broader completeness claim about tensor reductions is made.

`matrix_rank_vecMulVec_le_one` specializes the rank-at-most-one hypothesis to
outer products. The proofs are field-general and do not assume characteristic
two or nonzero summands.

## Matrix factorization and `RankLE` reconstruction

The factorization theorem has the weaker hypotheses

```lean
{k rows cols : Type*} [Field k] [Fintype cols]
```

with no `Fintype rows` assumption:

```lean
exists_eq_sum_vecMulVec_rank (A : Matrix rows cols k) :
  ∃ v : Fin (Matrix.rank A) → rows → k,
    ∃ w : Fin (Matrix.rank A) → cols → k,
      A = ∑ s, Matrix.vecMulVec (v s) (w s)
```

It reconstructs a matrix using a family indexed by its matrix rank, including
rank zero and empty-index boundary cases.

The tensor upper-bound declarations are:

- `rankLE_common_first_factor_matrix`;
- `rankLE_sum_shared_first_factor`;
- `rankLE_sum_shared_second_factor`;
- `rankLE_sum_shared_third_factor`.

The generic reconstruction results do **not** require the common factor to be
nonzero. They produce `RankLE` witnesses and hence upper bounds; they do not
assert that the displayed bound is the exact or minimal tensor rank. The
second- and third-factor forms permute tensor modes in the proof.

## Anchored literal first-factor fiber

Inside `BilinearComplexity.Scheme.Replacement`,
`LiteralFirstFactorClass S` is intentionally a first-mode structure. It stores:

- a fixed first factor `factor`;
- an anchor slot `anchor : Fin r`;
- `anchor_factor : (S.term anchor).1 = factor`;
- `factor_ne_zero : factor ≠ 0`.

Its full literal fiber is

```lean
F.slots = Finset.univ.filter fun s => (S.term s).1 = F.factor.
```

`anchor_mem_slots` proves that the anchor belongs to this fiber, and
`slots_nonempty` rules out phantom empty classes. `mem_slots` characterizes the
fiber exactly. “Full” means all slots with literal equality of the stored first
factor; it does not mean equality up to nonzero scalar or projective
proportionality.

`complementaryMatrix` sums the second/third outer products over this full
fiber. Its API includes:

- `complementaryMatrix_apply`;
- `complementaryMatrix_rank_le_card`;
- `matrixRankDefectNat_eq_card_sub_rank`.

The nonzero-factor requirement belongs to this literal operational structure;
it is not needed by the generic matrix factorization or generic common-factor
`RankLE` reconstruction above.

## Noncomputably chosen first-mode certificate

`exists_literalFirstFactorClass_certificate` factors the complementary matrix
and proves existence of an exact local replacement. The public
`LiteralFirstFactorClass.certificate` is a **noncomputably chosen witness** from
that existence theorem rather than an algorithmic normal form. Its bookkeeping
specification is

```lean
certificate.removed = slots
certificate.inserted.length = complementaryMatrix.rank
certificate.resultRank = r - slots.card + complementaryMatrix.rank.
```

`certificate_local_eq` and `certificate_sumTensor_eq` prove local replacement
and equality of represented tensor sums. `certificate_rankLE` gives the upper
bound at the certificate's `resultRank` parameter.

These statements must be kept distinct:

- `certificate.resultRank` is the number of slots in the output scheme;
- `RankLE S.sumTensor certificate.resultRank` is a tensor-rank upper bound;
- neither statement proves exact or minimal tensor rank;
- equality of `sumTensor` does not prove `Scheme.Valid` for the output.

The generic `Certificate.valid_output` theorem elsewhere requires both source
validity and a separate `InsertedValid` proof. T5 does not establish
`InsertedValid` for every chosen matrix factorization and therefore makes no
general output-validity claim.

Shortening is explicitly guarded:

- `certificate_resultRank_lt` assumes
  `complementaryMatrix.rank < slots.card` and uses `slots.card ≤ r`;
- `certificate_resultRank_lt_of_matrixRankDefectNat_pos` accepts positivity of
  the guarded natural expression;
- `rankLE_pred_of_complementaryMatrix_rank_lt` yields
  `RankLE S.sumTensor (r - 1)`.

The certificate structure and these shortening declarations are first-mode
only. T5 does not provide second- or third-mode `Scheme.Replacement.Certificate`
structures by symmetry.

## Asymmetric dependence compatibility API

The migrated dependence-based declarations are:

- `exists_shared_first_factor_reduction_certificate`;
- `rankLE_sum_shared_first_factor_of_not_linearIndependent`;
- `rankLE_sum_scalar_shared_first_factor_of_not_linearIndependent`;
- `rankLE_sum_shared_second_factor_of_not_linearIndependent`.

Their names describe the directions actually supplied. In particular, the
first-factor forms assume dependence of the second-factor family, and the
common-second-factor form assumes dependence of the first-factor family. This
is an intentionally asymmetric compatibility API, not a six-way permutation
family. These sufficient dependence criteria do not replace the complete
complementary-matrix-rank computation.

## Boundary and fidelity checks

The module checks:

- an empty selected matrix set;
- singleton and duplicate nonzero rank-one matrices, including a false reverse
  monotonicity inequality;
- two zero matrices;
- an end-to-end `Scheme ℚ 1 1 2 2` fixture whose terms share nonzero first and
  second factors and have the distinct third basis vectors `[1, 0]` and
  `[0, 1]`.

For the last fixture Lean proves `S.Valid S.sumTensor`, full two-slot fiber,
complementary matrix rank one, chosen certificate `resultRank = 1`, and
`RankLE S.sumTensor 1`. It does not claim that the chosen output scheme is
valid, nor that one is the exact tensor rank.

`#check @...` commands audit inferred signatures, including the anchored class
API. `#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound`. The module contains no `sorry`, `admit`, declared axioms, search
tables, campaign hashes, or census outputs.

## Scope and non-goals

T5 proves positivity pruning for the guarded `matrixRankDefectNat` expression
inside a full literal equal-first-factor fiber and constructs a corresponding
first-mode replacement witness. It does not formalize the c659 or c680 census,
classify every tensor-rank reduction, prove tensor-rank minimality, establish
general certificate-output validity, add arbitrary lower bounds, provide all
six dependence permutations, or begin T6.
