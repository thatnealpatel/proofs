# T5 — maximal-class rank-defect monotonicity

**Status.** Lean proof task.

**Goal.** Prove the field-general matrix-rank inequality that makes a maximal
literal equal-factor class a complete pruning test for all of its subsets.
Connect the theorem to shared-factor tensor reduction without importing any
search procedure or binary-field assumption.

## Plain-language statement

Suppose a collection of rank-one tensor terms has the same nonzero factor in
one tensor leg. After removing that common factor, each term is a rank-one
matrix in the other two legs.

For a finite set of terms `S`, let `M_S` be the sum of those complementary
rank-one matrices and define

`defect(S) = |S| - rank(M_S)`.

If `I` is a subset of `G`, then

`defect(I) <= defect(G)`.

Thus, if the full equal-factor class `G` has defect zero, every subset of `G`
has defect zero. Conversely, any deficient subset forces the full class to be
deficient. A complete reduction census may therefore test each maximal literal
equal-factor class once; it does not need a support cutoff or an enumeration of
all subsets.

## Mathematical setup

Let `k` be a field, let `m` and `n` be finite index types, and let `X` be a
finite term-index type. For vectors

`v : X -> m -> k`,

`w : X -> n -> k`,

define the complementary rank-one matrix

`A_x(i,j) = v_x(i) * w_x(j)`

and, for a finite set `S` of term indices,

`M_S = sum x in S, A_x`.

The target theorem is valid more generally for any family of matrices `A_x`
with `Matrix.rank (A_x) <= 1`.

## Statements to establish

### 1. Rank growth under adjoining rank-one matrices

For finite sets `I subset G`, prove

`Matrix.rank (M_G) <= Matrix.rank (M_I) + |G \ I|`.

The proof should expose the two ingredients:

1. matrix rank is subadditive under addition;
2. each adjoined matrix has rank at most one.

Do not specialize to `F_2`. The theorem should work over every field.

### 2. Defect monotonicity

First prove `Matrix.rank (M_S) <= |S|`, so the natural-number subtraction in

`defect(S) = |S| - Matrix.rank (M_S)`

has its intended meaning. Then prove

`|I| - Matrix.rank (M_I) <= |G| - Matrix.rank (M_G)`

whenever `I subset G`.

Include empty-set, singleton, duplicate-vector, and zero-vector boundary cases.
The tensor census uses nonzero summands, but the linear-algebra theorem should
not need that restriction.

### 3. Full-class criterion

Package the two operational corollaries:

- `defect(G) = 0` implies `defect(I) = 0` for every `I subset G`;
- `0 < defect(I)` for some `I subset G` implies `0 < defect(G)`.

Define a literal equal-factor class independently of the theorem: it is the
full set of term slots whose selected factor is exactly one fixed nonzero
vector. Maximality is not an algebraic hypothesis in the inequality; it is what
ensures that every subset considered by the census lies inside one complete
class.

### 4. Tensor-reduction interpretation

For terms

`u tensor v_x tensor w_x`

sharing the same factor `u`, identify their sum with

`u tensor M_S`.

A factorization of `M_S` into `r = Matrix.rank (M_S)` rank-one matrices gives a
replacement using `r` tensor terms, so positive defect gives a shorter exact
presentation of this local sum. Keep this statement separate from the defect
monotonicity theorem: monotonicity is a pruning theorem, while the matrix
factorization supplies the actual replacement.

Relate the result to the existing one-step dependence theorems in
`Proofs/Scratch/GlobalRankSearch/SharedFactorReduction.lean`. Reuse those
results where they fit, but do not weaken the new statement to dependence of
only one complementary factor list. The census criterion uses the rank of the
complete complementary matrix sum.

State the analogous common-second-factor and common-third-factor conclusions
by permutation of tensor modes rather than reproving the rank inequality.

## Lean route

1. Define the rank-one complementary matrix and finite-set sum.
2. Prove rank at most one for an outer-product matrix, preferably by an explicit
   matrix-product factorization.
3. Prove or locate matrix-rank subadditivity over a field.
4. Induct over `G \ I` to bound rank growth.
5. Convert `G.card = I.card + (G \ I).card` and the rank bound into the defect
   inequality with explicit natural-number arithmetic.
6. Derive the full-class corollaries.
7. Add the tensor interpretation and connect it to the existing shared-factor
   reduction API.

If `Matrix.rank` creates unnecessary cardinal arithmetic, an equivalent
finite-dimensional linear-map formulation is acceptable, but the final public
theorem must state the ordinary natural-number matrix-rank result used by the
certificate programs.

## Acceptance criteria

- The main theorem assumes an arbitrary field, not characteristic two.
- It quantifies over every subset of a declared finite class.
- No support-size cutoff appears.
- Matrix rank, set cardinality, and natural subtraction are connected without
  an implicit nonnegativity assumption.
- Tests or examples discriminate the false reversed inequality.
- At least one example has strict inequality: adding a rank-one term increases
  cardinality without increasing matrix rank.
- The tensor corollary distinguishes the pruning implication from construction
  of the shorter replacement.
- The resulting Lean file reports its axioms and contains no campaign-specific
  hashes, root tables, or search outputs.

## Non-goals

Do not formalize the c659 or c680 census in this task. Do not claim that every
rank reduction arises from a literal shared-factor class. Do not infer tensor
rank minimality from a defect-zero census.
