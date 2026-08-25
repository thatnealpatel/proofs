# Rank-49 deformation T2 — restricted derivatives and exact rejection scope

**Status.** Proof task. The target is the soundness of derivative and support
filters, not the numerical rank of the rank-49 Jacobian.

**Goal.** Formalize the linear, quadratic, and cubic coefficients of a perturbed
rank-one decomposition; define restricted-support and gauge quotients; and prove
exactly what an inconsistent restricted system or nonzero obstruction class
rejects.

**Motivation.** For the certified rank-49 point over `F_2`, exact external
computation gives a `4096 x 2352` Jacobian of rank 2155, kernel dimension 197,
and connected gauge/isotropy image rank 143. Exhaustive support searches reject
nongauge first-order directions on at most four terms. Those numbers should
later enter Lean through replayable finite certificates. This card first proves
the domain-independent semantics that make such a replay meaningful.

## Existing Lean ground

- `Proofs/BilinearComplexity/Basic.lean` and `RankCalculus.lean` provide tensors,
  finite sums, reindexing, and linear actions.
- `Proofs/Scratch/FlipQuantum/Phase1Schemes.lean` provides ordered schemes and
  exact represented tensors.
- `Proofs/BilinearComplexity/LinearFlattening.lean` and related files provide
  examples of turning finite matrix-rank certificates into tensor statements.
- Mathlib supplies kernels, ranges, quotients, scalar restriction/extension,
  matrices, and finite-dimensional rank-nullity.

This task should share the scheme semantics produced by T1 rather than define a
second incompatible scheme type.

## Statements to establish

### 1. Exact perturbation expansion

For one rank-one term over a commutative ring, expand

`(U + t u) tensor (V + t v) tensor (W + t w)`

through degree three. For a finite ordered scheme, sum the expansions and define:

- the linear map `J(d)`;
- the quadratic coefficient
  `Q(d) = sum_l (u_l tensor v_l tensor W_l
               + u_l tensor V_l tensor w_l
               + U_l tensor v_l tensor w_l)`;
- the cubic coefficient
  `C(d) = sum_l u_l tensor v_l tensor w_l`.

Also state the bilinear mixed quadratic expression needed when the second
coefficient is independent of the first. Prove, with signs valid over a general
commutative ring, the first two lifting equations. In characteristic two these
specialize to

`J d1 = 0` and `J d2 + Q(d1) = 0`.

Do not infer an all-order family from the vanishing of these two coefficients.

### 2. Restricted variation modules

For a finite set of term indices and, optionally, a specified set of factor
coordinates, define the submodule of variations allowed on that support. Define
the restricted Jacobian by composing its inclusion `iota_S` with `J`. Keep
`ker (J o iota_S)` in its restricted domain and use `iota_S` whenever comparing
it with ambient gauge or symmetry subspaces.

Prove the exact rejection theorem:

> If a residual is not in the range of the restricted Jacobian, no first-order
> correction of that residual exists using those allowed variables.

The theorem is relative to the specified support, residual, coefficient ring,
and allowed coordinates. It says nothing about larger supports, different
residuals, or isolated finite solutions.

### 3. Gauge directions and normal classes

Define the two local term-scaling derivative directions for every nonzero
rank-one term. Define the infinitesimal sandwich directions and their span.
Prove directly that these directions lie in `ker J`.

Let `V` be the full variation module and set

`G := range(dH) <= V`.

Prove `G <= ker J`. Define the ambient normal tangent quotient with a
well-typed denominator as

`ker J / G.comap((ker J).subtype)`.

Do not obtain its dimension by adding raw generator counts: gauge and sandwich
generators can overlap.

For a restricted inclusion `iota_S : V_S -> V`, set

`K_S := ker (J o iota_S) <= V_S`

and define the restricted gauge submodule of the kernel subtype by

`G_S := (G.comap iota_S).comap K_S.subtype <= K_S`.

The inclusion `G.comap iota_S <= K_S` follows from `G <= ker J`. A restricted
kernel vector is nongauge exactly when its class in `K_S / G_S` is nonzero.
Equivalently, compare its image in the ambient normal tangent quotient. For
arbitrary coordinate masks, this gauge submodule need not have dimension two
per selected term, and deleting two ambient columns is not a quotient unless a
proved basis change supplies a direct-complement choice.

State the `46*|S|` criterion only for the audited binary situation in which each
selected term contributes its full 48-coordinate block and its local kernel is
proved to be exactly the two-dimensional scaling subspace. Under those
hypotheses, rank `46*|S|` excludes a nongauge direction on that term support.

### 4. First nongauge coefficient of a formal arc

Give a precise formal-power-series or truncated-polynomial statement:

> For an arc of valid decompositions through a base point, its first nonzero
> coefficient satisfies the linearized equations. After a proved gauge
> normalization, its first nongauge coefficient determines a class in the
> normal tangent quotient.

A support bound on that first coefficient then converts an exhaustive
restricted-kernel computation into a rejection theorem for arcs with that
normalized leading support. It still does not reject distant finite points.

### 5. Second-order obstruction class

For `d1 in ker J`, define the class of `Q(d1)` in `coker J`. Prove:

- a nonzero class forbids a second-order lift of that prescribed first-order
  direction, even if `d2` is allowed all scheme coordinates;
- a same-support cokernel test only forbids a same-support `d2`;
- vanishing is necessary, not sufficient, for an all-order lift.

If first-order solutions are `d1 = d0 + N z`, prove that rejecting an entire
support requires checking the quadratic obstruction on the whole affine family,
not merely on `d0` or a basis. In characteristic two, do not replace the
quadratic map by its polarization: diagonal information is lost.

### 6. Certificate and scalar-extension bridge

Specify a small elimination witness containing enough data to replay rank,
pivots, kernel membership, and inconsistency. Prove the checker sound: an
accepted witness implies the corresponding abstract linear-map statement.

Prove the needed field-extension lemma: a matrix with entries in `F_2` has the
same rank after extending scalars to a field containing `F_2`. This lets a
certified support-four rank exclusion apply to first-order directions over every
field extension of `F_2`.

## Proof route

1. Prove the one-term trilinear expansion, then sum over terms.
2. Define support as a linear inclusion rather than by zero-filled ad hoc
   arrays; derive the computational column-selection view afterward.
3. Prove gauge and sandwich kernel membership from T1 action preservation,
   preferably by differentiation rather than a second coordinate expansion.
   For a coordinate-restricted problem, compute the preimage or intersection of
   the ambient gauge image rather than subtracting a fixed number of dimensions.
4. Use quotient universal properties for normal classes and cokernel
   obstructions.
5. Keep the formal-arc result initially at a finite truncation sufficient to
   identify the first nonzero coefficient; general power-series machinery can
   be layered on later.
6. Make the executable checker a refinement of ordinary Gaussian elimination,
   with explicit replay data rather than trusting a reported dimension.

## Acceptance criteria

- The linear, quadratic, and cubic formulas are tested against direct expansion
  on small finite examples.
- Every rejection theorem states its support and variable scope.
- Full-cokernel and restricted-cokernel obstruction claims are separate.
- The affine freedom in first-order solutions is explicit.
- Scalar-extension rank preservation is a theorem, not an empirical claim.
- The later external facts `rank J = 2155` and minimum nongauge support five can
  be imported as data only after a checker witness is available.

## Explicit nonclaims

This task does not prove a 54-dimensional component, integrability of a normal
tangent, absence of finite replacements, or absence of another binary point.
Tangent rigidity on a support is not finite or global rigidity.

**Rank-47 local/global fixture:** `/home/exedev/x/tensor/data/z2/4x4x4_m47_c659_iteration5551_Z2.txt` has Jacobian nullity and exact gauge-plus-sandwich tangent rank 139 but is globally inequivalent to the three older audited classes.
