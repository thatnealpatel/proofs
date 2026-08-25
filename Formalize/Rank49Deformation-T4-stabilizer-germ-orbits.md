# Rank-49 deformation T4 — stabilizer, support-five census, generic germ, and orbit relation

**Status.** Exact computational research card with proof-producing outputs. It
is downstream of the three Lean foundation cards but is not itself initially a
Lean implementation task.

**Goal.** Complete the finite and generic calculations needed to decide whether
the certified five-term `G_m` family captures the minimum-support integrable
geometry of the specified rank-49 point, and determine how many decomposition
orbits the family actually represents.

## Fixed source and established boundary

The source is

`/home/exedev/x/matmul-schemes/matmul-schemes/z2/4x4x4_m49_c680_iteration65_Z2.txt`

with SHA-256

`5fc92a6bf83fc29d9527ab100bad5d72d769178b616b31a36c3c0c0b8ad9d09d`.

The exact audited artifacts are in
`/home/exedev/x/rank47-fresh-eyes/r49-deformation-poc/`; their
`SHA256SUMS` file currently verifies.

Established facts over `F_2`:

- all 4096 Brent equations hold;
- `J` has shape `4096 x 2352`, rank 2155, and kernel dimension 197;
- the explicit gauge-plus-sandwich differential has rank 143;
- the normal tangent quotient has dimension 54;
- every support of at most four terms has only local scaling directions;
- one support-five nongauge direction on zero-based terms
  `{1,14,29,37,42}` integrates to an exact `G_m` family;
- no second regular `F_2` fiber is supplied by that affine family;
- an exact `F_4` fiber is a 49-slot tensor presentation with nonzero factors
  and is not a literal permutation of the base summand-tensor multiset.

The current hashed checker does not test pairwise distinctness of all 49 new
summand tensors, so this fact is not yet imported as the stronger existing
`Scheme.Valid` predicate. These facts do not establish a 54-dimensional
component, full orbit inequivalence of the `F_4` fiber, a finite binary
replacement, a rank reduction, or minimal tensor rank 49.

## A. Exact decomposition stabilizer

Compute the decomposition stabilizer with its kernel and field of definition
made explicit. First define the algebraic witness stabilizer group scheme
`Stab_wit,x` and its normal split-torus kernel `C_x`, then distinguish:

- the point group `Stab_wit,x(K)` of sandwich matrices, term gauges,
  permutations, and outer orientations over each field extension `K/F_2`;
- the quotient group scheme `Stab_wit,x / C_x`;
- the effective point action `K_eff,x(K)`, defined as the image of
  `Stab_wit,x(K)` on the decomposition data;
- `F_2`-rational points versus geometric points over an algebraic closure.

Do not identify the `K`-points of the quotient group scheme with the naive
quotient of point groups unless the required surjectivity or descent statement
is proved. Only a specified finite point image, such as `K_eff,x(F_2)`, has a
reported finite order and a literal finite support-orbit enumeration. Keep every
one of these objects distinct from the ambient isotropy group of the
matrix-multiplication tensor.

For each of the six outer orientations `sigma`, explicitly define the oriented
factors

`(U_l^sigma, V_l^sigma, W_l^sigma) := sigma . (U_l,V_l,W_l)`,

including the cyclic and transpose/reversal leg reindexings. For every
compatible term correspondence, solve exactly for invertible `4 x 4` matrices
`P,Q,R` and term scalars satisfying

`P U_l^sigma Q^-1 = lambda_l U_{pi(l)}`,

`Q V_l^sigma R^-1 = mu_l V_{pi(l)}`,

`R W_l^sigma P^-1 = nu_l W_{pi(l)}`,

`lambda_l mu_l nu_l = 1`.

The normal subgroup scheme `C_x` is isomorphic to a split three-torus and
contains witnesses `P=pI`, `Q=qI`, `R=rI` with compensating term gauges. The
outer orientation group acts on it by permuting `p,q,r`; only the diagonal
subtorus is central under all six orientations. The group scheme `C_x` is
geometrically positive-dimensional, while its point group over every finite
field, including `F_4`, is finite. Over `F_2` the nonzero gauge values are
trivial. Retain gauge fields in the witness format. A positive result must
contain the full matrices, inverses, orientation, term permutation, and mapped
factor equations. The witness replayer must first apply `sigma` with its
certified leg reindexings, then check the sandwich/gauge equations. An
exhaustive negative branch must distinguish “proved no solution” from timeout
or branch limit.

Use exact rejection filters before solving: sorted per-term rank triples, the
three projective factor matroids and circuit hypergraphs, colored pair-rank or
pencil graphs, complementary Khatri-Rao ranks, cyclic-product similarity
invariants, and term-incidence data. A mismatch is a rejection certificate;
matching invariants are never an equivalence certificate.

**Orbit-filter fixture:** `/home/exedev/x/matmul-schemes/matmul-schemes/z2/4x4x4_m47_c659_iteration5551_Z2.txt` is rejected from each older rank-47 class by factor-rank and cyclic-product mismatches despite matching their full-span, Khatri--Rao, and Jacobian-dimension data.

Deliver:

- defining equations and verified point witnesses for each explicitly named
  stabilizer object;
- the normal split-torus subgroup scheme, quotient morphism, outer-coordinate
  action, and effective point-action image;
- exact order and orbit data only for a certified finite point image;
- an independent witness replayer;
- the induced actions on terms, supports, `ker J`, the trivial tangent image,
  the normal quotient, and the Jacobian cokernel.

Only the effective stabilizer point action at `x` acts on tangent and
obstruction spaces at `x`; the full ambient isotropy moves the base point. In
characteristic two, do not assume a finite-point module is semisimple when the
acting finite image has even order.

## B. Exhaustive support-five classification

There are

`binom(49,5) = 1,906,884`

five-term supports. Run and report two distinct classifications:

- the rational census over `F_2`, with projective directions over `F_2` and
  supports reduced by the induced term action of `K_eff,x(F_2)`;
- the geometric census over `Fbar_2`, with projective directions over
  `Fbar_2`, supports reduced by the explicitly computed geometric effective
  point action, and formal integrability declared over `Fbar_2[[tau]]`.

Finite-extension rational points, such as directions first visible over `F_4`,
are reported separately and are not by themselves a complete geometric census.
Scalar extension preserves restricted matrix ranks but can introduce new
projective directions and stabilizer witnesses.

In either census, a pure outer orientation usually sends `x` to another base
point and cannot independently identify two restricted systems at `x`. It
contributes to fixed-point reduction only when an exact
sandwich/gauge/permutation witness returns the oriented point to `x`, in which
case the composite lies in the effective stabilizer image. An alternative
groupoid census over six oriented base points must state and certify every
return map explicitly.

For every support-orbit representative `S` in each declared census:

1. construct the restricted derivative `J_S = J o iota_S` exactly;
2. compute the image of `iota_S(ker J_S)` in the ambient normal quotient,
   equivalently
   `(iota_S(ker J_S) + image(dH))/image(dH)`, not only raw nullity;
3. enumerate factor-matroid three-circuits and derivative block circuits;
4. identify paired circuits sharing one term and test the complementary closure
   hypotheses from T3;
5. evaluate the full quadratic obstruction class in `coker J` for every normal
   first-order direction over that census's declared coefficient field;
6. when the normal space has dimension greater than one, solve the complete
   projective quadratic obstruction locus over the same declared field rather
   than testing a basis; report points over finite extensions separately;
7. continue every surviving leading direction over the corresponding formal
   power-series ring in two explicitly separate modes: later Hasse coefficients
   restricted to the same `V_S`, and later coefficients allowed the full
   variation space `V`; record statuses such as `no_same_support_lift` and
   `no_full_coordinate_lift` separately;
8. replay every family in all 4096 Brent coordinates.

The bounded geometric conjecture under test is:

> Every minimum-support normal direction over `Fbar_2` that integrates over
> `Fbar_2[[tau]]` at this specified point is, up to the geometric effective
> fixed-point action, induced by two factor-matroid three-circuits sharing one
> term and satisfying the T3 closure identity.

State and test the analogous `F_2[[tau]]` conjecture separately for the rational
census. One integrable direction in the relevant declared category without that
structure refutes that version of the conjecture. Failure to find the motif is
not a rejection until the corresponding exhaustive classification and its
certificate are complete.

Produce a manifest listing every support orbit, orbit size, restricted rank,
normal dimension, circuit signature, obstruction status, solver status, and
artifact hash. Preserve `unknown` for unfinished nonlinear branches.

## C. Generic Jacobian along the certified family

Let `b=1+t` and `1+s=b^-1`. Construct the exact family over `F_2(b)` and compute
the Jacobian rank at its generic point, together with the rank of the connected
symmetry differential there.

The decisive tangent calculations are interpreted as follows:

- generic kernel dimension 144 and orbit tangent rank 143 establish only a
  one-dimensional quotient tangent. To prove a generically 144-dimensional
  orbit-swept locus, additionally verify that `d phi` is outside the orbit
  tangent, that the orbit-sweep map has generic differential rank 144, and the
  local-dimension or smoothness hypothesis needed to turn that rank into a
  component statement;
- generic kernel dimension greater than 144 establishes additional generic
  tangent directions or nonsmooth/nonreduced structure. It does not by itself
  refute a one-modulus reduced component; obstruction, lifting, or reduced
  local-dimension evidence must decide that question;
- rank changes at special parameters should be computed as an exact jump locus
  and compared with stabilizer, factor-rank, and circuit changes.

At the binary base point, a certified decomposition

`ker J = image(dH) direct_sum N`

makes `N` only a 54-dimensional **linear tangent complement**, not a normal
slice. Compute all mixed terms on the selected representatives and state the
dependence on `N`. To make the quadratic obstruction gauge-independent, prove
including mixed terms that

`Q(d+h) - Q(d) in image(J)` for every `h in image(dH)`,

or provide the appropriate action-corrected equivalent. Otherwise restrict
every obstruction conclusion to the chosen representatives. Reserve “normal
slice” for an actual local or formal slice with a proved gauge-normalization
statement. The audited quotient dimension alone supplies neither a complement
nor such a slice. The 4096-coordinate cokernel is an obstruction container, not
automatically a minimal obstruction space; do not claim a miniversal
obstruction theory without handling equation syzygies or an appropriate
cotangent-complex argument.

Output exact row-reduction or determinant-minor certificates over `F_2(b)` that
can be independently replayed. A sampled finite-field rank is only a screen.

## D. Equivalence relation on the parameter

For every field extension `K/F_2`, define the rational correspondence

`R(K) = {(b,b') in K^x x K^x : an equivalence witness exists over K}`.

Define the geometric correspondence separately after base change to an
algebraic closure. Equivalence over `F_q`, over its algebraic closure, over a
rational-function field, and only after an algebraic extension are different
relations and require different witness rationality claims.

For the family map `phi : G_m -> X_49`, determine these correspondences under
sandwiching, term permutation, gauges, and all six outer orientations. Use the
stabilizer and invariant machinery from part A, then solve the exact factor
equations over each stated base field.

A plausible bounded conjecture is that generic parameters are inequivalent
apart from a finite correspondence induced by automorphisms of the paired
circuit configuration. Do not assume in advance that the correspondence is
only the diagonal or diagonal plus `b -> b^-1`.

Deliver either:

- equations and witnesses describing every component of the geometric
  correspondence together with the fields of definition and descent data, and
  a separate description of `R(K)` for each finite field used; or
- a rigorously stated partial result with unresolved branches marked `unknown`.

Infer the number of `F_q`-rational decomposition orbits only from `R(F_q)`, with
witness rationality and descent checked explicitly. The current non-permutation
`F_4` check is not full orbit separation over `F_4` or its algebraic closure.

## Certificate discipline and acceptance

- Every run records source hashes, code revision and diff, exact command,
  coefficient field, seeds if any, time/memory limits, and solver statuses.
- Exact positive claims carry independently replayable witnesses.
- Exhaustive negative claims carry a finite coverage certificate or a small
  checker for the complete partition of cases.
- Stabilizer orbit reduction never relies on a hash as proof of equality.
- Tangent dimension is not reported as component dimension.
- Same-support obstruction, full-support obstruction, finite frozen-term
  `UNSAT`, and global nonexistence remain four different conclusions.
- The output should be suitable for later Lean replay through T1–T3, but the
  external search procedure itself need not be formalized in Lean.

## Lower-priority boundary question

The points `b=0` and `b=infinity` are poles of the displayed affine factors.
A separate compactification study may allow legitimate term gauges, compute
DVR valuations and initial summands, and ask for a stable limit. Collective
residue cancellation is not a finite decomposition and does not by itself give
a rank-47 endpoint.
