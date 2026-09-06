# Field-contextual structure and the ternary boundary

This document synthesizes the current field-native and generic five-circuit
APIs after the binary kernel. It is a documentation record, not a completion
claim for Goal 2. The fixed ternary results below are an executable
profile-`(2,2,1)` instance; they do not establish full F3-LG connectivity,
ambient geodesicity, an orbit classification, or an arbitrary-field compiler.

## Semantic atoms, coefficients, and gauges

`FieldRankOne` distinguishes an actual semantic atom from a chosen
coefficient-bearing presentation. An `Atom k a b c` is identified extensionally
by its evaluated nonzero tensor. A representative has a nonzero scalar
coefficient and nonzero factors; coefficient absorption (`Rep.absorbFirst`)
and rescaling show that a coefficient can be moved into a factor without
changing the actual tensor. `atom_surjective` proves that every semantic atom
has a coefficient-absorbed presentation, but this is an existential theorem,
not a runtime canonical representative or gauge-selection algorithm.

`FieldNativeMoves.Factor` is a nonzero coordinate factor. Its `atom u v w`
constructor uses coefficient one and evaluates to
`evalFactors 1 u v w`. Distinct factor triples can therefore denote the same
occupancy atom. The native state is a finite set of actual atoms, not a
multiset of presentations: gauge-equivalent presentations do not create extra
slots. All source-order variants and all factor-role orientations are retained
unless a stated theorem identifies them.

The ternary fixture makes this distinction essential. In
`FieldContextual.F3Profile221`,

- `atomA.val = A`, `atomB.val = B`;
- `atom2C.val = (2 : F3) • C`, `atom2D.val = (2 : F3) • D`;
- `atomJ.val = J`.

Thus the endpoint state contains the actual atoms `2C` and `2D`, not unscaled
`C` and `D` with a coefficient silently discarded. The relation is

$$A+B=2C+2D+J,$$

and the ordered actual tensor family has the signed relation vector
`(1,1,2,2,2)` in `F3`. In `FieldFiveCircuitProfile.F3Fixture`, the same
coefficients are absorbed explicitly in the first factors
`(e0,e1,2 • e0,2 • e1,e0+e1)`. This is coefficient absorption, not a claim
that the corresponding actual atoms are equal.

## General field-native local moves

`FieldNativeMoves` is parameterized by an arbitrary field `k` and coordinate
dimensions `a,b,c`. It supplies coefficient-correct semantic formulas rather
than a binary representation shortcut.

### Split and directed Reduction

`AddFormula` carries two nonzero factors, a proof that their sum is nonzero,
and exact presentations of the source and two outputs. `SplitFormula` has
three constructors, `first`, `second`, and `third`, for splitting in each
factor position. `SplitFormula.eval_eq` proves the source tensor is the sum of
the two output tensors. `NativeReplacement.split` turns such a formula into a
singleton-to-pair relation, with output distinctness checked explicitly.

`NativeReplacement.reduction` is the directed pair-to-singleton inverse of a
Split formula. It is not an unrestricted equal-evaluation replacement and does
not add cancellation, `Plus`, or a general replacement primitive.

### Flip/shear in all six orientations

`ShearFormula` retains the order of the two varying factor presentations and
requires both the sum and difference to be nonzero. Its formulas implement

\[
 (x_1,y_1),(x_2,y_2)
 \longmapsto
 (x_1+x_2,y_1),(x_2,y_2-y_1).
\]

`FlipFormula` has exactly the six ordered factor-role constructors:

1. `firstSecond`,
2. `secondFirst`,
3. `firstThird`,
4. `thirdFirst`,
5. `secondThird`,
6. `thirdSecond`.

`FlipFormula.eval_eq` checks exact tensor evaluation for every orientation.
`FlipFormula.symm` proves the coefficient-correct inverse in the same ordered
orientation. The inverse uses a negated varying factor and the reversed
difference; the paired negations are a product-one gauge change. It is not
just the characteristic-two identity `-x=x`. `NativeReplacement.flip` also
requires distinct source and target atoms.

### Global native steps and reversal

`NativeReplacement` contains only Split, directed Reduction, and the six
ordered Flip orientations. `NativeStep D E` stores the local source and target,
source occurrence in `D`, target freshness against
`stateDifference D source`, and the exact erase/insert equation for `E`.
`NativeStep.eval_eq` proves evaluation preservation. Freshness is against the
unchanged state; the general native step does not itself impose local
source/target disjointness or exclude a state-changing failure mode.

`NativeReplacement.symm` and `NativeStep.reverse` provide algebraic and global
reversal. Reversal recovers the erased source exactly and preserves the
coefficient-correct local relation. `NativeStep.reverse` is an ordinary `def`;
its proof fields use classical finite-set reasoning. The explicitly
noncomputable complement/path constructions are a separate boundary described
below. Neither reversal nor those constructions supply an arbitrary canonical
factorization or a caller-free runtime path generator.

## Strict paths, restoration, and complement transport

`FieldNativePath.StrictNativeStep` strengthens a native step with disjoint
local source and target and a proof that the global state changes. This is the
precise strictness needed for complement transport; it excludes self-loop and
partially overlapping Flip presentations. `StrictNativeStep.reverse` is
available and preserves strictness.

`CarrierPath P D E` stores a strict path together with a subset proof at every
vertex. It exposes `start_subset`, `end_subset`, and `snoc`. The
noncomputable `StrictNativeStep.complement` maps a strict step inside a finite
carrier contravariantly,

\[
 D\longrightarrow E
 \quad\mapsto\quad
 P\setminus E\longrightarrow P\setminus D,
\]

using the inverse local relation. `CarrierPath.complement` reverses an entire
carrier-bounded strict path and supplies the corresponding subset proofs.
These constructions are reusable finite-carrier path transport, not a
connectivity or shortest-path theorem. Their exact scope is:

- both endpoints must be subsets of the same explicitly supplied finite
  carrier `P`;
- the transported path is strict at every local step;
- self-loop/overlap Flip cases are excluded rather than silently mapped;
- the construction is noncomputable in the current API;
- no general complement equivalence for nonstrict paths is proved.

The identity/self-loop issue is substantive: a local relation can preserve an
endpoint set while its complement does not have the corresponding native
self-loop. A safe path theorem therefore transports strict steps and may omit
stutters; it does not assert universal complement edge equivalence. Likewise,
reversal/restoration proves local semantic facts and path construction for
supplied proof objects, not geodesicity against all ambient competitors.

`FieldContextual` separately supplies `stateUnion`, `stateDifference`,
compatible-context evaluation, and erase-endpoint restoration. These exact
finite-set identities explain how an unchanged context is restored around a
replacement. `LinearTransport.mapState` can execute transport when given an
explicit injective atom map and tensor linear map; it does not construct such a
map from arbitrary factor embeddings, prove factor-span correspondence, or
provide a canonical gauge choice.

## Fixed F3 all-context two-step certificate

The actual executable fixture regression is fixed at `F3 = ZMod 3` and factor
dimensions `(2,2,1)`. Define

- `A2 = {atomA, atomB}`;
- `B3 = {atom2C, atom2D, atomJ}`;
- `contextSource C = C ∪ A2`;
- `contextTarget C = C ∪ B3`.

The context hypothesis is exactly
`Disjoint C (stateUnion A2 B3)`. It says that the outside finite semantic
context is disjoint from all five endpoint atoms. It does not assert that the
context is empty or that its atoms lie in a smaller hand-chosen list.

`FieldNativeRegression` constructs the actual local formulas and checks all
nonvanishing, distinctness, source-membership, freshness, and exact
erase/insert equations. Let `atomQ` be the borrowed atom represented by
`e1 ⊗ (e0+e1) ⊗ 1`. There are two executable branches.

### q absent

When `atomQ ∉ C`, `absentExecution` uses:

1. `Split` `atomB ↦ atom2D + atomQ`, retaining `atomA`;
2. `Flip` `(atomQ, atomA) ↦ (atomJ, atom2C)`.

The middle state is `absentMiddle C = {atomA,atom2D,atomQ} ∪ C`, and the
endpoint is exactly `contextTarget C`. This is the split-then-flip diamond.

### q present

When `atomQ ∈ C`, `presentExecution` uses:

1. `Flip` `(atomQ, atomA) ↦ (atomJ, atom2C)`, borrowing `atomQ` from `C`;
2. `Split` `atomB ↦ atom2D + atomQ`, restoring the borrowed atom.

The middle state is
`presentMiddle C = {atomB,atomJ,atom2C} ∪ C.erase atomQ`, and the endpoint
again is exactly `contextTarget C`. This is the flip-then-split diamond.

`allContextForward C hC` selects solely on the decidable membership test
`atomQ ∈ C`, not on an external census or path oracle. `allContextReverse C
hC` reverses the certified execution using the proved native inverses. The
reverse branches are therefore inverse-flip then reduction for the q-absent
context, and reduction then inverse-flip for the q-present context.

The checked cardinality theorems give source card `C.card + 2`, target card
`C.card + 3`, and middle card `C.card + 3` in the absent branch or
`C.card + 2` in the present branch. Every forward and reverse execution has
altitude at most `C.card + 3`.

The executable `TwoStepExecution.actualProjection` reports the actual start,
middle, and end cardinalities followed by the two local source/target arities.
The four current projections are exactly:

```text
forward, q absent:  ([2, 3, 3], [(1, 2), (2, 2)])
forward, q present: ([3, 3, 4], [(2, 2), (1, 2)])
reverse, q absent:  ([3, 3, 2], [(2, 2), (2, 1)])
reverse, q present: ([4, 3, 3], [(2, 1), (2, 2)])
```

`runtimePlan` is a computable two-label summary of these four branch plans,
and `runtimeCardTrace` is a computable cardinality summary. The
proof-bearing executions themselves retain actual atoms, local formulas, and
restoration proofs; the summaries are not substitutes for replay. The
`TwoStepExecution.path` and `.reverse` projections expose strict paths for
these supplied certificate objects. This is a fixed-fixture all-context
certificate, not a generic compiler.

### Ambient and dimension boundary

The all-context theorem is proved only for the actual `(2,2,1)` F3 fixture and
its stated semantic context condition. Do **not** generalize it to larger
ambients, arbitrary factor embeddings, or all profile-221 realizations without
an explicit factor/evaluation/path-transport lemma. In particular, a fixed
`(2,2,1)` coordinate proof is not an ambient-geodesicity theorem. The current
modules do not classify all ternary circuits, all F3 orbits, or all native
paths against unrestricted ambient competitors.

## Generic five-circuit profile structure

`FieldFiveCircuitProfile` now supplies a genuine arbitrary-field structural
layer, independent of the fixed native F3 path layer. For coordinate families
`x,y,z` over any field, `IsProductRelation` records a coefficient-bearing
linear relation among five evaluated pure tensors. `IsMinimalFiveProductCircuit`
requires a nonzero relation and that every relation with at least one zero
coefficient is zero. The theorem
`minimalFiveProductCircuit_iff` identifies this coefficient-minimality
criterion with `EveryDeletionIndependent`, i.e. linear independence after each
single-index deletion. `EveryDeletionIndependent.linearIndependent_restrict`
then gives independence for every proper indexed subfamily.

The built arbitrary-field results are:

- `productFamilyRank_eq_four`: the span rank of the five actual product
  tensors is exactly four;
- `factorRank_sum_le_six`: the sum of the three factor-family span ranks is at
  most six, under nonzero factors and coefficient-minimality;
- `four_le_factorRank_product`: the product of the three factor span ranks is
  at least four;
- `factorRank_profile`: the rank triple is, up to `List.Perm`, one of
  `[4,1,1]`, `[3,2,1]`, `[2,2,1]`, or `[2,2,2]`.

These statements quantify arbitrary fields and use coefficient-minimality,
not the binary all-ones/XOR relation. The proof-side `familyRank` is a span
rank; it does not construct runtime bases or a factorization compiler. The
profile theorem is structural and does not assert orbit counts, native
reachability, contextual restoration, or ambient shortestness.

The genuine F3 instantiation `F3Fixture` supplies nonzero factors, identifies
its product family with the existing actual fixture family, proves
`isMinimalFiveProductCircuit`, records the signed relation, proves the generic
rank-sum/product/profile consequences, and proves the exact factor ranks
`(2,2,1)` via `factorRanks_eq_221`. It is a checked nonbinary instance, not a
full F3 classification or a new tensor-rank claim.

## Full ternary shared-two-ray certificate

The new production module `BilinearComplexity.FieldTernaryFiveCircuitPair`
adds a full-class algebraic certificate over `F3 := ZMod 3`. Its public theorem
`exists_shared_two_factor_rays` takes arbitrary ambient dimensions
`a,b,c : ℕ` and displayed factor families
`x : Fin 5 → Fin a → F3`, `y : Fin 5 → Fin b → F3`, and
`z : Fin 5 → Fin c → F3`. Its hypotheses are only nonvanishing of every
displayed factor and `IsMinimalFiveProductCircuit x y z`. It concludes
`HasSharedTwoRayPair x y z`: distinct indices `i,j` share factor rays in
`x,y`, or in `x,z`, or in `y,z`. The dimensions are not restricted to two;
the conclusion concerns the exact factor spans in the supplied ambients.

Here “same ray” is not literal vector equality. `SameRay u v` is defined
explicitly as `u = v ∨ u = (2 : F3) • v`, and
`sameRay_iff_exists_smul` proves the equivalent form
`∃ d : F3, d ≠ 0 ∧ u = d • v`. Thus the two ternary nonzero scalars are the
ray choices `1` and `2`; a displayed equality such as `u = 2 • v` is a factor-
ray equality even when `u` and `v` are different vectors. The certificate never
silently replaces this projective relation with literal factor equality.
The auxiliary relation is deliberately zero-aware: `SameRay 0 0` holds, and
`HasSharedTwoRayPair` alone does not assert nonvanishing. Their projective
interpretation uses the main theorem's explicit nonzero hypotheses. The
standalone executable certificate enforces its own nonzero boundary below.

### Ambient-independent four-ray bound and the 222 case

The proof establishes the required finite-ray bound without assuming an
ambient dimension bound. For any five nonzero vectors in a factor family whose
span rank is at most two, the span has at most `3^2 = 9` vectors over `F3`,
so its nonzero vectors represent at most four projective rays (the two
nonzero scalar representatives of each ray). Five displayed factors therefore
contain a distinct same-ray pair. This is a proof-side cardinality argument;
it does not enumerate a basis or ask the caller for one, and it is not a
runtime `finrank` computation.

For profile `(2,2,2)`, `rank222_pair` starts with that repeated ray and uses
the nonzero minimal relation supplied by `IsMinimalFiveProductCircuit`.
The determinant test selects an exact two-dimensional factor-span projection.
Contracting the relation against that test leaves support of size one, two,
or three: size one contradicts nonvanishing; size two gives proportional outer
factors in both remaining modes; size three is resolved by the checked
three-term outer-relation dichotomy and the corresponding secondary-support
contraction. The result is one of the three two-mode ray-sharing alternatives.
This is the complete 222 argument, not a caller-supplied pair or a
classification oracle.

The proof then consumes the existing arbitrary-field
`factorRank_profile` in all `List.Perm` orientations. Its oriented case split
handles `[4,1,1]`, `[3,2,1]`, and `[2,2,1]` by a rank-one family being
same-ray across all five indices and a second family of rank at most two; the
`[2,2,2]` branch uses the argument above. Consequently the theorem is stated
for every ordering of all four existing profiles, rather than only a sorted
presentation. The earlier arbitrary-field product-family rank four,
rank-sum-at-most-six, product-at-least-four, deletion-independence, and exact
F3 `(2,2,1)` fixture claims are unchanged.

### Executable bounded scan and the genuine fixture

The module also exposes `Orientation` (`xy`, `xz`, `yz`), `Candidate`, and the
executable `scan`. The candidate list has exactly 300 entries, proved by
`candidates_length`: ordered pairs of five indices, the three orientations,
and two nonzero F3 scalars for each of the two displayed ray equalities.
`Candidate.Valid` checks distinct indices, all three factor vectors at both
indices are nonzero (six checks), both scalars are nonzero, and the selected
two proportionality equalities. Thus the standalone `scan_sound` certificate
has a genuine projective interpretation even without a minimal-circuit
hypothesis. `scan_isSome` proves that the scan succeeds under the same
arbitrary-ambient nonzero and minimal-five hypotheses; `certifiedScan` returns
the proof-bearing subtype `{candidate // Candidate.Valid candidate x y z}`.

The checked regressions `scan_all_zero_eq_none` and
`scan_zero_dimensional_eq_none` reject the all-zero and zero-dimensional
families; their actual evaluations both return `none`. A successful standalone
scan certifies the returned pair, not that the whole input is a minimal circuit.

This runtime does not compute factor ranks or `finrank`, choose bases, receive a
caller pair, or consult an existence oracle. The factor families are inputs to
the scan and to the certified wrapper. This API is a finite shared-ray
certificate, not a general runtime extractor that factors arbitrary atoms into
factor families.

On the genuine `F3Fixture`, `fixtureCertificate` is selected by the scan, not
hard-coded. The build log records the exact evaluation

```text
{ first := 0, second := 2, orientation := xz,
  firstScalar := 2, secondScalar := 1 }
```

and the kernel-checked theorem `fixture_scan_execution` proves the exact result

```text
scan F3Fixture.first F3Fixture.second F3Fixture.third =
  some ⟨0, 2, .xz, 2, 1⟩
```

The scan has no endpoint partition: its returned pair may be across endpoint
groups, and this pair-level algebraic fact does not imply that a contextual
`Reduction` is legal. In particular it does not provide a compiler or prove
F3-LG connectivity, ambient geodesicity, or an obstruction. It is a structural
certificate that can supply a pair to later coefficient-correct transformations,
subject to their independent occupied-context and restoration hypotheses.

The locked production build completed successfully at 8704 jobs. The recorded
standard-axiom audits for the new public results report only the project’s
existing `propext`, `Classical.choice`, and `Quot.sound` dependencies; the log
contains linter warnings but no build failure. This status does not alter the
remaining full F3-LG branch below.

## Reusable limits and remaining Goal 2 status

Reusable field-independent content currently includes evaluated-atom semantics,
coefficient absorption/rescaling, exact contextual union/difference
restoration, coefficient-correct local evaluation, native inversion, and
strict finite-carrier path transport within the hypotheses above. It does not
include an arbitrary-field native compiler, a canonical all-gauge runtime
enumerator, or a factor-embedding transport theorem for arbitrary ambient
spaces.

Full F3-LG—both-direction connectivity for the complete local carrier together
with local geodesicity against unrestricted ambient competitors—remains absent.
A substantive kernel-checked obstruction to that full statement is also
absent. The all-context `(2,2,1)` diamond is surviving positive instance
structure, not either branch of the full Goal 2 acceptance. No orbit
classification, ambient geodesicity, arbitrary-field compiler, copied binary
13-orbit count or constants, novelty/open-problem resolution, or new-rank
claim is made.

Independent semantic, vacuity/trust/effectivity, foundations, and status
reviews remain pending for the overall tranche. This document records current
source status and exact assumptions; where a generic executable reversal or
transport would require an API not presently present, that limitation is
reported rather than inferred away.
