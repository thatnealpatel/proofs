# Certified bounded binary search and field-semantic foundations

This is a partial next tranche after the contextual compiler at `1dbd285`.
It does **not** complete the search-and-field campaign. The existing local
compiler and its contracts remain unchanged.

## Complete binary primitive search

`NormalizedBinaryNativeSuccessors.successors` constructively enumerates all
Split triples, Flip quadruples, and directed Reduction triples in every one of
the six factor orientations. It executes the existing legality checker;
source membership, nonzero terms, distinctness, occupancy, factor equations,
and exact replacement remain native obligations. Duplicate presentations and
duplicate endpoints are deliberately retained. `mem_successors_iff` and
`mem_successors_iff_ambient` prove exact agreement with the existing relations.

`NormalizedBinaryBoundedSearch.optimize D k H hD` has no caller-supplied
optimizer, coverage oracle, or lower bound. Here `hD : D.card ≤ H`. It returns
an actual native `MovePath`, a terminal state, length and altitude bounds, and

$$
\forall p:D\longrightarrow E,\quad
\operatorname{length}(p)\le k\ \land\ \operatorname{altitude}(p)\le H
\quad\Longrightarrow\quad
|\mathrm{result.finish}|\le |E|.
$$

The generic `FiniteBoundedSearch` implementation retains a complete bounded
path tree and folds a deterministic cardinality minimum. It retains the
zero-edge root. Its only pruning is checking the actual cardinality ceiling
on each extension; there is no symmetry quotient or unproved deduplication.
All computational choices are made by the algorithm. The universal lower
bound follows from inductive path coverage, not an external census.

`BinaryAmbientBoundedSearch.optimize eU eV eW D k H hD` exposes the same
contract for arbitrary binary factors with **supplied full ambient linear
coordinate equivalences**. `BinaryAmbientFullFrame` reflects every ambient
native edge and path into these coordinates, preserving vertices, length,
and altitude. Competitors may leave the initial/endpoint spans. Full factor
coordinates—not merely an endpoint `ExactSpanPresentation`—are essential.
No runtime basis selection is used.

This certifies **budget-optimal endpoint cardinality**, not full-component
coverage or unrestricted tensor-rank optimality. It is an exhaustive reference
algorithm, not a scalability result.

## Executions and matrix multiplication

Build the standalone runtime with `lake build binary-search`, then run
`.lake/build/bin/binary-search`. The default runs the successor pilot, rank
certificate and priority S-B1 cases. `binary-search sb1 k H` runs a single
bounded search and emits the source, endpoint and every path vertex as JSON;
`binary-search rank` and `binary-search successors` isolate the other checks.
The native successor pilot counts presentations, including duplicates. The
S-B1 regression module checks
an explicit three-term decomposition of binary row-times-column multiplication
`⟨1,2,1⟩`; a one-edge search discovers a two-term endpoint, while budget zero
retains three terms. A comparison path appears only in the mathematical
optimality proof, not as an input or branch in the optimizer.

Term count means scalar multiplications in the stated bilinear tensor model,
not additions, data movement, or runtime. This small overcomplete-scheme
improvement is an integration regression, not a new matrix-multiplication
rank bound. `BinaryMatMulRankCertificate` separately constructs the seven
Strassen products as a normalized binary finite-set state, checks its exact
matrix-multiplication evaluation, and combines it with the existing independent
`seven_le_rank_matMulTensor_zmod` lower bound. It proves exact tensor rank seven
for binary `2 × 2` multiplication and supplies a generic state-to-`RankLE`
bridge. This is a checked instance of a known result, not search discovery.
Bounded native search alone does not establish the independent rank bound.

## Declared runtime pilot

The frozen S-B1 source is exactly the coordinate triples
`([1,0],[1,0],[1])`, `([1,0],[0,1],[1])`,
`([1,1],[0,1],[1])`. The standalone executions used a 60-second timeout per
case. The following are single-run measurements on the campaign sandbox,
not speedup or scalability claims:

| $k$ | $H$ | Endpoint count | Selected path length | Seconds |
|---:|---:|---:|---:|---:|
| 0 | 3 | 3 | 0 | 0.22 |
| 1 | 3 | 2 | 1 | 0.44 |
| 2 | 3 | 2 | 1 | 1.99 |
| 3 | 3 | 2 | 1 | 40.86 |
| 0 | 4 | 3 | 0 | 0.24 |
| 1 | 4 | 2 | 1 | 0.43 |
| 2 | 4 | 2 | 1 | 4.17 |
| 3 | 4 | **incomplete: timed out** | — | 60.00 |

Successful runs returned altitude three and the same finite set of terms as
the SHA-256-verified frozen input. JSON state arrays use constructive carrier
order; their array order is not asserted to match the input file. Peak runtime
RSS across all eight attempts was at most 95,940 KiB,
below the declared 4 GiB budget. A prior Lean-importer successor execution
used 6,696,084 KiB; this failed the pilot memory budget and is retained
separately from the standalone runtime evidence. The timed-out run has no
reported endpoint result and supplies no computational lower bound. Invalid
ceiling `H=2` is rejected. Raw JSON, exit codes, timings and the input-fidelity
check, archived measured executable, source hashes and baseline-relative source
patch are preserved under `artifacts/search/` in the canonical campaign root.
The strengthened verifier asserts the original fixture SHA before comparing
term sets. No primitive-versus-macro comparison has yet been performed.

## Field-semantic scope

`FieldRankOne` models coefficient-bearing representatives and actual nonzero
pure-tensor atoms over a field. Atom equality is equality of evaluated tensors,
so gauge-equivalent representatives do not create distinct occupancy slots.
It proves coefficient absorption/rescaling and correspondence with valid
ordered schemes without substituting multisets for finite sets.

`FieldContextual` supplies exact finite-set replacement, compatible-context
evaluation, endpoint restoration, semantic composition, and coefficient-correct
Split/Reduction/shear identities. These are semantic replacement lemmas, not
a complete native move enumerator or a field compiler. Subtraction specializes
to addition only under the stated characteristic-two hypothesis. The genuine
ternary relation is

$$A+B=2C+2D+J,$$

where $A,B,C,D$ are the four matrix units and $J$ is the all-ones rank-one
matrix (with a one-dimensional third factor). Actual endpoint atoms include
$2C,2D$, not $C,D$ with silently erased coefficients. The concrete finite
endpoints have cardinalities two and three, are disjoint, and form a proved
five-element linear circuit. A nonempty compatible context tests restoration.
The normalized binary Carrier/State correspondence preserves evaluation and
cardinality. `LinearTransport.mapState` is executable from its supplied
injective atom map; classical recovery of raw representatives and ordered
schemes remains explicitly proof-side. These results do not construct a
canonical ternary factorization algorithm or a native ternary path compiler.

## Remaining campaign acceptance

Automatic recognition of contextual five-circuit macros, recovery of effective
presentations, macro-assisted search, and primitive-versus-macro measurements
are not supplied by these modules. The existing compiler still consumes
supplied local input; it must not be counted again as automatic discovery.

The fixed ternary candidate F3-LG asks for both-direction connectivity inside
the exact factor carrier, with outside context fixed, and local geodesics that
are shortest against unrestricted ambient competitors. Its explicit finite
state bounds use the full local carrier size. No full-class ternary compiler,
coverage theorem, geodesic-localization theorem, or algebraic/contextual
counterexample is established here. Field semantics alone does not complete
that branch.

Canonical preparation, frozen inputs, resource measurements, findings and
remaining obligations are recorded in the single campaign ledger and numbered
documents 25–31 under
`~/x/auto-research/binary-five-circuit/`. No novelty, published-open-problem
resolution, new rank bound, connectivity, or macro-speedup claim is made.
All acceptance proofs must have axiom closure contained in
`{propext, Classical.choice, Quot.sound}`; no `native_decide` or external
search result is a proof dependency. AI assistance is disclosed in the
repository README.
