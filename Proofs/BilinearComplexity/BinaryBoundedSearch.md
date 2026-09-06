# Certified bounded binary search and field-semantic foundations

This is a partial next tranche after the contextual compiler at `1dbd285`.
It does **not** complete the search-and-field campaign. The existing local
compiler and its contracts remain unchanged. The first-tranche compiler
optimizes supplied replacements: it does not discover traces, establish global
connectivity, minimize unrestricted tensor rank, prove new matrix-multiplication
bounds, or extend automatically to other fields. In particular, the first-tranche
claims about the thirteen binary exact-span orbits, context-stable shortest
native paths, outside-span preservation, endpoint restoration, and the
minimal-221 borrowing obstruction remain baseline claims, not discoveries of
this tranche.

## Effective coordinates and exact presentations

`BinaryEffectiveSpanCoordinates.effectiveSpanCoordinates` is an executable,
deterministic constructor for a finite binary coordinate span. It exhaustively
tries candidate families of rank at most the supplied ambient coordinate
dimension. Its validity guard checks that every candidate vector is represented
by the input generators, that the full coefficient map has zero kernel
(`Function.Injective`, not just injectivity of the displayed tuple), and that
every input generator is represented by candidate coefficients. The selected
linear equivalence has the theorem-backed certificate
`r = Module.finrank F2 (Submodule.span F2 (S : Set ...))`.

This is a runtime exhaustive enumerator, not a runtime semantic `finrank`,
chosen basis, or choice-backed inverse. Its regressions cover empty and
zero-only spans, a nonzero singleton, duplicate input, the dependent family
`e1,e2,e1+e2`, and full spans in dimensions 0 through 3.

`BinaryEffectiveExactSpanPresentation.effectiveExactSpanPresentation` applies
that constructor independently to the three endpoint factor projections in
supplied full ambient frames. It takes the generators from `A ∪ B` and
transports the resulting explicit coordinate equivalences to the corresponding
ambient factor spans. Thus it supplies an exact effective presentation for a
recognized endpoint pair; it does not replace the full ambient frames needed
when competitors may leave the endpoint spans.

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
native edge and path into these coordinates, preserving vertices, length, and
altitude. Competitors may leave the initial/endpoint spans. Full factor
coordinates—not merely an endpoint `ExactSpanPresentation`—are essential. No
runtime basis selection is used.

This certifies **budget-optimal endpoint cardinality**, not full-component
coverage or unrestricted tensor-rank optimality. It is an exhaustive reference
algorithm, not a scalability result.

## Automatic contextual macro recognition

`BinaryContextualMacroRecognition` recognizes both directed uses of a
five-circuit replacement. Given a current state `D` and supplied full frames,
`forwardKeys` enumerates a two-term source among `D` and a three-term target
among all ambient terms. Independently, `reverseKeys` enumerates a three-term
source among `D` and a two-term target among all ambient terms. The reverse
loop therefore does **not** incorrectly restrict its two-term target to `D`.
`rawKeys` keeps the direction tags disjoint.

`Applicable` checks the two cardinalities, endpoint disjointness, exact
coordinate evaluation equality, and the direction-specific source/context
conditions. An accepted key recovers its unchanged context by set difference,
constructs an effective exact-span presentation, and invokes the existing
contextual compiler. `RecognizedMacro` stores the key and applicability proof,
with computable accessors for its endpoints, context, presentation, compiler
result, semantic orbit certificate, and actual expanded native path. The existing
compiler supplies the semantic
orbit and its contextual shortestness certificate; recognition does not
reclassify the binary orbits.

`PassesBounds` tests the **actual expanded path**: its primitive length and
`MovePath.altitude`, which covers every internal vertex, not a generic
`|C|+4` estimate. Recognized compiled paths have exact primitive length two or
three and positive cost. No presentation, key, classifier, path, or coverage
oracle is supplied by a caller. The primitive successor adapter remains
complete independently of macro recognition.

## Oracle-free macro-assisted optimizer

`BinaryMacroBoundedSearch` retains all primitive successors and adds only
finite, certified recognized blocks. `Step.primitive` stores the actual
primitive edge; `Step.macroStep` stores a `CachedMacro` at its actual
intermediate source state together with its admission proof. The cache retains
the dependent `RecognizedMacro`, the actual path computed during admission,
and equality to that object's directed native path. `admittedMacros_keys`
proves literal ordered key-list equality with `recognizedKeyList`, including
duplicates. The same applicability and complete path bounds are tested.
`CachedMacro.ofRecognized` wraps manual semantic objects when needed.

The `Trace` type retains these nodes. Its `cachedMacros_results` theorem proves
ordered projection to the semantic macro list, and `cached_macro_factorization`
proves literal cached native segments. `Trace.macro_factorization` proves that
every reported macro is literally a segment of the expanded native path. The
same factorization is exposed for the selected result by
`Result.macro_factorization`; it is not an attached label or a reconstructed
post-processing annotation.

`Candidate.extend` charges `step.path.length`, so a macro costs its actual
compiled primitive length. `extensions` checks the entire expanded prefix for
both `length ≤ k` and `altitude ≤ H`; consequently every intermediate macro
vertex is subject to the declared ceiling. An early numerical guard skips
constructing macros only when `prefix.length + 2 > currentLayer`; primitive
successors remain unconditional. `extensions_eq_unpruned` proves literal list
equality with the complete available-step map and final bounds filter.
`boundedCandidates_complete` retains
complete coverage of every bounded intrinsic ambient **primitive** path, even
when no macro is available. There is no state deduplication, symmetry quotient,
heuristic pruning, or assumed macro-generation theorem. The root candidate
keeps the domain nonempty.

`BinaryMacroBoundedSearch.optimize` is therefore an oracle-free exhaustive
optimizer against every bounded ambient native competitor. Its primary
objective is minimum endpoint cardinality. Its sole secondary rule is narrow:
on equal endpoint cardinality it prefers a trace containing a macro over a
macro-free trace, and only in the orientation where the left trace is
macro-free and the right trace is not. All other equal-cardinality ties retain
the left candidate. This is not a shortest-trace, fewest-block, or global
macro-usage theorem. The source theorem `optimize_card_eq_primitive` proves
equality of the macro and primitive optimum cardinalities under the same full
frames and `(k,H)` domain; it does not assert a performance gain.

## Executions, baselines, and status

The frozen S-B1 source is exactly the coordinate triples
`([1,0],[1,0],[1])`, `([1,0],[0,1],[1])`, and
`([1,1],[0,1],[1])`. The existing standalone `BinarySearchMain` driver and
`NormalizedBinarySearchRegression` establish the earlier primitive baseline:
budget zero retains three terms, and a one-edge bounded search discovers a
two-term endpoint. The comparison path used in that proof is an independent
ambient competitor, not an input or branch in the optimizer. These are frozen
S-B1 discovery/integration regressions, not new discoveries.

`BinaryMatMulRankCertificate` independently constructs the known seven-term
Strassen state, checks its binary `2 × 2` multiplication evaluation, and uses
the existing independent `seven_le_rank_matMulTensor_zmod` lower bound to
certify the known rank-seven instance. This is a baseline anchor, not a new
rank result and not a result of bounded search. Term count means scalar
multiplications in the stated bilinear tensor model, not additions, data
movement, or runtime.

`BinaryMacroSearchMain` is a built compiled-native driver, available through
`lake build binary-macro-search`. Its `primitive k H`, `macro k H`, and
`activated k H` modes emit actual vertices, evaluations, primitive-edge replay
checks, and retained macro provenance. Cached macro paths are used in both
trace expansion and serialization. `canonicalReplayState` re-enumerates occupied
terms through constructive `FinEnum` representatives; its theorem proves exact
state identity. `edgeReplay_eq_direct` proves literal equality of the resulting
Boolean list to the original complete native-successor membership checks.
No edge check, relation, optimizer candidate, or budget is changed.

The first frozen native comparison used fresh processes with a 60-second
limit and 4 GiB address-space cap. All four primitive runs completed with
endpoint cardinalities `3,2,2,2` in the matrix order below; macro runs at `k=0,1`
completed with the same cardinalities. The two cost-two macro runs and the
borrowing activation run each timed out. Successful paths passed independent
coordinate evaluation and native-edge replay. These failures remain preserved;
they establish no selected macro, endpoint, lower bound, or speedup. The
subsequent admitted-path caching repair is proved and built; a second archived
run of the same frozen matrix still timed out in those three cost-two cases.
Both failed rounds remain preserved. A four-process payload diagnostic then
isolated expensive primitive-edge replay; provider completion and actual vertex
serialization succeeded independently. Following the proved replay-state
identity repair, a third run completed **all nine processes** under the same
60-second/4-GiB limits. Independent coordinate evaluation and native-edge replay
passed throughout. The input SHA-256 remains
`63bbfb5be99d49fee8686431b77f1a99f1a7fee777dfaf478b4be29a05a29ffa`;
the successful executable SHA-256 is
`a458a321688e77fd9bef610352059640dc85f0fd125fa6cb506ad454b1bf168a`.

| `(k,H)` | Primitive card / wall seconds | Macro card / wall seconds |
| --- | --- | --- |
| `(0,3)` | 3 / 5.84 | 3 / 5.80 |
| `(1,3)` | 2 / 6.31 | 2 / 6.17 |
| `(2,3)` | 2 / 7.86 | 2 / 20.78 |
| `(2,4)` | 2 / 10.48 | 2 / 24.05 |

Both cost-two macro runs selected one genuine two-edge macro, with vertex
cardinalities `[3,2,2]` and altitude 3. Their longer selected paths agree with
the stated cardinality objective and macro tie preference, not a shortest-path
objective. The separate automatic borrowing run completed in 25.56 seconds
and returned three candidates; each carries one forward `221` row-0 macro of
distance 2, context cardinality 4, and expanded cards `[6,6,7]`. The largest
process RSS in this matrix was 109,420 KiB. These are single-run measurements,
not a speedup claim: macro search was slower than primitive search in the
cost-two comparison. Boundary runs at `k=0,1` alone would not establish macro
activation.

The frozen comparison contract is field `F2`, dimensions `(2,2,1)`, the
SHA-256-identified S-B1 input, identical full frames and objectives, and the
matrix `(k,H)=(0,3),(1,3),(2,3),(2,4)`. A separate activated-macro regression
uses the declared borrowing context at `k=2,H=7`; the successful third run
obtained nonempty automatic admission and inspected actual expanded vertices
and provenance.
Whole-process measurements include module initialization, replay and
serialization, not just search. The one-key diagnostic that motivated caching
is not a replacement for a completed optimizer/provider run.

## Field-semantic foundations and exact scope

`FieldRankOne` models coefficient-bearing representatives and actual nonzero
pure-tensor atoms over a field. Atom equality is equality of evaluated tensors,
so gauge-equivalent representatives do not create distinct occupancy slots. It
proves coefficient absorption/rescaling and correspondence with valid ordered
schemes without substituting multisets for finite sets.

`FieldContextual` supplies exact finite-set replacement, compatible-context
evaluation, endpoint restoration, semantic composition, and
coefficient-correct Split/Reduction/shear identities. These are semantic
replacement lemmas, not a complete native move enumerator or arbitrary-field
compiler. Subtraction specializes to addition only under the stated
characteristic-two hypothesis. The genuine ternary relation is

$$A+B=2C+2D+J,$$

where `J` is the all-ones rank-one matrix with a one-dimensional third factor.
Actual endpoint atoms include `2C` and `2D`, not `C` and `D` with silently
removed coefficients. The concrete endpoints have cardinalities two and three,
are disjoint, and form a proved five-element linear circuit; a nonempty
compatible context tests restoration. These facts do not provide a ternary
native compiler or F3-LG result. See `FieldContextualStructure.md` for the
new field-native and profile API synthesis.

## Remaining campaign acceptance and review status

The previously missing Goal 1 cost-two activation/comparison executions now
pass on the frozen domain, in addition to the checked bounded optimizer.
These executions fill the declared comparison/activation gap; they do not
change the optimizer's bounded scope. Goal 2 still requires
either a full-class F3 compiler with coverage and ambient geodesicity or a
kernel-checked substantive F3-LG obstruction. The new
`FieldTernaryFiveCircuitPair` proves the full-class shared-two-ray theorem in
arbitrary F3 ambient dimensions and computes a checked pair certificate from
displayed factor families; this does not resolve that compiler/obstruction
branch. No F3 orbit classification, native compiler, ambient
geodesicity, connectivity, novelty, published-open-problem resolution, new
matmul rank bound, or macro speedup is claimed here.

Canonical preparation, frozen inputs, resource measurements, findings and
remaining obligations are recorded in the single campaign ledger and numbered
documents 25–54 under `~/x/auto-research/binary-five-circuit/`. Independent
semantic, vacuity/trust/effectivity, and foundations/status reviews are
required; their verdicts and checkpoint disposition must be recorded in that ledger.
All acceptance proofs must have axiom
closure contained in `{propext, Classical.choice, Quot.sound}`; no
`native_decide` or external search result is a proof dependency. AI assistance
is disclosed in the repository README.
