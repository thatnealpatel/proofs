# Context-stable binary five-circuit compilation

## Public entry points

Import `BilinearComplexity` for the complete API, or import
`BilinearComplexity.BinaryContextualConcreteTrace` for the contextual compiler
and its optimality and trace dependencies.

`BinaryContextualFiveCircuitCompiler.compileContextualBinaryFiveCircuit`
consumes an effective `ExactSpanPresentation`, the local endpoint proofs, and
the supplied finite context with its endpoint-disjointness proof. It returns a
`ContextualBinaryFiveCircuitCompilation`. There is no caller-supplied path,
lower-bound callback, requested distance, or run-time basis selection.

The ambient terms are nonzero rank-one terms over `F2`, with finite-set states.
For the selected problem, the local endpoints are disjoint sets `A`, `B` with
cardinalities two and three, equal tensor evaluation, and circuit union. The
context `C` need only be disjoint from `A ∪ B`. In particular, it may occupy the
local exact-span carrier. The effective presentation is data supplied to the
compiler; abstract existence of coordinates is not used as a run-time choice.

## Exact local distance and returned paths

For `result := compileContextualBinaryFiveCircuit ...`, the public result API
includes:

| API | Contract |
| --- | --- |
| `result.label`, `result.ambient_membership` | Computed label and semantic `AmbientInOrbit` membership of the actual local endpoints |
| `result.forward`, `result.reverse` | Actual native ambient `MovePath`s from `C ∪ A` to `C ∪ B` and back |
| `result.forward_length`, `result.reverse_length` | Both lengths equal `orbitDistance result.label` |
| `result.forward_altitude_le`, `result.reverse_altitude_le` | Both altitudes are at most `C.card + 4` |
| `result.forward_outside`, `result.reverse_outside` | Every vertex agrees exactly with `C` outside the local exact-span carrier |
| `result.forward_path_length_ge`, `result.reverse_path_length_ge` | Every ambient competitor has length at least the computed orbit distance |
| `result.forward_shortest`, `result.reverse_shortest` | The actual returned paths are globally shortest for their respective contextual endpoints |
| `result.certified_optimality` | Joint orbit, exact-length, altitude, and both-direction shortestness certificate for the same runtime result |

The shortestness methods are supplied by
`BinaryContextualFiveCircuitOptimality`. They quantify over **all** native
ambient competitors, including paths that leave the local spans or change
outside context terms. They do not impose locality or freshness on competing
paths. The common distance is indexed by the existing thirteen exact-span
factor/mode orbits:

| Orbit labels | Distance |
| --- | ---: |
| `221-01`, `221-02`, `221-03` | 2 |
| `411-01` | 3 |
| `321-01`, `321-02`, `321-03` | 3 |
| `321-04`, `321-05`, `321-06` | 2 |
| `222-01` | 3 |
| `222-02`, `222-03` | 2 |

The value is uniform over endpoint-disjoint contexts and ambient realizations
of the orbit; it is not a distance measured only inside a searched local box.
The theorem `orbitDistance_compileContextualBinaryFiveCircuit_eq` explicitly
proves independence from both the context and the supplied effective
presentation for fixed ambient endpoints, by comparing the two independently
compiled empty-context paths using global optimality.
If `L = localBox P` is the nonzero rank-one carrier of the three exact factor
spans, every vertex `Y` of either returned path satisfies

$$Y\setminus L=C\setminus L.$$

Terms of `C ∩ L` may be removed temporarily. All of `C` is restored at the
macro endpoint, whose exact state is part of the dependent `MovePath` type.
There is no factor-separation or path-wide context-retention assumption.

## Concrete compositional trace compiler

`BinaryContextualConcreteTrace.compileContextualJump` returns a concrete
`MacroCompilation` for each proof-bearing `ContextualFiveCircuitJump`.
The jump supplies its context, local endpoints, direction, effective
presentation, and endpoint equalities. The compiler selects the actual forward
or reverse ambient path and fills the global `shortest` certificate.

The generic trace interface's orbit field alone is unverified metadata.
The concrete adapter closes that gap with
`compileContextualJump_ambient_membership` and
`compileContextualJump_distance`, binding the actual local endpoint orbit and
its canonical distance. `compileContextualJump_outside` also certifies the exact
outside-box invariant for every vertex of the adapted macro path. No compiler
interface remains as a public input to `ContextualTrace.compileConcrete`.

For a trace with `m = macroCount` contextual replacements and
`n = primitiveCount` primitive steps, the concrete APIs prove

$$\operatorname{length}(\operatorname{compileConcrete}(t))
=n+\operatorname{concreteMacroDistanceSum}(t)
=n+\sum_i d_i\le n+3m.$$

`ContextualTrace.compileConcrete_length` supplies the exact accounting;
`compileConcrete_length_le` supplies the budget. The theorem
`compileConcrete_altitude_le` gives

$$\operatorname{altitude}(\operatorname{compileConcrete}(t))
\le \operatorname{maxStateCard}(t)+1=R+1.$$

Here `R` is the largest cardinality of an explicit input trace state, not a
bound on a search or on a silently expanded input. Context restoration occurs
at every macro boundary, so temporary overhead does not accumulate. Singleton
and primitive-only traces are included. Optimality is certified for each
macro, **not** for the concatenation of a supplied trace. No procedure for
finding macro traces between arbitrary endpoints is claimed.

## Native exclusion proof and trust boundary

The lower-bound chain is explicit:

1. Native edges have symmetric-difference support of size three or four.
   The five-term endpoint difference rules out paths of length zero or one.
2. A hypothetical two-edge path has one auxiliary term and supports of sizes
   three and four. Three-support factor geometry puts that auxiliary in the
   endpoint exact spans, even for an unrestricted ambient competitor.
3. Ambient context reflection and finite orbit-action reflection produce an
   actual normalized contextual competitor at a selected row.
4. `BinaryContextualExclusionSemantics` checks valid encodings and line/Flip
   algebra. `BinaryContextualExclusionEnumeration` checks complete five-term
   partitions and four-term permutation handling.
5. `BinaryContextualFlipReflection` checks native four-support occupancy in
   all six orientations. `BinaryContextualNativeExclusion` proves the full
   native-short-path implication to `hasContextualTwoEdgePath`, including both
   support orders and the two possible auxiliary-occupancy bits.
6. The five kernel-evaluated false results therefore yield native contextual
   lower bounds of three. The other eight rows use the universal lower bound
   of two. Optimality transport uses the same `orbitDistance` as the upper paths.

The raw Boolean false calculations alone are not native exclusions. The full
implication in step 5 is essential. Likewise, external search produced upper
path candidates only; Lean checks their native moves, guarded occupancy
coverage, endpoints, lengths, and transport. See
[NormalizedBinaryContextual.md](NormalizedBinaryContextual.md) for the preserved
candidate-generation provenance and coordinate conventions.

All relevant new public declarations are audited for axiom closure within
`{propext, Classical.choice, Quot.sound}`. No `sorryAx`, project-specific axiom,
`native_decide`, or external census is used to establish these contracts.
The only primitive semantics are intrinsic Split, Flip, and directed
Reduction; there is no Plus, cancellation edge, arbitrary replacement edge,
or multiset substitution.

## Collision-bearing executable certificates

`BinaryContextBorrowing221` supplies the minimal-profile-221 example in which
no native path between the contextual endpoints can retain every context term
at every vertex. The public ambient compiler and concrete trace compiler both
execute this instance in the two native directions. Their observed vertex
cardinalities and lengths are

```text
([6, 6, 7], 2, [7, 6, 6], 2)
```

The public `collisionRoundtripTrace221` composes the two contextual jumps using
the same context. Its actual concrete compilation prints

```text
([6, 6, 7, 6, 6], 4, 2, 0, 7, 7)
```

The entries are vertex cardinalities, compiled length, macro count, primitive
count, largest input-state cardinality, and compiled altitude. This checks the
compositional execution; it does not assert that the round trip is a globally
shortest path between its identical endpoints.

These executions traverse the effective presentation, classification,
context recovery, actual native path compilation, and ambient restoration;
they do not bypass the public compiler by calling a normalized row directly.
The impossibility of retaining all context is a separate kernel-checked
statement, not a conclusion inferred from this runtime output.

## Scope and attribution

This development closes the selected internal local-rewrite and compiler
obligations. It does not claim resolution of a named published open problem,
global flip-graph connectivity, discovery of arbitrary macro traces, a new
tensor-rank bound, or an empirical search-performance improvement. In
particular, the concatenation bound is not a global endpoint-shortestness
claim. AI-assisted development is disclosed in the repository `README`.
