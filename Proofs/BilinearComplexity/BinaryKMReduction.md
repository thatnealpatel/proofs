# Contextual compilation of indexed binary KM Reductions

## Scope and entry point

Import `BilinearComplexity.BinaryKMReduction`. The effective entry point is
`BinaryKMReduction.compile d context hcontext`. Its result contains an actual
`MovePath BinaryAmbientMoves.AllModeMove` between the two finite-set endpoints.
It does not accept a residual path, an occupancy schedule, a coverage oracle,
or classical coordinates as runtime inputs.

This is a binary specialization of the **broader indexed-family Reduction**
of Kauers–Moosbauer (KM), not a new Plus identity. It compiles into the existing
Split/Flip/directed narrow-pair Reduction relation. It adds no primitive and
changes neither the accepted five-circuit theorem nor its competitors.

The implementation works in arbitrary modules over `F2` with decidable equality.
Finite coordinate modules provide executable examples. The working factor order
is `(b,c,a)`, with the common factor **third**. The usual printed common-first
formula is written `(a,b,c)`; these are named factor roles, not an undocumented
change of tensor convention. The API covers this ordered family directly; it
is not a claimed all-field normalization or symmetry-quotient compiler.

## Exact representation and admissibility

`BinaryKMIndexedData.Data n` supplies nonzero vectors
$a,b_0,c_0,b_i,c_i$ for $i\in\mathrm{Fin}(n)$, with

$$b_0=\sum_i b_i,\qquad c_i+c_0\ne0,$$

and an injective source presentation $i\mapsto(b_i,c_i)$. In working order put

$$P=(b_0,c_0,a),\quad T_i=(b_i,c_i,a),\quad U_i=(b_i,c_i+c_0,a).$$

These are the existing nonzero binary factor-triple atoms. There is no list
multiplicity, projective-ray quotient, or silently discarded scalar.
Over `F2` the only nonzero scalar is one, so proportional nonzero common factors
are literally equal. An indexed KM coefficient-zero term is unchanged: it
belongs to the supplied context, not to `Data`'s coefficient-one active family.
The dependence witness is effective input; the compiler does not discover all
possible dependences in an arbitrary decomposition.

The source is $A=\{P\}\cup\{T_i\}$ and the target is $B=\{U_i\}$.
`d.ContextAdmissible context` means the context is disjoint from **both** whole
endpoints. The compiler derives target injectivity, pivot distinctness,
evaluation equality, and

$$|C\cup A|=|C|+n+1,\qquad |C\cup B|=|C|+n.$$

**The local endpoints may overlap.** `d.changedIndices` computes the indices
whose $U_i$ is not in the active source. All other indices occur in two-cycles
of $c\mapsto c+c_0$; they contribute zero to the discarded $b$-sum and are
left unchanged. This preprocessing is proved, not a caller-supplied partition.
If $m=|\mathrm{changedIndices}|$, then $1\le m\le n$.

Zero outputs, repeated indexed inputs, and outputs colliding with unchanged
context are outside this admissible rank-decreasing operation. In particular,
`Finset.image` is not a cancellation mechanism: two occurrences contribute
zero in characteristic two but their set image contributes one nonzero atom.
Omitting a zero term preserves an indexed sum, but does not instantiate the
selected nonzero-output, exactly-one-term-drop contract. No such omitted or
colliding case is silently relabeled a certified transition.

## Returned quantitative certificate

For `result := BinaryKMReduction.compile d C hC`:

| Field | Meaning |
|---|---|
| `path` | Actual native path from `d.sourceEndpoint C` to `d.targetEndpoint C` |
| `localCosts` | Computed occupancy-selected primitive costs, one for each changed index |
| `costs_length`, `costs_one_or_two` | Exactly $m$ costs, each one or two |
| `length_eq_sum` | Actual expanded path length equals the sum of those costs |
| `length_lower`, `length_upper` | $m\le\operatorname{length}\le2m\le2n$ |
| `altitude_le` | Every vertex has cardinality at most $|C|+n+1$ |
| `carrier`, `carrier_eq` | Computed finite endpoint/residual/bridge carrier |
| `outside_fixed` | Every vertex has the initial membership outside that carrier |

The lower bound $m$ here describes **this construction**, not all competing
native paths. Neither the compiler nor the cost list certifies shortestness.

`Compilation.carrier_factors_in_original_spans` places every carrier atom in
the original local factor spans. `compile_outside_carrier` gives the finite-set
outside equality; `context_restored` and `fixedState_restored` state exact
endpoint retention. These do **not** say context is retained at every vertex.

## Collision-aware mechanism

The changed indices are sorted effectively. The current residual is the sum
of the remaining $b_i$'s; zero and repeated residuals are allowed. A nonzero
residual gives a pivot $(r,c_0,a)$. Exchanging one $T_i$ for $U_i$ toggles the
old and new pivots. Their intermediate appearances telescope by symmetric
difference; only the initial pivot is removed in the final state.

`BinaryKMNativeToggle.compileThreeSupportToggle` implements a degenerate
three-support transition in one native step. For nonzero old and new residuals,
`compileFourSupportToggle` examines their actual occupancy:

- Different occupancies: one Flip.
- Both present: two Reductions.
- Both absent: two Splits.

In a two-step branch the bridge $(b_i,c_0,a)$ is created before consumption
when absent, or consumed before restoration when already occupied. This is
why arbitrary occupied intermediate contexts do not require a freshness
assumption. Every local path has altitude at most the larger boundary card;
the global boundary invariant yields the no-growth bound.

This mechanism covers every active arity, not a finite circuit table. In
particular the public five-active-index case is a **six-term to five-term**
replacement, beyond the minimal-five $2|3$ catalogue. Endpoint-overlap and
zero-residual cases are included by the same compiler, not special recipes.

## Composition

`compilePair` consumes two admissible indexed families and a proof that the
first target equals the second source; it computes both paths itself.
`compilePair_observations` proves that primitive lengths add and actual
altitudes combine by maximum. `compilePair_bounds` gives

$$m_1+m_2\le L\le2(m_1+m_2),\qquad H\le|D_0|.$$

The second operation starts at a state one term smaller than the first source,
so intermediate overhead does not accumulate. `compilePair_outside_fixed`
preserves initial membership outside the union of the two computed carriers.
The suffix recursion also exposes exact local-cost recurrence through
`compileSuffix_localCosts_cons`. These are supplied-operation composition
results, not discovery of an optimal sequence between arbitrary endpoints.

## Published comparison and what is added

Primary sources:

- Kauers–Moosbauer, *Flip Graphs for Matrix Multiplication*,
  [arXiv:2212.01175](https://arxiv.org/abs/2212.01175), Definition 2 and
  Proposition 3 (indexed Reduction), Definition 4 (Flip), Definition 8 and
  Theorem 9 (graph and weak connectivity).
- Moosbauer–Poole, *Flip Graphs with Symmetry and New Matrix Multiplication
  Schemes*, [arXiv:2502.04514](https://arxiv.org/abs/2502.04514), the Remark
  immediately following the Flip/Reduction/Plus formulas: every general
  Reduction is asserted to sequence as Flips followed by a simple Reduction.

The KM tensor identity and MP algebraic sequencing assertion are prior art.
The additional contract here is an **effective legal finite-set simulation in
arbitrary endpoint-disjoint contexts**, including transient occupancy borrowing,
zero residuals and endpoint overlap, with explicit expanded costs, no-growth,
restoration and carrier bounds. This is not a priority or mathematical-novelty
claim merely because those details were not found in the inspected sources.

| Published operation/model | This API's coverage |
|---|---|
| Indexed KM Reduction with one-dimensional common-factor span and dependent second-factor family | The displayed binary, coefficient-one active witness with the exact admissibility above; arbitrary active arity |
| KM Flip and simple pair Reduction | Existing native laws, used only with exact nonzero/distinct/freshness conditions |
| Original directed KM graph | **Not** graph equality/inclusion: the native simulation may use upward Splits |
| KM graph's symmetry orbits | Not a quotient-state implementation; atoms and states remain explicit |
| Reverse Reduction and Plus augmentations | No added edge and no universal coverage claim |
| Arbitrary-field scalar redistribution or multiset/Gaussian rank-drop operations | Unsupported by this binary API |

A broad KM Reduction is one source-level macro edge; its native expansion is
charged at the actual returned length, never at unit primitive cost. For a
covered minimal-five $3\to2$ replacement, the enlarged macro graph permits the
single broad edge while the accepted **native** distance remains two or three.
The existing native borrowing obstruction remains a native statement; it
cannot be transferred unchanged to a graph allowing the entire replacement
as one context-fixed edge. This compiler need not attain the accepted
five-circuit shortest length; reuse that compiler when its sharper contract is
wanted. No new orbit census or five-circuit optimality claim is made here.

## Verification and implementation handoff

`BinaryKMRegression` contains the four frozen public inputs: six-to-five with
empty and occupied contexts, an internal-zero-residual family, and an
endpoint-overlap family. Its packets must expose the actual `path.vertices`,
expanded costs and carrier; printed summaries alone are not execution evidence.
Campaign evidence and final review dispositions are recorded in the single
external ledger, under documents 67–70 and `artifacts/km/`.

For another implementation, use the precise `Data` guards above, the computed
changed-index filter, sorted residual recursion and occupancy table. Recognition
of a dependence and execution of a supplied certified dependence are distinct.
Return actual states/steps; preserve the bridge-occupancy ordering, and validate
full endpoint and outside-carrier restoration. No Go implementation, benchmark
speedup, or formal verification of Go is claimed by this Lean API.

`BinaryKMMain` is the standalone native driver. Build and run the unchanged
four-input packet set with:

```text
flock .lake/agent.lock lake build binary-km-regression
.lake/build/bin/binary-km-regression
```

The frozen native run emitted these actual compiler traces:

| Case | Local costs | Primitive length | Vertex cardinalities | Altitude |
|---|---|---:|---|---:|
| Six-to-five, empty context | `[1,1,1,1,1]` | 5 | `[6,6,6,6,6,5]` | 6 |
| Same family, occupied auxiliaries | `[2,2,1,1,1]` | 7 | `[8,7,6,7,8,8,8,7]` | 8 |
| Internal zero residual | `[1,1,1]` | 3 | `[4,3,4,3]` | 4 |
| Endpoint overlap | `[1]` | 1 | `[4,3]` | 4 |

The occupied case has context-cardinality trace `[2,1,1,1,2,2,2,2]`, making
actual borrowing and restoration visible. An independent Sage replay checked
all sixteen emitted edges against all six orientations of the unchanged native
formulas, exact finite-set endpoints, tensor evaluation, costs, no-growth and
outside-carrier preservation. This finite replay is additional execution
evidence, not the proof of arbitrary-arity coverage.

The command is a reproducible public-API execution, not a performance comparison.
The interpreter attempts exceeded the declared 4 GiB limit and remain preserved
as failures. The unchanged four-input compiled-native run exited successfully
under a 60-second/4-GiB limit, measured at 0.10 seconds and 84,700 KiB peak RSS.
No search speedup or broader performance guarantee follows from that measurement.

The accepted binary five-circuit and bounded-search kernels are preserved.
The predecessor's full F3 compiler and unrestricted ternary optimality remain
incomplete and deferred; this binary theorem does not discharge them.
