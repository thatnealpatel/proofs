# Profile inequality bridge checkpoint

## Scope

Focused coordinate-tensor experiment over `ZMod 2`; no `TensorProduct`
equivalence, move semantics, graph, context, Arai, or full-scheme API was
introduced. The implementation remains in scratch pending review and
production extraction.

## Completed endpoint

File: `Proofs/Scratch/ProfileInequalityBridge.lean`

The final theorem
`BilinearComplexity.ProfileInequalityExperiment.pair_triple_profile_finrank_le_six`
starts from five indexed nonzero pure coordinate tensors, injectivity of the
five tensor values, and the displayed binary two-equals-three relation. It
proves

```text
finrank(span(range U)) + finrank(span(range V)) + finrank(span(range W)) ≤ 6.
```

No exact-span or classification hypothesis is assumed. The proof obtains
subset minimality from
`BinaryCircuit.circuit_of_binaryCycle_card_five` and a selected mode of rank at
most two from `PairTripleSpan.pair_triple_span_drop`.

Supporting checked lemmas now include:

- coordinate K1 over fintypes and selected finsets;
- disjoint equal-fiber K1 and singleton-cancellation wrappers;
- a common-nonzero-vector overlap inequality;
- binary finrank-two three-value classification;
- equality and nonvanishing of the three complementary fiber sums;
- local `(3,1,1)` and `(2,2,1)` complementary bounds;
- finite-partition adapters for both fiber-cardinality shapes;
- the selected-mode rank-one and rank-two branches;
- the selected-mode profile inequality;
- the `pair_triple_span_drop` and automatic-minimality endpoint adapter.

A concrete five-term example checks that the endpoint assumptions are jointly
satisfiable and invokes the endpoint theorem.

## Verification

The following command succeeded:

```text
flock .lake/agent.lock lake build Scratch.ProfileInequalityBridge
```

The completed target built successfully in 8,700 jobs. The only reported
warnings came from pre-existing `unusedSectionVars` in imported
`BilinearComplexity.BinaryCircuit` declarations.

The file contains no `sorry`, `admit`, declared `axiom`, or `native_decide`.
`#print axioms` for every theorem in the experiment reports only subsets of:

```text
[propext, Classical.choice, Quot.sound]
```

`git diff --check -- Proofs/Scratch/ProfileInequalityBridge.lean` also passed.

## Correctness-sensitive structure

The proof does not infer fiber nonemptiness directly from minimality. It first
uses selected-mode finrank two to obtain occurring independent values, chooses
a known nonempty proper fiber, proves that fiber's complementary sum is
nonzero by minimality, transfers nonvanishing through equality of the three
fiber sums, and only then proves all fibers nonempty. The six ordered positive
fiber-cardinality cases are dispatched explicitly.

In the rank-one branch, every selected factor equals one occurring nonzero
factor over `ZMod 2`; evaluating at a nonzero coordinate reduces the full
five-term tensor cancellation to the two-mode K1 inequality. In the outer
adapter, the three disjuncts of `pair_triple_span_drop` are handled by explicit
mode orderings rather than an implicit tensor-mode identification.

## Remaining before production promotion

1. Extract a deliberately small production API and remove scratch-only
   examples, `#check`s, and axiom-print commands during extraction.
2. Remove unnecessary ambient `Fintype` and `DecidableEq` assumptions from
   reusable helpers where their public statements permit it.
3. Derive the positive-rank form `sum (r_i - 1) ≤ 3` and the elementary four
   unordered profiles, including the ambient-dimension-three exclusion of
   `411`.
4. Present the theorem as the repository's direct binary coordinate proof.
   Cite Lovitz--Petrov separately for the field-general splitting inequality,
   and mention Ballico only as a separate geometric classification under its
   additional hypotheses; neither source theorem is invoked by this endpoint.
5. Only after production extraction and the profile corollary, begin the typed
   canonical `221` move replay.
