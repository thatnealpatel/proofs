# Normalized binary transport 221 spike checkpoint

## Compiled

`NormalizedBinaryTransport221Spike.lean` transports the designated profile-221 replay into profile `(3,3,2)` using the non-coordinate linear maps

- `(x,y) ↦ (x+y,y,x)` in the first and second factors, and
- `x ↦ (x,x)` in the third factor.

The file proves injectivity on vectors and carrier triples, maps finite-set states by `Finset.image`, and proves exact cardinality preservation. It proves reusable transport lemmas for a generated first-factor Split, source third-factor Flip, and directed narrow pair Reduction. These proofs transport every formula, freshness/collision condition, membership condition, and exact replacement equation; they do not merely evaluate mapped endpoints. The concrete forward and reverse labeled paths compile and both have length two and exact altitude three.

## Blocker

The production predicates `GeneratedFirstSplit`, `SourceThirdFlip`, `DirectedNarrowPairReduction`, their `Move`, and their preservation theorems are specialized through `Term := Carrier profile221` and `State221 := State profile221`. Consequently a mapped profile-332 edge cannot inhabit the existing production `Move` relation even though all defining laws transport. The spike therefore uses profile-polymorphic local copies of only those three predicates and a local three-constructor move relation. No broader move-system redesign was attempted.

## Exact next production refactor

Parameterize the three predicate definitions, their local evaluation/cardinality lemmas, and the tagged `Move` relation in `NormalizedBinaryReplay221.lean` by `{p : Profile}`, retaining `Term`/`State221` aliases and the existing concrete replay as profile-221 specializations. Generalize the existing move-preservation and `MovePath` metric infrastructure only as far as required for these three constructors. Then move the three private transport lemmas from the spike into one small transport module parameterized by factorwise injective additive maps; no certificate, orbit, permutation, context, or full-scheme API needs to change.
