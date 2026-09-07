# Rank-49 deformation T1 — exact scheme semantics

- **Mathematical status:** infrastructure theorem package, not a tensor-rank claim.
- **Work status:** hard-blocked; substantial public modules exist, but the acceptance target is partial.
- **Remaining target:** finish an exact standard-action witness (sandwich matrices, gauges, term permutation, and six orientations), certificate transport/composition, and the narrow theorem that repeated-factor enumeration is complete for ordinary nontrivial two-term flips over `F₂`.
- **Proved prerequisites:** `Proofs/BilinearComplexity/Scheme.lean`, `SchemeAction.lean`, `SchemeReplacement.lean`, and `SchemeFlipReduction.lean` provide ordered semantics, basic actions, deterministic local replacement, validity bookkeeping, and flip identities.
- **Proved prerequisite:** accepted main revision `4b6938dc2aa2fb5655f22433f2aeee02bf2377b3` publishes `BilinearComplexity.AffineCollisionNativeWitness.exists_strictNativeFlip`, one concrete strict native Flip witness in a five-atom fresh context. It does not supply the general collision-to-useful-operation interface or the standard-action transport.
- **Next obligation:** discharge the relevant theorem obligations in `Proofs/BilinearComplexity/SchemeMoveAlgebra.lean`, which deliberately contains `sorry`; then connect the published witness to a small independently replayed action/replacement example. A valid length-49 presentation proves only `RankLE 49`, not minimal rank.
