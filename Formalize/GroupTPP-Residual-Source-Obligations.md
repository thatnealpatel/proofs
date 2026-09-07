# Group-theoretic residual source obligations

This card retains distinct unresolved formalization targets from the deleted source digests. Adjacent definitions or elementary lemmas do not discharge these source-level results.

- **arXiv:0908.3671 — Murthy additive bound.** Prove the source's unresolved lower additive bound for maximal TPP triples, with its exact hypotheses and extremal cases. The current TPP API does not validate the full source statement.
- **arXiv:1009.5526 — commuting-probability results.** Formalize the Nath–Das lower-bound equality characterization, the associated isoclinism invariance, and the odd-order classification at the stated threshold. `Proofs/GroupTPP/CommProbBound.lean` and `Proofs/GroupTPP/IsoclinismInvariants.lean` provide ingredients, not the complete source results.
- **arXiv:1011.2083 — central-index/class-2 classification.** Formalize Yadav's central-index bound and the Property-A class-2 `p`-group classification up to isoclinism. Existing class-2 and isoclinism infrastructure does not establish this combined theorem.
- **arXiv:1104.5097 — exhaustive Tables 1–4.** Reproduce and validate the finite nonabelian-group TPP capacity tables, including the search universe, normalization, and all reported ratios. Existing search predicates are not an exhaustive certificate.
- **arXiv:1107.5969 — subgroup capacity.** Formalize Hedtke's `h(G)` bound and its dependence on subgroup cores and quotient data; existing subgroup-TPP definitions do not prove the capacity theorem.
- **arXiv:1107.5973 — right-quotient growth.** Prove the `2|X| ≤ |Q(X∪{c})| ≤ 3|X|` extension lemma and its exact subgroup hypotheses, rather than relying on finite examples.
- **arXiv:1204.4641 — rank-boundedness/classification.** Formalize the rank-bounded derived-group theorem and the supporting classification for finite groups with bounded central quotient rank. The current group-rank APIs do not provide the source theorem.
- **arXiv:1411.0848 — commutativity spectrum.** Formalize the Eberhard/Joseph limit-point and well-ordering results for commuting probabilities, together with the bilinear-map structural input. The existing finite commuting-probability bounds are only prerequisites.
- **arXiv:2112.08681 — `p`-element commuting probability.** Formalize Theorems A–C, including the normal abelian Sylow characterization, simple-group equality case, and centralizer-ratio bound. `Proofs/GroupTPP/CommProbBound.lean` does not contain these `p`-element results.
- **arXiv:2512.16730 — Conjecture 5.1.** Formalize the unresolved dihedral/abelian-normal-subgroup-of-prime-index conjectural extension beyond the proved `rho₀` bounds and lemmas. The existing `Proofs/GroupTPP/MurthyPrimeIndex.lean` results do not settle Conjecture 5.1.
- **arXiv:2605.02071 — higher-commutativity asymptotics.** Formalize the exact asymptotic and finite-spectrum theorem, including inverse finite-spectrum rigidity, beyond the elementary isoclinism propositions currently present.

**Status:** hard-blocked. These are named residuals, not bibliography claims or completion claims. The source references above are the exact scopes retained from their deleted digests.
