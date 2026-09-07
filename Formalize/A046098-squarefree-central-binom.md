# A046098 — squarefree central binomial coefficients

- **Mathematical status:** known theorem in the central-binomial formulation (Granville–Ramaré); OEIS A046098 asserts the resulting 13-term list.
- **Work status:** hard-blocked; the unbounded power-of-two stratum remains.
- **Remaining target:** prove the full A046098 list is complete, equivalently complete the theorem that `Nat.centralBinom n` is not squarefree for all `n≥5`.
- **Proved prerequisites:** `Proofs/Erdos/Erdos175/NotSquarefree.lean` proves the non-power-of-two case without a bound and the power-of-two case through `2^30`.
- **Next obligation:** formalize the Granville–Ramaré exponential-sum argument for arbitrary powers of two. The bounded certificate is not an unbounded proof.
