# A064097 — Cloitre's quasi-log upper bound

- **Mathematical status:** open empirical inequality from OEIS A064097; Wilson's lower bound is proved.
- **Work status:** hard-blocked.
- **Remaining target:** for `n>1`, prove the original strict inequality `quasilog n < 2.5 * Real.log n` (the existing non-strict formal statement is intentionally unfinished).
- **Proved prerequisites:** `Proofs/NumberComplexity/Quasilog.lean` defines the completely additive quasi-log, proves its defining clauses and `Nat.log 2 n ≤ quasilog n`, and contains the intended upper-bound `sorry`.
- **Next obligation:** control prime steps using more than naive induction: that induction would require `2 ≤ 2.5*log 2`, which is false. A proof must exploit additional structure in `p-1` or bound prime-chain behavior.
