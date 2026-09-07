# A076142 — mean quasi-log/addition-chain gap

- **Mathematical status:** open empirical asymptotic from OEIS A076142.
- **Work status:** hard-blocked by addition-chain average estimates.
- **Remaining target:** prove existence of the asserted positive constant governing `(∑ k≤n, (quasilog k - NumberComplexity.l k)) * log n / n^2`, including the claimed numerical range if stated.
- **Proved prerequisites:** `Proofs/NumberComplexity/QuasilogChainGap.lean` proves the gap is nonnegative and contains the intended asymptotic statement with `sorry`; `Proofs/NumberComplexity/Quasilog.lean` and `Proofs/NumberComplexity/AdditionChain.lean` provide `quasilog`, `NumberComplexity.IsAddChain`, `NumberComplexity.AdditionChain`, and `NumberComplexity.l`.
- **Next obligation:** establish a genuine average-order theorem for shortest addition chains. Pointwise comparison and a stated limit are not such a theorem.
