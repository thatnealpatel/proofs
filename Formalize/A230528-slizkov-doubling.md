# A230528 — addition-chain doubling gap

- **Mathematical status:** open question of Alexey Slizkov (OEIS A230528).
- **Work status:** hard-blocked; counterexample-searchable but not currently dispatched.
- **Remaining target:** prove or refute `∀ k, NumberComplexity.l k - NumberComplexity.l (2*k) ≤ 1`.
- **Proved prerequisites:** `Proofs/NumberComplexity/SlizkovDoubling.lean` states the exact question and proves the elementary append-a-doubling inequality; `Proofs/NumberComplexity/AdditionChain.lean` provides `NumberComplexity.IsAddChain`, `NumberComplexity.AdditionChain`, `NumberComplexity.l`, and `l_two_mul_le`. The checked range through `k=50000` is evidence only.
- **Next obligation:** either give a structural bound on the possible saving or provide an explicit `k` together with certified optimal chain lengths witnessing a larger deficit.
