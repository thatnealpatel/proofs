# A083207 — Ianakiev tau-sigma conjecture

- **Mathematical status:** open conjecture (Ivan N. Ianakiev, OEIS A083207, 2020-04-24).
- **Work status:** hard-blocked after two proposed routes were refuted.
- **Remaining target:** if `d>1`, `d∣k`, and `tau(d)*sigma(d)=k`, prove that `k` is Zumkeller.
- **Proved prerequisites:** `Proofs/Enumerative/ZumkellerTauSigma.lean` formalizes the exact target and a conditional odd-perfect-number consequence.
- **Next obligation:** find new structural mathematics. The claims that the hypotheses force `6∣k` or that a suitable unitary Zumkeller divisor always exists are false (`d=496` and `d=234` respectively), so neither is a viable route. The conditional reduction is not a proof.
