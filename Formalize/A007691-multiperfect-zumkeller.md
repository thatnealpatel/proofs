# A007691 — multiply-perfect numbers are Zumkeller

- **Mathematical status:** open conjectural subsequence assertion recorded by OEIS A083207.
- **Work status:** hard-blocked; the perfect-number slice is proved.
- **Remaining target:** prove `IsZumkeller n` for every multiply-perfect `n > 1`, in particular the unresolved abundancy-at-least-three cases.
- **Proved prerequisites:** `Proofs/Enumerative/MultiperfectZumkeller.lean` proves every perfect number is Zumkeller, proves the practical-to-Zumkeller bridge, and checks nine listed examples. `Proofs/Enumerative/ZumkellerSigmaHalf.lean` supplies the published practical-number characterization.
- **Next obligation:** obtain a divisor-partition argument for non-perfect multiply-perfect numbers. The conditional consequence of Coleman's open conjecture is not a proof of this target.
