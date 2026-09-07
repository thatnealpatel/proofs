# A273929 — congruent numbers in classes 5, 6, 7 mod 8

- **Mathematical status:** open unconditionally; known conditionally on BSD through the Tunnell/Monsky lineage.
- **Work status:** hard-blocked for the BSD/rank formulation, but the rank-free statement is unstarted.
- **Remaining target:** for every squarefree `n≡5,6,7 mod 8`, construct a nontrivial rational point on `y²=x³-n²x` (equivalently, prove `n` congruent) without assuming BSD.
- **Available ground:** Mathlib's `WeierstrassCurve` can state rational point existence, and `Proofs/Scratch/CongrCurveIso.lean` handles the same curve family under scaling.
- **Next obligation:** define the congruent-number/point correspondence and prove it, then supply the unconditional point-existence mathematics. Do not replace this by an uninstantiable conditional Mordell–Weil rank functional.
