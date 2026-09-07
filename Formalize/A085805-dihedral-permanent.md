# A085805 — permanent of a dihedral character table

- **Mathematical status:** open OEIS conjecture (Yuval Dekel's 2003 comment): nonvanishing occurs exactly for group orders congruent to `4 mod 16`.
- **Work status:** hard-blocked; one direction is proved only for an explicit table family.
- **Remaining target:** prove nonvanishing for every order `16m+4` and identify the explicit matrices with the actual character tables of Mathlib's `DihedralGroup` under the order convention.
- **Proved prerequisites:** `Proofs/Scratch/DihedralPermanent.lean` proves vanishing outside `4 mod 16` for the explicit textbook matrices and computes orders 4 and 20. It also records the nonvanishing proposition without proving it.
- **Next obligation:** formalize the dihedral character-table bridge and prove the structured permanent is nonzero in the remaining congruence class. A table checked at finitely many orders is not that bridge.
- **Convention:** OEIS `D_k` denotes order `k`; A017089 is the associated index sequence, and the permanent values are A086641.
