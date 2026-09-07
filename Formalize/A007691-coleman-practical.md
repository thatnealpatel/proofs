# A007691 — Coleman practical-number conjecture

- **Mathematical status:** open conjecture (Jaycob Coleman, OEIS A007691).
- **Work status:** hard-blocked: its odd case would rule out odd perfect numbers.
- **Remaining target:** prove that every positive multiply-perfect number is practical.
- **Proved prerequisites:** `Proofs/Enumerative/Practical.lean` defines `Nat.Practical` and `Nat.IsMultiperfect`, proves the Stewart step and standard practical-number infrastructure, proves the even-perfect case, and states the full target with an intentional `sorry`. `Proofs/Enumerative/StewartCriterion.lean` proves Stewart's criterion in both directions.
- **Next obligation:** prove the claim for odd multiply-perfect numbers (or first prove the still-useful even multiply-perfect case beyond abundancy two). Bounded certificates and the formal conditional implication to nonexistence of odd perfect numbers do not discharge this obligation.
