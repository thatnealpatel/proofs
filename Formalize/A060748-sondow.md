# A060748 — bounded ranks in the cubic-sum family

- **Mathematical status:** open conjectural finiteness question of Jonathan Sondow (OEIS A060748).
- **Work status:** hard-blocked.
- **Remaining target:** determine whether Mordell–Weil ranks in the family `x³+y³=m` (birational to `y²=x³-432m²`) are bounded, and formalize the corresponding finiteness statement.
- **Concrete blocker:** Mathlib lacks the Mordell–Weil rank, finite-generation, height, and descent infrastructure needed even to instantiate the statement on concrete curves. A hypothesis-carried surrogate rank is not an acceptable resolution.
- **Next obligation:** obtain an unconditional rank/descent API before attempting this target.
