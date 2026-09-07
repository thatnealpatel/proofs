# A031507 — Mordell-curve rank records

- **Mathematical status:** open growth problem suggested by the Gebel–Pethő–Zimmer observations recorded at OEIS A031507.
- **Work status:** hard-blocked.
- **Remaining target:** formalize and prove a substantive growth statement for the least positive `k` such that `y²=x³+k` has Mordell–Weil rank `n`.
- **Concrete blocker:** Mathlib has no usable Mordell–Weil rank, finite-generation, height, or descent layer. A theorem conditional on a per-curve finite-generation hypothesis would not furnish a satisfiable instance and is not an acceptable substitute.
- **Next obligation:** first obtain an unconditional Mordell–Weil rank/descent API capable of handling a concrete curve; only then state the record-growth target.
