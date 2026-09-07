# Rank-49 deformation T2 — restricted derivatives

- **Mathematical status:** general soundness infrastructure for deformation filters.
- **Work status:** hard-blocked; the algebraic core is substantial, but certificate/scalar-extension acceptance remains.
- **Remaining target:** provide a replayable finite-elimination certificate for restricted Jacobian rank, kernel/gauge quotient, and inconsistency, together with the scalar-extension theorem needed to transport an `F₂` rank exclusion to every field extension.
- **Proved prerequisites:** `Proofs/BilinearComplexity/SchemeDeformation.lean` formalizes linear, quadratic, cubic and mixed coefficients, restricted variation modules, quotient/cokernel obstruction classes, finite truncated arcs, and scoped no-lift theorems without `sorry`.
- **Next obligation:** connect the external `4096×2352` computations to those abstract declarations through checked pivots/kernel/range witnesses. A same-support obstruction rejects only that support and correction scope; it does not prove finite or global rigidity, component dimension, or absence of another point.
