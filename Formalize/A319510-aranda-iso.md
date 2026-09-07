# A319510 — rank invariance under `n↦4n`

- **Mathematical status:** the curve isomorphism is proved; the OEIS rank formula remains an empirical claim until a rank layer identifies it precisely.
- **Work status:** hard-blocked.
- **Remaining target:** deduce `rank(E_n)=rank(E_{4n})` for `E_n : y²=x³-n²x`, and verify that this is exactly A319510's indexing convention.
- **Proved prerequisite:** `Proofs/Scratch/CongrCurveIso.lean` constructs an additive equivalence of affine point groups for `n≠0`, induced by `(x,y)↦(4x,8y)`, and proves the discriminant/non-singularity conditions.
- **Next obligation:** add a genuine Mordell–Weil rank definition invariant under this equivalence, then pin the OEIS identification without a squarefree normalization or index shift.
