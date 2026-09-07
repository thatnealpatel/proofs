# A236397 — Peebles sunflower/capset equality

- **Mathematical status:** open conjecture from OEIS A236397.
- **Work status:** hard-blocked.
- **Remaining target:** for even `n`, prove `A236397(n+1)=2*A090245(n)` using the Peebles poster's sunflower-free weight convention.
- **Proved prerequisites:** `Proofs/BilinearComplexity/CapsetSliceRank.lean` formalizes the weight functional and capset number, proves the one-sided poster theorem `A236397(n)≤A090245(n)`, and proves the Ellenberg–Gijswijt bound. The Peebles equality itself remains intentionally unfinished.
- **Next obligation:** prove the reverse/sharp correspondence needed for equality, not merely another asymptotic upper bound or finite term check.
- **Scope:** the OEIS entry does not define the weight convention; the implementation follows the Peebles 2013 poster. The formerly intended CLP/EG prerequisite is now complete and is not residual work.
