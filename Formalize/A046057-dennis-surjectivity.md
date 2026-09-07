# A046057 — Dennis gnu-surjectivity

- **Mathematical status:** open conjecture of R. Keith Dennis (OEIS A046057).
- **Work status:** hard-blocked.
- **Remaining target:** prove `∀ n ≥ 1, ∃ m, GroupCount.gnu m = n`.
- **Proved prerequisites:** `Proofs/GroupCount/DennisSurjectivity.lean` defines the target, pins the least witnesses for values one and two, and preserves the corrected A053403 evidence: that companion lists 508 values not yet realized within the search, with largest known term 55487.
- **Proved prerequisite:** accepted main revision `4b6938dc2aa2fb5655f22433f2aeee02bf2377b3` publishes Proofs/GroupCount/HolderPQ.lean, theorem `GroupCount.gnu_mul_primes`, the full Hölder `pq` formula. It realizes only a structured family of `gnu` values and does **not** imply Dennis surjectivity.
- **Next obligation:** consume `GroupCount.gnu_mul_primes`, characterize its witness values, and construct witnesses for every remaining positive value; Dennis surjectivity remains open.
