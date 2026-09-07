# A039669 — Erdős's `m-2^k` completeness conjecture

- **Mathematical status:** open conjecture (Erdős; OEIS A039669 / Erdős problem 1142).
- **Work status:** hard-blocked after a proved finite window.
- **Remaining target:** prove that the positive integers `m>2` for which every `m-2^k` with `k≥1` and `2^k<m` is prime are exactly `4,7,15,21,45,75,105`.
- **Proved prerequisites:** `Proofs/Erdos/Covering/ErdosMinus2k.lean` defines the guarded predicate, proves all seven memberships, and proves completeness through `10^9`; the full theorem is intentionally stated with `sorry`. `Proofs/Erdos/Covering/NotTwoPowerPlusPrime.lean` gives an infinite complementary family.
- **Next obligation:** supply an unbounded argument. The primitive-root congruence reduction formalized for the finite window is due to Chris Nash (2000); it does not prove global completeness. The strongest citable search bound recorded by OEIS is `2^120`, not the unreviewed `2^128` forum computation.
- **Boundary and consolidated A089654 scope:** omitting `m>2` makes `0,1,2` vacuous solutions. The deleted A089654 card adds no independent conjecture: its row `T(n,k)=2n+1-2^k` is exactly this predicate's odd part under `m=2n+1`, and the proved bridge requires `0<n` because row zero is empty and vacuously all-prime. Its six indices `{3,7,10,22,37,52}` map to `{7,15,21,45,75,105}`; OEIS A089654 attributes the conjecture to Erdős and records verification through `2^77` (weaker than A039669's `2^120`).
