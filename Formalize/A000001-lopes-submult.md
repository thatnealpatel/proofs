# A000001 — gnu submultiplicativity

- **Mathematical status:** conjecture (Jorge R. F. F. Lopes, OEIS A000001).
- **Work status:** hard-blocked; only the coprime case is proved.
- **Remaining target:** for all positive `i,j`, prove `gnu i * gnu j ≤ gnu (i*j)` without assuming `i.Coprime j`.
- **Proved prerequisite:** `Proofs/GroupCount/Submult.lean` proves the coprime case using direct products and also records `2 ≤ gnu 9` and `4 ≤ gnu 36`.
- **Next obligation:** replace the coprime order argument by a construction that remains injective on isomorphism classes when the factors share primes. Direct products alone do not supply that injection.
