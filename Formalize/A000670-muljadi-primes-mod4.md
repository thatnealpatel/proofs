seq:     A000670
claim:   muljadi-fubini-primes-mod4
status:  open
stmt:    S
proof:   hard
module:  Proofs/Enumerative/Fubini.lean
source:  OEIS A000670 comment, Paul Muljadi, 2011-01-28
         (cf. A290376, prime Fubini numbers)

CLAIM
  Every prime Fubini number greater than 3 is
  congruent to 1 mod 4. Known prime Fubini values:
  3, 13, 541, 47293, ... (indices 2, 3, 5, 7, ...;
  per A290376 no further prime up to index 12000).

LEAN
  Statement is immediate:
    forall n, (fubini n).Prime -> fubini n > 3 ->
      fubini n % 4 = 1
  using project fubini and Nat.Prime.

ROUTE
  The completed description of Fubini numbers modulo 4 in
  `Proofs/Enumerative/FubiniMod.lean` gives eventual residues 1,3 on
  alternating indices. It reduces the target to proving that prime values
  cannot occur at the residue-3 positions; index parity alone does not
  obviously control primality.

EVIDENCE
  All known prime Fubini numbers > 3 are ≡ 1 mod 4.
