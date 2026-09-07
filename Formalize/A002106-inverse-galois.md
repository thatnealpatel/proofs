seq:     A002106
claim:   transitive-groups-are-galois-groups
status:  open (equivalent to inverse Galois over Q)
stmt:    L
proof:   hard-open (major)
dependency: no inverse-Galois realization infrastructure exists in the project
source:  OEIS A002106 comment, Charles R Greathouse
         IV, 2014-05-28; equivalence to inverse
         Galois noted in-entry (Jianing Song,
         2025-05-26)

CLAIM
  A002106(n) = number of transitive permutation
  groups of degree n up to conjugacy in S_n.
  Comment-conjecture: this equals the number of
  groups arising as Gal(f) for irreducible degree-n
  f over Q — equivalent to the inverse Galois
  problem restricted through transitive embeddings.

LEAN
  Mathlib has Polynomial.Gal, galActionHom into
  Equiv.Perm (rootSet), transitivity for irreducible
  polynomials (galAction_isPretransitive). Missing:
  enumeration of transitive subgroups up to
  conjugacy, and everything realization-theoretic.
  L is for the counting statement; the ">=" direction
  (every Galois group of an irreducible f IS
  transitive) is already essentially in Mathlib and
  is the one formalizable fragment.

ROUTE
  Statement-archive. Do not dispatch.

EVIDENCE
  Equality holds for all n where both sides are
  known (small n).
