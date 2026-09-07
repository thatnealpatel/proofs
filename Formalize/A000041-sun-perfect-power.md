seq:     A000041
claim:   sun-no-perfect-power
status:  open
stmt:    S
proof:   hard
module:  Proofs/Enumerative/PartitionPerfectPower.lean
source:  OEIS A000041 comment, Zhi-Wei Sun,
         2013-12-02

CLAIM
  No partition number p(n) (n >= 1) is a perfect
  power x^m with x > 1, m > 1.

LEAN
  Nat.Partition exists with Fintype, so
  p n = Fintype.card (Nat.Partition n). Define
    IsPerfectPower N := exists x m, 2 <= m ∧ 2 <= x ∧
      x ^ m = N
  (absent from Mathlib; IsPrimePow is unrelated).
  Statement is then one line.

ROUTE
  Open (deep arithmetic of the partition function).
  Statement-archive; the IsPerfectPower def is
  trivially reusable. Bounded verification via
  computed p(n) values is the only near-term
  activity.

EVIDENCE
  Verified for large computed ranges of p(n)
  (in-entry discussion).
