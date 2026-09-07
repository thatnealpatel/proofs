seq:     A090052
claim:   group-perfect-uniqueness
status:  open
stmt:    M
proof:   hard
module:  Proofs/GroupCount/GroupPerfect.lean
source:  OEIS A090052 comments (unattributed
         "seems fairly certain")

CLAIM
  A090052 = group-abundant numbers: n with
  gnu(n) > n. Conjectures in-entry: (i) n = 1 is the
  only "group-perfect" number (gnu(n) = n); (ii)
  almost all n are group-deficient (gnu(n) < n),
  i.e. group-abundant numbers have density 0.

LEAN
  gnu def as in A000001-cdo-iteration.md. (i):
    forall n >= 2, gnu n ≠ n.
  (ii) needs natural density (Mathlib has
  Nat.density-flavored tooling in progress; state via
  limit of counting function / n).

ROUTE
  (i) open in general (needs upper bounds on gnu
  away from 2-heavy orders and exact knowledge at
  them). For squarefree and cube-free n there are
  classical gnu bounds that likely settle those
  strata — a provable partial. (ii) open; Pyber-type
  gnu upper bounds are the tool, far from current
  machinery.

EVIDENCE
  No group-perfect n found in GAP range; abundant n
  are sparse (2-group-heavy orders).
