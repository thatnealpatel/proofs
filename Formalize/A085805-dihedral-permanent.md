seq:     A085805
claim:   dihedral-permanent-16m4
status:  VANISHING DIRECTION PROVED 2026-08-20
         (sorry-free, Proofs/Scratch/
         DihedralPermanent.lean, uncommitted; full
         reviewer trio passed): permanent = 0 for
         every dihedral order not ≡ 4 (mod 16), for
         the explicit textbook table family (bridge to
         Mathlib's DihedralGroup char table NOT
         formalized — disclosed; family certified
         externally = true tables, orders 4-40).
         Orders 4, 20 certified (8, -576; order 20 by
         exact ℤ√5 kernel decide).  Nonvanishing
         (M ≡ 1 mod 4) archived as a named Prop; order
         36 needs ℚ(cos π/9) arithmetic, out of kernel
         reach.  CONVENTIONS PINNED: OEIS D_k = order
         k (data-pinned; entry never defines it;
         cross-ref A017089 = 8n+2 is the index
         sequence); the "Probably" comment is Yuval
         Dekel's (Jul 24 2003, submitter); permanent
         values are published as A086641 (7 terms,
         a(6)-a(7) Irvine Jul 2026).  Adjacent art:
         Schmidt–Simion 1984 (S_n vanishing criterion,
         via A086644).
stmt:    M
proof:   route: two permanent involutions (column
         scaling by the alternating linear character;
         column permutation j ↦ M-j), reduction
         perm = 2(P_B − P_A); verified exactly in Sage
         to M = 10 before dispatch
module:  Proofs/GroupTPP/CharDegrees.lean (dihedral
         degrees), DihedralTPP
source:  OEIS A085805 comment (unattributed
         "probably")

CLAIM
  A085805 = k such that the permanent of the
  character table of the dihedral group D_k is
  nonzero. Conjecture in-entry: these are exactly the
  numbers of the form 16m + 4.

LEAN
  Matrix.permanent exists in Mathlib
  (LinearAlgebra.Matrix.Permanent). Missing: the
  dihedral character table as a concrete matrix —
  Mathlib has DihedralGroup and the project has
  dihedral commProb work; the explicit table (four
  1-dim characters + 2-dim cos characters, split by
  parity of k) must be built. That table is
  independently valuable (first explicit character
  table as data in the project; feeds DihedralTPP).

ROUTE
  Permanent of the structured table should reduce to
  a trigonometric/root-of-unity product with a clean
  vanishing criterion — plausibly a finite symbolic
  computation per congruence class of k mod 16.
  Compute first (Sage side) to confirm the 16m+4
  pattern and locate the vanishing mechanism before
  any prover dispatch.

EVIDENCE
  Pattern over computed range in-entry; NOT verified
  in this sweep — treat the exact form (16m+4,
  conventions for D_k) as unpinned until the entry is
  re-read.
