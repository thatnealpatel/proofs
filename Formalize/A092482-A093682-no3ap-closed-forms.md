seq:     A092482, A093682
claim:   no3ap-closed-forms
status:  rows 3-6 LANDED 2026-08-20 (sorry-free,
         Proofs/Scratch/No3APClosedForms.lean,
         uncommitted; full reviewer trio passed).
         EPISTEMIC CORRECTIONS: row 0 = Szekeres's
         A003278 (not Sze); rows 1-5 carry OEIS
         "proved by Lawrence Sze" credits (2004, via
         Stephan, no located write-up) — the "rows ≥ 3
         unproved" premise was wrong; the underlying
         structure theorem is Odlyzko–Stanley 1978
         (memo, proofs omitted; printed Thm 2
         defective) with published proof in Rolnick,
         EJC 59 (2017).  Tier: formalization, plus a
         machine-forced OEIS data correction —
         A093680's printed residual 19 must be 18
         (fails at n ≡ 8 mod 16), issue
         thatnealpatel/proofs#37 — and, as far as
         searched, the first written-out derivation of
         the exact A093681 periodic formula.  The
         A092482 closed form itself was NOT attempted
         by the campaign file (rows only).
stmt:    M
proof:   M-L
module:  none
source:  OEIS A093682 formulas (unattributed
         conjecture, checked to m = 13, n = 1000);
         A092482 formulas (conjecture checked to
         n = 512)

CLAIM
  A093682: array T(m,n), each row a greedy
  no-3-term-AP sequence variant with claimed closed
  form
    T(m,n) = sum_{k=1..n-1} (3^v2(k) + 1)/2 + f_m(n)
  where v2 = A007814 = 2-adic valuation and f_m is
  eventually periodic with period P <=
  2^floor((m+3)/2). A092482 (greedy no-3AP from
  1,2,3): for n > 2,
    a(n+2) = 1 + A053644(n) + A005836(n)
  (A053644 = highest power of 2 <= n; A005836 =
  base-3 digits in {0,1} numbers).

LEAN
  Nat.digits, padicValNat (v2), and the greedy-def
  machinery shared with A003278-stanley-digits. Same
  file-family; build after that one.

ROUTE
  Same digit-induction toolkit as A003278; the
  periodic-residual claim needs a finite-state
  argument per row — plausibly provable row-by-row
  for small m (each row is a self-contained bounded
  claim), general m harder. Sze's proof for rows 0-2
  is the literature anchor to consult.

EVIDENCE
  Checked to m = 13, n = 1000 (A093682) and n = 512
  (A092482) per entries.
