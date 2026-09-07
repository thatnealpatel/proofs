seq:     A267632
claim:   palindrome-rows
status:  PROVED: odd rows and power-of-two rows
stmt:    S
proof:   S (both cases; elementary subset bijections)
module:  Proofs/Enumerative/PalindromeRows.lean (Enumerative.PalindromeRows)
helper:  Proofs/Enumerative/PalindromeRowsBijection.lean
         (Enumerative.PalindromeRowsBijection)
source:  OEIS A267632 comment, unattributed
         (originally labelled "observation-conjecture")

FORMALIZED
  A267632.T_symm_of_odd : Odd n → k ≤ n → T n k = T n (n - k).
  A267632.T_symm_of_two_pow (j : ℕ) {k : ℕ} :
    1 ≤ k → k < 2^j → T (2^j) k = T (2^j) (2^j - k).
  The existing definitions and theorem signature are unchanged.
  Rows 1–8 and sharpness controls at rows 6, 10, 12 remain kernel-checked.
  The earlier literature note (2026-07-29) regarded this as LIKELY-KNOWN
  from Ramanathan 1944 / Barnes 1959; neither formula is needed for this proof.

CLAIM AND EXACT INDEXING
  T(n,k) counts k-element subsets of {1,...,n} whose sum is divisible by n.
  The truncated row (T(n,1),...,T(n,n-1)) is palindromic for odd n or n = 2^j.

  The project encodes the labels by i+1 for i ∈ Finset.range n:
    rowSubsets n k := (Finset.powersetCard k (Finset.range n)).filter
      (fun S => n ∣ S.sum (· + 1))
    T n k := (rowSubsets n k).card
  IMPORTANT: the previous card incorrectly displayed S.sum id. The shifted
  predicate is the actual definition; it is not replaced or assumed equivalent
  to the unshifted predicate on the same S.

STANDALONE BIJECTION CHECKPOINT
  The helper imports only Mathlib, not PalindromeRows or its target theorem.
  All names below are under A267632.PalindromeBijection.

  shiftedResidueSet n S reduces i ∈ S modulo n, then translates by 1.
  Thus it sends the actual label i+1 to its residue; the label n represents 0.
  shiftedResidueValues first translates by -1, then takes canonical values.
  Both round trips, preservation of cardinality, and
    sum(shiftedResidueSet n S) = 0 ↔ n ∣ ∑ i ∈ S, (i+1)
  are proved for S ⊆ range n and n ≠ 0. In particular n = 1 is included.

  gcd_dvd_half_two_pow proves, for 0 < j and 0 < k < 2^j,
    gcd(k,2^j) ∣ 2^j / 2.
  exists_mul_eq_half_two_pow constructs via integer Bezout a residue t with
    (k : ZMod (2^j)) * t = ((2^j / 2 : ℕ) : ZMod (2^j)).
  The proof internally uses the equivalent 2^(j-1) form.

  sum_univ_zmod_two_pow proves that the total residue sum is 2^(j-1).
  complementTranslate t S := translateSet t (univ \ S).
  Its sum for a size-k zero-sum S is
    n/2 + (n-k)*t = n/2 - k*t = 0.
  Its cardinality is n-k. The inverse is complementTranslate (-t), with the
  SAME chosen t, not an independent solution for n-k. Both inverse identities
  are proved on every finite subset. complementTranslateEquiv packages the
  restricted equivalence of the two zero-sum families.

  shifted_row_card_eq_zeroSumSubsets proves the exact filtered-power-set card
  bridge for every nonzero n and every k, with no endpoint restrictions.
  shifted_row_card_symm_two_pow closes the literal shifted filter-card target.
  This standalone module compiled before the original residual was connected.
  T_symm_of_two_pow then unfolds only T and rowSubsets and applies that checkpoint.
  No character sums or Fourier/Gauss-sum formula are used.

BOUNDARIES AND NONVACUITY
  The hypotheses are jointly satisfied at j=3, k=2 and j=3, k=6; concrete
  bijection and representation tests also include n=4, k=1 and n=1.
  At j=0, n=1: there are no indices with 1 ≤ k < n. This is checked explicitly;
  T_one_endpoints proves T 1 0 = T 1 1 = 1, and the residue bridge still applies.
  T_zero proves T n 0 = 1 for every n.
  T_two_pow_self_eq_zero proves T (2^j) (2^j) = 0 for every 0 < j.
  Thus both endpoint exclusions are necessary at positive exponents.
  T_eq_zero_of_lt proves T n k = 0 whenever n < k.
  n=0 is never a power-of-two modulus and is excluded from finite residue
  constructions; the original totalized definition has T 0 0=1, T 0 1=0.

VALIDATION
  Focused standalone build:
    flock .lake/agent.lock lake build Enumerative.PalindromeRowsBijection
  Focused final build:
    flock .lake/agent.lock lake build Enumerative.PalindromeRows
  Both compile without placeholders or forbidden trust mechanisms.
  #print axioms on complementTranslateEquiv, shifted_row_card_symm_two_pow,
  T_symm_of_two_pow, and T_two_pow_self_eq_zero reports exactly
    [propext, Classical.choice, Quot.sound].
  Ground computations use rfl/decide, never native_decide.
  References are untouched. The harness, not the proof worker, finalizes the
  jj revision; the exact review revision belongs in the campaign handoff.
