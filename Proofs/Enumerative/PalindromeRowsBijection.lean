import Mathlib

set_option autoImplicit false

/-!
# Standalone elementary bijection for A267632 power-of-two rows

This module does not import `PalindromeRows` or its target theorem. Its last theorem
uses exactly the filtered power set in that file: `S ⊆ range n`, with cardinality `k`
and `n ∣ ∑ i ∈ S, (i + 1)`. In particular, replacing the shifted sum by `∑ i ∈ S, i`
without also translating the residue representatives would change the objects.

The labels `1,...,n` are identified with `ZMod n` by `i ↦ i+1` for `i ∈ range n`;
the label `n` represents zero. For `n = 2^j`, `j > 0`, the sum of all residues is
`n/2`. Since `gcd(k,n) ∣ n/2` for `0 < k < n`, Bezout supplies one `t` with
`k*t = n/2`. The forward map is complement followed by translation by `t`. The
inverse uses this SAME `t`, complementing and then translating by `-t`.

The residue bridge works also for `n = 1`, for every `k`. The internal truncated-row
symmetry at `j = 0` has no indices; its two endpoint counts are separately checked.
No Fourier analysis, character sums, or computation axioms are used.
-/

open Finset

namespace A267632.PalindromeBijection

/-- Translation of a finite subset by `t`, using the standard additive-group permutation. -/
def translateSet {G : Type*} [AddCommGroup G] [DecidableEq G]
    (t : G) (S : Finset G) : Finset G :=
  S.map (Equiv.addRight t).toEmbedding

example : translateSet (1 : ZMod 4) {0, 3} = {0, 1} := by decide

/-- Membership in a translated subset is membership after subtracting the translation. -/
lemma mem_translateSet {G : Type*} [AddCommGroup G] [DecidableEq G]
    {t x : G} {S : Finset G} : x ∈ translateSet t S ↔ x - t ∈ S := by
  simp only [translateSet, mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change y + t - t ∈ S
    simpa only [add_sub_cancel_right] using hy
  · intro hx
    refine ⟨x - t, hx, ?_⟩
    change x - t + t = x
    exact sub_add_cancel x t

/-- Translation preserves the cardinality of a finite subset. -/
lemma card_translateSet {G : Type*} [AddCommGroup G] [DecidableEq G]
    (t : G) (S : Finset G) : (translateSet t S).card = S.card := by
  simp [translateSet]

/-- Translating a subset adds its cardinality times the translation to its sum. -/
lemma sum_translateSet {G : Type*} [AddCommGroup G] [DecidableEq G]
    (t : G) (S : Finset G) :
    ∑ x ∈ translateSet t S, x = (∑ x ∈ S, x) + S.card • t := by
  rw [translateSet, sum_map]
  change ∑ x ∈ S, (x + t) = _
  rw [sum_add_distrib]
  simp

/-- Successive translations add their translation parameters. -/
lemma translateSet_translateSet {G : Type*} [AddCommGroup G] [DecidableEq G]
    (a b : G) (S : Finset G) :
    translateSet a (translateSet b S) = translateSet (b + a) S := by
  ext x
  simp only [mem_translateSet]
  rw [sub_sub, add_comm]

/-- Translation by zero fixes every finite subset. -/
lemma translateSet_zero {G : Type*} [AddCommGroup G] [DecidableEq G] (S : Finset G) :
    translateSet 0 S = S := by
  ext x
  simp [mem_translateSet]

/-- Translation by `t` after complementing in the whole finite group. -/
def complementTranslate {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (t : G) (S : Finset G) : Finset G :=
  translateSet t (Finset.univ \ S)

example : complementTranslate (2 : ZMod 4) {0} = {0, 1, 3} := by decide

/-- Complement and translation by `-t` undo complement and translation by `t`. -/
lemma complementTranslate_neg_leftInverse
    {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] (t : G) (S : Finset G) :
    complementTranslate (-t) (complementTranslate t S) = S := by
  ext x
  simp only [complementTranslate, mem_translateSet, mem_sdiff, mem_univ, true_and]
  constructor
  · intro h
    by_contra hx
    apply h
    simpa only [sub_neg_eq_add, add_sub_cancel_right] using hx
  · intro hx hbad
    have hnot : x ∉ S := by
      simpa only [sub_neg_eq_add, add_sub_cancel_right] using hbad
    exact hnot hx

/-- The same two maps are inverses in the other order, with no new choice of translation. -/
lemma complementTranslate_neg_rightInverse
    {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] (t : G) (S : Finset G) :
    complementTranslate t (complementTranslate (-t) S) = S := by
  simpa only [neg_neg] using complementTranslate_neg_leftInverse (-t) S

/-- Canonical representatives in `range n` cover `ZMod n` when `n` is nonzero. -/
lemma univ_zmod_eq_image (n : ℕ) [NeZero n] :
    (Finset.univ : Finset (ZMod n)) = (Finset.range n).image (fun i : ℕ => (i : ZMod n)) := by
  ext x
  simp only [mem_univ, mem_image, true_iff]
  refine ⟨x.val, mem_range.mpr x.val_lt, ?_⟩
  exact ZMod.natCast_zmod_val x

/-- Reduction modulo `n` is injective on its canonical representatives. -/
lemma natCast_inj_on_range (n : ℕ) [NeZero n] {a b : ℕ}
    (ha : a ∈ Finset.range n) (hb : b ∈ Finset.range n)
    (h : (a : ZMod n) = (b : ZMod n)) : a = b := by
  have hva : (a : ZMod n).val = a := ZMod.val_natCast_of_lt (mem_range.mp ha)
  have hvb : (b : ZMod n).val = b := ZMod.val_natCast_of_lt (mem_range.mp hb)
  rw [← hva, h, hvb]

/-- The sum of all residues is the reduction of the integer sum `0 + ... + (n-1)`. -/
lemma sum_univ_zmod (n : ℕ) [NeZero n] :
    (∑ x : ZMod n, x) = ((n * (n - 1) / 2 : ℕ) : ZMod n) := by
  rw [univ_zmod_eq_image]
  rw [sum_image (fun a ha b hb h => natCast_inj_on_range n ha hb h)]
  rw [← Nat.cast_sum, Finset.sum_range_id]

/-- For a positive exponent, the sum of all residues modulo `2^j` is `2^(j-1)`. -/
lemma sum_univ_zmod_two_pow (j : ℕ) (hj : 0 < j) :
    (∑ x : ZMod (2 ^ j), x) = ((2 ^ (j - 1) : ℕ) : ZMod (2 ^ j)) := by
  letI : NeZero (2 ^ j) := ⟨Nat.ne_of_gt (Nat.two_pow_pos j)⟩
  rw [sum_univ_zmod]
  have hp : 2 ^ j = 2 * 2 ^ (j - 1) := by
    have hsum := Nat.two_pow_pred_add_two_pow_pred hj
    omega
  have harith : 2 ^ j * (2 ^ j - 1) / 2 = 2 ^ (j - 1) * (2 ^ j - 1) := by
    rw [hp]
    calc
      2 * 2 ^ (j - 1) * (2 * 2 ^ (j - 1) - 1) / 2 =
          2 * (2 ^ (j - 1) * (2 * 2 ^ (j - 1) - 1)) / 2 := by rw [Nat.mul_assoc]
      _ = 2 ^ (j - 1) * (2 * 2 ^ (j - 1) - 1) := Nat.mul_div_cancel_left _ (by norm_num)
  rw [harith]
  have hncast : ((2 ^ j : ℕ) : ZMod (2 ^ j)) = 0 := ZMod.natCast_self (2 ^ j)
  have hpred : (((2 ^ j : ℕ) - 1 : ℕ) : ZMod (2 ^ j)) = -1 := by
    have hnpos : 1 ≤ 2 ^ j := Nat.two_pow_pos j
    rw [Nat.cast_sub hnpos, hncast]
    ring
  rw [Nat.cast_mul, hpred]
  have htwo : (2 : ZMod (2 ^ j)) * ((2 ^ (j - 1) : ℕ) : ZMod (2 ^ j)) = 0 := by
    calc
      (2 : ZMod (2 ^ j)) * ((2 ^ (j - 1) : ℕ) : ZMod (2 ^ j)) =
          ((2 * 2 ^ (j - 1) : ℕ) : ZMod (2 ^ j)) := by rw [Nat.cast_mul]; norm_num
      _ = ((2 ^ j : ℕ) : ZMod (2 ^ j)) := by rw [hp]
      _ = 0 := hncast
  have hselfneg : -((2 ^ (j - 1) : ℕ) : ZMod (2 ^ j)) =
      ((2 ^ (j - 1) : ℕ) : ZMod (2 ^ j)) := by
    apply neg_eq_iff_add_eq_zero.mpr
    simpa only [two_mul] using htwo
  rw [mul_neg_one, hselfneg]

/-- An interior index has gcd with `2^j` dividing the preceding power of two. -/
lemma gcd_dvd_pred_two_pow {j k : ℕ} (hj : 0 < j) (hk0 : 0 < k) (hk : k < 2 ^ j) :
    Nat.gcd k (2 ^ j) ∣ 2 ^ (j - 1) := by
  have hdvd : Nat.gcd k (2 ^ j) ∣ 2 ^ j := Nat.gcd_dvd_right k (2 ^ j)
  obtain ⟨a, haj, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [ha]
  apply (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mpr
  by_contra hnot
  have hja : j ≤ a := by omega
  have hajeq : a = j := Nat.le_antisymm haj hja
  have hn_dvd_k : 2 ^ j ∣ k := by
    rw [← hajeq, ← ha]
    exact Nat.gcd_dvd_left k (2 ^ j)
  have hn_le_k : 2 ^ j ≤ k := Nat.le_of_dvd hk0 hn_dvd_k
  omega

/-- Equivalently, the gcd of an interior index and a power of two divides half the modulus. -/
lemma gcd_dvd_half_two_pow {j k : ℕ} (hj : 0 < j) (hk0 : 0 < k) (hk : k < 2 ^ j) :
    Nat.gcd k (2 ^ j) ∣ 2 ^ j / 2 := by
  rw [← Nat.pow_sub_one (by norm_num) (Nat.ne_of_gt hj)]
  exact gcd_dvd_pred_two_pow hj hk0 hk

/-- Bezout gives a translation taking `k` times the translation to `2^(j-1)` modulo `2^j`. -/
lemma exists_mul_eq_pred_two_pow {j k : ℕ} (hj : 0 < j) (hk0 : 0 < k)
    (hk : k < 2 ^ j) :
    ∃ t : ZMod (2 ^ j),
      (k : ZMod (2 ^ j)) * t = ((2 ^ (j - 1) : ℕ) : ZMod (2 ^ j)) := by
  obtain ⟨q, hq⟩ := gcd_dvd_pred_two_pow hj hk0 hk
  let t : ZMod (2 ^ j) := ((q : ℤ) * Nat.gcdA k (2 ^ j) : ℤ)
  refine ⟨t, ?_⟩
  have hbez := Nat.gcd_eq_gcd_ab (x := k) (y := 2 ^ j)
  dsimp [t]
  rw [show (k : ZMod (2 ^ j)) = ((k : ℤ) : ZMod (2 ^ j)) by norm_num]
  have hcastn : (((2 ^ j : ℕ) : ℤ) : ZMod (2 ^ j)) = 0 := by
    rw [Int.cast_natCast]
    exact ZMod.natCast_self (2 ^ j)
  have hqcast : ((2 ^ (j - 1) : ℕ) : ZMod (2 ^ j)) =
      ((Nat.gcd k (2 ^ j) : ℕ) : ZMod (2 ^ j)) * (q : ZMod (2 ^ j)) := by
    simpa only [Nat.cast_mul] using congrArg (fun x : ℕ => (x : ZMod (2 ^ j))) hq
  have hbezcast : ((Nat.gcd k (2 ^ j) : ℕ) : ZMod (2 ^ j)) =
      ((k : ℤ) : ZMod (2 ^ j)) * (Nat.gcdA k (2 ^ j) : ZMod (2 ^ j)) +
        (((2 ^ j : ℕ) : ℤ) : ZMod (2 ^ j)) * (Nat.gcdB k (2 ^ j) : ZMod (2 ^ j)) := by
    simpa only [Int.cast_natCast, Int.cast_add, Int.cast_mul] using
      congrArg (fun x : ℤ => (x : ZMod (2 ^ j))) hbez
  rw [hqcast, hbezcast, hcastn]
  simp only [Int.cast_mul, Int.cast_natCast, zero_mul, add_zero]
  ring

/-- The translation can equivalently be specified by `k*t = n/2` in `ZMod n`. -/
lemma exists_mul_eq_half_two_pow {j k : ℕ} (hj : 0 < j) (hk0 : 0 < k)
    (hk : k < 2 ^ j) :
    ∃ t : ZMod (2 ^ j), (k : ZMod (2 ^ j)) * t = ((2 ^ j / 2 : ℕ) : ZMod (2 ^ j)) := by
  rw [← Nat.pow_sub_one (by norm_num) (Nat.ne_of_gt hj)]
  exact exists_mul_eq_pred_two_pow hj hk0 hk

example : 0 < (3 : ℕ) ∧ 0 < (6 : ℕ) ∧ 6 < 2 ^ 3 := by norm_num
example : Nat.gcd 6 8 ∣ 8 / 2 := gcd_dvd_half_two_pow (j := 3) (by norm_num)
  (by norm_num) (by norm_num)
example : ∃ t : ZMod 8, (6 : ZMod 8) * t = 4 :=
  exists_mul_eq_pred_two_pow (j := 3) (k := 6) (by norm_num) (by norm_num) (by norm_num)

/-- The finite family of size-`k` subsets of `ZMod n` whose sum is zero; `n` must be nonzero. -/
def zeroSumSubsets (n k : ℕ) (hn : n ≠ 0) : Finset (Finset (ZMod n)) := by
  letI : NeZero n := ⟨hn⟩
  exact (Finset.univ.powersetCard k).filter (fun S => ∑ x ∈ S, x = 0)

/-- The zero-sum subset family for the always nonzero modulus `2^j`. -/
def powZeroSumSubsets (j k : ℕ) : Finset (Finset (ZMod (2 ^ j))) :=
  zeroSumSubsets (2 ^ j) k (pow_ne_zero j (by norm_num))

example : (zeroSumSubsets 4 2 (by decide)).card = 1 := by decide
example : (powZeroSumSubsets 2 2).card = 1 := by decide

/-- Membership in the zero-sum family means precisely the given cardinality and zero sum. -/
lemma mem_zeroSumSubsets {n k : ℕ} {hn : n ≠ 0} {S : Finset (ZMod n)} :
    S ∈ zeroSumSubsets n k hn ↔ S.card = k ∧ ∑ x ∈ S, x = 0 := by
  letI : NeZero n := ⟨hn⟩
  simp [zeroSumSubsets]

/-- Membership in the power-of-two zero-sum family, in cardinality-and-sum form. -/
lemma mem_powZeroSumSubsets {j k : ℕ} {S : Finset (ZMod (2 ^ j))} :
    S ∈ powZeroSumSubsets j k ↔ S.card = k ∧ ∑ x ∈ S, x = 0 := by
  simp only [powZeroSumSubsets, mem_zeroSumSubsets]

/-- Complementing and translating by the chosen `t` sends size `k` zero-sum sets to size `n-k`. -/
lemma complementTranslate_mem {j k : ℕ} (hj : 0 < j)
    (hk : k < 2 ^ j) {t : ZMod (2 ^ j)}
    (ht : (k : ZMod (2 ^ j)) * t = ((2 ^ (j - 1) : ℕ) : ZMod (2 ^ j)))
    {S : Finset (ZMod (2 ^ j))} (hS : S ∈ powZeroSumSubsets j k) :
    complementTranslate t S ∈ powZeroSumSubsets j (2 ^ j - k) := by
  letI : NeZero (2 ^ j) := ⟨Nat.ne_of_gt (Nat.two_pow_pos j)⟩
  obtain ⟨hcard, hsum⟩ := mem_powZeroSumSubsets.mp hS
  apply mem_powZeroSumSubsets.mpr
  constructor
  · rw [complementTranslate, card_translateSet, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, ZMod.card, hcard]
  · rw [complementTranslate, sum_translateSet]
    have hcompl : (∑ x ∈ Finset.univ \ S, x) =
        ((2 ^ (j - 1) : ℕ) : ZMod (2 ^ j)) := by
      have hsplit := Finset.sum_sdiff (Finset.subset_univ S) (f := fun x : ZMod (2 ^ j) => x)
      rw [hsum, add_zero, sum_univ_zmod_two_pow j hj] at hsplit
      exact hsplit
    rw [hcompl]
    have hcardcompl : (Finset.univ \ S).card = 2 ^ j - k := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, ZMod.card, hcard]
    rw [hcardcompl]
    simp only [nsmul_eq_mul]
    rw [Nat.cast_sub hk.le, ZMod.natCast_self, zero_sub, neg_mul, ht]
    ring

/-- The inverse map uses the same translation parameter negated, not an independently chosen one. -/
lemma complementTranslate_neg_mem {j k : ℕ} (hj : 0 < j) (hk0 : 0 < k)
    (hk : k < 2 ^ j) {t : ZMod (2 ^ j)}
    (ht : (k : ZMod (2 ^ j)) * t = ((2 ^ (j - 1) : ℕ) : ZMod (2 ^ j)))
    {S : Finset (ZMod (2 ^ j))} (hS : S ∈ powZeroSumSubsets j (2 ^ j - k)) :
    complementTranslate (-t) S ∈ powZeroSumSubsets j k := by
  have hpos : 0 < 2 ^ j - k := Nat.sub_pos_of_lt hk
  have hlt : 2 ^ j - k < 2 ^ j := Nat.sub_lt (Nat.two_pow_pos j) hk0
  have hhalfneg : ((2 ^ j - k : ℕ) : ZMod (2 ^ j)) * (-t) =
      ((2 ^ (j - 1) : ℕ) : ZMod (2 ^ j)) := by
    rw [Nat.cast_sub hk.le, ZMod.natCast_self, zero_sub]
    calc
      -((k : ZMod (2 ^ j))) * -t = (k : ZMod (2 ^ j)) * t := by ring
      _ = ((2 ^ (j - 1) : ℕ) : ZMod (2 ^ j)) := ht
  have himage := complementTranslate_mem hj hlt hhalfneg hS
  rwa [Nat.sub_sub_self hk.le] at himage

/-- Explicit equivalence of the complementary-size zero-sum families for a single chosen `t`. -/
def complementTranslateEquiv (j k : ℕ) (hj : 0 < j) (hk0 : 0 < k)
    (hk : k < 2 ^ j) (t : ZMod (2 ^ j))
    (ht : (k : ZMod (2 ^ j)) * t = ((2 ^ (j - 1) : ℕ) : ZMod (2 ^ j))) :
    {S // S ∈ powZeroSumSubsets j k} ≃ {S // S ∈ powZeroSumSubsets j (2 ^ j - k)} where
  toFun S := ⟨complementTranslate t S.val, complementTranslate_mem hj hk ht S.property⟩
  invFun S := ⟨complementTranslate (-t) S.val, complementTranslate_neg_mem hj hk0 hk ht S.property⟩
  left_inv S := Subtype.ext (complementTranslate_neg_leftInverse t S.val)
  right_inv S := Subtype.ext (complementTranslate_neg_rightInverse t S.val)

example : (complementTranslateEquiv 2 1 (by norm_num) (by norm_num) (by norm_num)
    2 (by decide) ⟨{0}, by decide⟩).val = {0, 1, 3} := by decide

/-- Complement and translation yield equal cardinalities of complementary-size zero-sum families. -/
theorem zeroSumSubsets_card_symm_two_pow (j : ℕ) {k : ℕ} (hj : 0 < j)
    (hk0 : 0 < k) (hk : k < 2 ^ j) :
    (powZeroSumSubsets j k).card = (powZeroSumSubsets j (2 ^ j - k)).card := by
  obtain ⟨t, ht⟩ := exists_mul_eq_pred_two_pow hj hk0 hk
  refine Finset.card_bij' (fun S _ => complementTranslate t S)
    (fun S _ => complementTranslate (-t) S)
    (fun _ hS => complementTranslate_mem hj hk ht hS)
    (fun _ hS => complementTranslate_neg_mem hj hk0 hk ht hS)
    (fun S _ => complementTranslate_neg_leftInverse t S)
    (fun S _ => complementTranslate_neg_rightInverse t S)

/-- Reduce a finite set of natural representatives modulo `n`. -/
def residueSet (n : ℕ) (S : Finset ℕ) : Finset (ZMod n) :=
  S.image (fun i : ℕ => (i : ZMod n))

/-- Take the canonical natural representatives of a set of residues. -/
def residueValues {n : ℕ} (A : Finset (ZMod n)) : Finset ℕ :=
  A.image ZMod.val

example : residueSet 4 {0, 3} = {0, 3} := by decide
example : residueValues ({0, 3} : Finset (ZMod 4)) = {0, 3} := by decide

/-- Reducing and taking values fixes subsets of `range n`. -/
lemma residueValues_residueSet {n : ℕ} [NeZero n] {S : Finset ℕ}
    (hS : S ⊆ Finset.range n) : residueValues (residueSet n S) = S := by
  ext i
  simp only [residueValues, residueSet, mem_image]
  constructor
  · rintro ⟨x, ⟨a, ha, rfl⟩, hxi⟩
    have hlt : a < n := mem_range.mp (hS ha)
    rw [ZMod.val_natCast_of_lt hlt] at hxi
    rwa [← hxi]
  · intro hi
    refine ⟨(i : ZMod n), ⟨i, hi, rfl⟩, ?_⟩
    exact ZMod.val_natCast_of_lt (mem_range.mp (hS hi))

/-- Taking values and reducing fixes every subset of a nonzero residue ring. -/
lemma residueSet_residueValues {n : ℕ} [NeZero n] (A : Finset (ZMod n)) :
    residueSet n (residueValues A) = A := by
  ext x
  simp only [residueSet, residueValues, mem_image]
  constructor
  · rintro ⟨i, ⟨y, hy, rfl⟩, hix⟩
    rw [ZMod.natCast_zmod_val] at hix
    rwa [← hix]
  · intro hx
    refine ⟨x.val, ⟨x, hx, rfl⟩, ?_⟩
    exact ZMod.natCast_zmod_val x

/-- Reduction preserves cardinality on subsets of canonical representatives. -/
lemma card_residueSet {n : ℕ} [NeZero n] {S : Finset ℕ}
    (hS : S ⊆ Finset.range n) : (residueSet n S).card = S.card := by
  apply Finset.card_image_iff.mpr
  intro a ha b hb hab
  exact natCast_inj_on_range n (hS ha) (hS hb) hab

/-- The sum of a reduced subset is the reduction of its natural-number sum. -/
lemma sum_residueSet {n : ℕ} [NeZero n] {S : Finset ℕ}
    (hS : S ⊆ Finset.range n) :
    (∑ x ∈ residueSet n S, x) = ((∑ i ∈ S, i : ℕ) : ZMod n) := by
  rw [residueSet, Finset.sum_image]
  · rw [Nat.cast_sum]
  · intro a ha b hb hab
    exact natCast_inj_on_range n (hS ha) (hS hb) hab

/-- The exact `{1,...,n}` encoding used by `rowSubsets`: reduce `i`, then translate by one. -/
def shiftedResidueSet (n : ℕ) (S : Finset ℕ) : Finset (ZMod n) :=
  translateSet 1 (residueSet n S)

/-- Inverse of `shiftedResidueSet`: translate by `-1`, then take canonical representatives. -/
def shiftedResidueValues {n : ℕ} [NeZero n] (A : Finset (ZMod n)) : Finset ℕ :=
  residueValues (translateSet (-1) A)

example : shiftedResidueSet 4 {0, 3} = {0, 1} := by decide
example : shiftedResidueValues ({0, 1} : Finset (ZMod 4)) = {0, 3} := by decide
example : shiftedResidueSet 1 {0} = {0} := by decide
example : shiftedResidueValues ({0} : Finset (ZMod 1)) = {0} := by decide

/-- The shifted residue map has a left inverse on the project's encoded subsets. -/
lemma shiftedResidueValues_shiftedResidueSet {n : ℕ} [NeZero n] {S : Finset ℕ}
    (hS : S ⊆ Finset.range n) : shiftedResidueValues (shiftedResidueSet n S) = S := by
  rw [shiftedResidueValues, shiftedResidueSet, translateSet_translateSet,
    add_neg_cancel, translateSet_zero]
  exact residueValues_residueSet hS

/-- The shifted residue map has a right inverse on all residue subsets. -/
lemma shiftedResidueSet_shiftedResidueValues {n : ℕ} [NeZero n] (A : Finset (ZMod n)) :
    shiftedResidueSet n (shiftedResidueValues A) = A := by
  rw [shiftedResidueSet, shiftedResidueValues, residueSet_residueValues,
    translateSet_translateSet, neg_add_cancel, translateSet_zero]

/-- Inverse shifted representatives always lie in the project's `range n` universe. -/
lemma shiftedResidueValues_subset_range {n : ℕ} [NeZero n] (A : Finset (ZMod n)) :
    shiftedResidueValues A ⊆ Finset.range n := by
  intro i hi
  rw [shiftedResidueValues] at hi
  simp only [residueValues, mem_image] at hi
  obtain ⟨x, hx, rfl⟩ := hi
  exact mem_range.mpr x.val_lt

/-- The shifted residue map preserves the number of labels selected. -/
lemma card_shiftedResidueSet {n : ℕ} [NeZero n] {S : Finset ℕ}
    (hS : S ⊆ Finset.range n) : (shiftedResidueSet n S).card = S.card := by
  rw [shiftedResidueSet, card_translateSet, card_residueSet hS]

/-- The residue sum is the reduction of the exact shifted sum in `rowSubsets`. -/
lemma sum_shiftedResidueSet {n : ℕ} [NeZero n] {S : Finset ℕ}
    (hS : S ⊆ Finset.range n) :
    (∑ x ∈ shiftedResidueSet n S, x) = ((∑ i ∈ S, (i + 1) : ℕ) : ZMod n) := by
  rw [shiftedResidueSet, sum_translateSet, sum_residueSet hS, card_residueSet hS]
  simp only [nsmul_eq_mul, mul_one]
  rw [Finset.sum_add_distrib, Nat.cast_add, Nat.cast_sum]
  simp

/-- Zero residue sum is equivalent to divisibility of the original shifted natural sum. -/
lemma shiftedResidueSet_sum_zero_iff {n : ℕ} [NeZero n] {S : Finset ℕ}
    (hS : S ⊆ Finset.range n) :
    (∑ x ∈ shiftedResidueSet n S, x) = 0 ↔ n ∣ ∑ i ∈ S, (i + 1) := by
  rw [sum_shiftedResidueSet hS, ZMod.natCast_eq_zero_iff]

/-- Reducing shifted labels bijects the exact filtered power set of A267632 with zero-sum
residue subsets, for every nonzero modulus and every cardinality, including endpoints. -/
theorem shifted_row_card_eq_zeroSumSubsets (n k : ℕ) (hn : n ≠ 0) :
    (((Finset.range n).powersetCard k).filter (fun S => n ∣ S.sum (· + 1))).card =
      (zeroSumSubsets n k hn).card := by
  letI : NeZero n := ⟨hn⟩
  have hmem {S : Finset ℕ} :
      S ∈ ((Finset.range n).powersetCard k).filter (fun S => n ∣ S.sum (· + 1)) ↔
        S ⊆ Finset.range n ∧ S.card = k ∧ n ∣ S.sum (· + 1) := by
    simp only [Finset.mem_filter, Finset.mem_powersetCard, and_assoc]
  refine Finset.card_bij' (fun S _ => shiftedResidueSet n S)
    (fun A _ => shiftedResidueValues A) ?_ ?_ ?_ ?_
  · intro S hS
    obtain ⟨hsub, hcard, hdvd⟩ := hmem.mp hS
    exact mem_zeroSumSubsets.mpr
      ⟨(card_shiftedResidueSet hsub).trans hcard,
        (shiftedResidueSet_sum_zero_iff hsub).mpr hdvd⟩
  · intro A hA
    obtain ⟨hcard, hsum⟩ := mem_zeroSumSubsets.mp hA
    have hsub := shiftedResidueValues_subset_range A
    have hround := shiftedResidueSet_shiftedResidueValues A
    apply hmem.mpr
    refine ⟨hsub, ?_, ?_⟩
    · rw [← card_shiftedResidueSet hsub, hround, hcard]
    · apply (shiftedResidueSet_sum_zero_iff hsub).mp
      rwa [hround]
  · intro S hS
    exact shiftedResidueValues_shiftedResidueSet (hmem.mp hS).1
  · intro A hA
    exact shiftedResidueSet_shiftedResidueValues A

/-- Independently compiling card checkpoint for the exact shifted subset predicate, without `T`.
The two bijections above give symmetry by conjugating complement/translation through residues. -/
theorem shifted_row_card_symm_two_pow (j : ℕ) {k : ℕ} (hk0 : 0 < k)
    (hk : k < 2 ^ j) :
    (((Finset.range (2 ^ j)).powersetCard k).filter
      (fun S => 2 ^ j ∣ S.sum (· + 1))).card =
    (((Finset.range (2 ^ j)).powersetCard (2 ^ j - k)).filter
      (fun S => 2 ^ j ∣ S.sum (· + 1))).card := by
  have hj : 0 < j := by
    by_contra h
    have hj0 : j = 0 := by omega
    simp only [hj0, pow_zero] at hk
    omega
  have hn : 2 ^ j ≠ 0 := pow_ne_zero j (by norm_num)
  rw [shifted_row_card_eq_zeroSumSubsets _ _ hn, shifted_row_card_eq_zeroSumSubsets _ _ hn]
  exact zeroSumSubsets_card_symm_two_pow j hj hk0 hk

example : (zeroSumSubsets 1 0 (by decide)).card = 1 := by decide
example : (zeroSumSubsets 1 1 (by decide)).card = 1 := by decide
example : (zeroSumSubsets 1 2 (by decide)).card = 0 := by decide
example : (zeroSumSubsets 4 0 (by decide)).card = 1 := by decide
example : (zeroSumSubsets 4 4 (by decide)).card = 0 := by decide
example : 0 < (2 : ℕ) ∧ 2 < 2 ^ 3 := by norm_num

#print axioms complementTranslateEquiv
#print axioms shifted_row_card_symm_two_pow

end A267632.PalindromeBijection
