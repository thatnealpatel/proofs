import Enumerative.HegartyPermutation

/-!
# Hegarty's three-eighths bound for OEIS A094870

This file formalizes Theorem 3.3 of Peter Hegarty, *Permutations avoiding arithmetic
patterns*, Electronic Journal of Combinatorics 11 (2004), R39.

The source uses one-based indices and proves `3 * N ≤ 8 * πg N`.  The definition imported
from `HegartyPermutation` is zero-indexed, with `A094870.a n = πg (n + 1)`.  Thus the exact
contract here is `3 * (n + 1) ≤ 8 * A094870.a n`.

There is a minor parity typo in the published counting argument.  On page 7, after (6),
the values excluded from `Y ∪ Z` below `n/2` must have parity *opposite* to `n`: values in
`Y` exceed `n/2`, while all values in `Z` have the same parity as `n`.  The printed word
“same” cannot imply the asserted estimate.  The proof below uses the corrected statement.
-/

set_option autoImplicit false

namespace A094870

/-- Among the positions `0, …, K - 1`, at most `(K + 1) / 2` have the same
parity as a fixed natural number `r`. -/
theorem card_filter_range_mod_two_eq_le (K r : ℕ) :
    ((Finset.range K).filter (fun e => e % 2 = r % 2)).card ≤ (K + 1) / 2 := by
  have hmaps : Set.MapsTo (fun e => e / 2)
      ↑((Finset.range K).filter (fun e => e % 2 = r % 2))
      ↑(Finset.range ((K + 1) / 2)) := by
    intro e he
    have heK : e < K := Finset.mem_range.mp (Finset.mem_filter.mp he).1
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  have hinj : Set.InjOn (fun e => e / 2)
      ↑((Finset.range K).filter (fun e => e % 2 = r % 2)) := by
    intro e he f hf heq
    have hepar : e % 2 = r % 2 := (Finset.mem_filter.mp he).2
    have hfpar : f % 2 = r % 2 := (Finset.mem_filter.mp hf).2
    change e / 2 = f / 2 at heq
    calc
      e = e % 2 + 2 * (e / 2) := (Nat.mod_add_div e 2).symm
      _ = f % 2 + 2 * (f / 2) := by rw [hepar, hfpar, heq]
      _ = f := Nat.mod_add_div f 2
  have hcard := Finset.card_le_card_of_injOn (fun e => e / 2) hmaps hinj
  simpa only [Finset.card_range] using hcard

private theorem card_pos_even_le (S : Finset ℕ) (T : ℕ)
    (hpos : ∀ w ∈ S, 1 ≤ w) (hle : ∀ w ∈ S, w ≤ T)
    (hpar : ∀ w ∈ S, w % 2 = 0) : S.card ≤ T / 2 := by
  have hmaps : Set.MapsTo (fun w => w / 2 - 1) ↑S ↑(Finset.range (T / 2)) := by
    intro w hw
    have hwpos := hpos w hw
    have hwle := hle w hw
    have hwpar := hpar w hw
    have hwdiv := Nat.mod_add_div w 2
    have hTdiv := Nat.mod_add_div T 2
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  have hinj : Set.InjOn (fun w => w / 2 - 1) ↑S := by
    intro x hx y hy heq
    have hxpos := hpos x hx
    have hypos := hpos y hy
    have hxpar := hpar x hx
    have hypar := hpar y hy
    have hxdiv := Nat.mod_add_div x 2
    have hydiv := Nat.mod_add_div y 2
    change x / 2 - 1 = y / 2 - 1 at heq
    have hxqpos : 1 ≤ x / 2 := by omega
    have hyqpos : 1 ≤ y / 2 := by omega
    have hq : x / 2 = y / 2 := by omega
    omega
  simpa only [Finset.card_range] using
    (Finset.card_le_card_of_injOn (fun w => w / 2 - 1) hmaps hinj)

private theorem card_pos_odd_le (S : Finset ℕ) (T : ℕ)
    (hle : ∀ w ∈ S, w ≤ T) (hpar : ∀ w ∈ S, w % 2 = 1) :
    S.card ≤ (T + 1) / 2 := by
  have hmaps : Set.MapsTo (fun w => w / 2) ↑S ↑(Finset.range ((T + 1) / 2)) := by
    intro w hw
    have hwle := hle w hw
    have hwpar := hpar w hw
    have hwdiv := Nat.mod_add_div w 2
    have hTdiv := Nat.mod_add_div T 2
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  have hinj : Set.InjOn (fun w => w / 2) ↑S := by
    intro x hx y hy heq
    have hxpar := hpar x hx
    have hypar := hpar y hy
    change x / 2 = y / 2 at heq
    calc
      x = x % 2 + 2 * (x / 2) := (Nat.mod_add_div x 2).symm
      _ = y % 2 + 2 * (y / 2) := by rw [hxpar, hypar, heq]
      _ = y := Nat.mod_add_div y 2
  simpa only [Finset.card_range] using
    (Finset.card_le_card_of_injOn (fun w => w / 2) hmaps hinj)

private theorem blockIdx_spec {c p : ℕ} (hc : 1 ≤ c)
    (hunseen : ∀ k < p, a k ≠ c) (hlt : c < a p) :
    1 ≤ blockIdx c p ∧ 2 * blockIdx c p ≤ p ∧
      c + a (p - 2 * blockIdx c p) = 2 * a (p - blockIdx c p) := by
  have hnc : ¬ IsCand p c := not_isCand_of_lt hlt
  have hex : Set.Nonempty
      {i | 1 ≤ i ∧ 2 * i ≤ p ∧ c + a (p - 2 * i) = 2 * a (p - i)} := by
    by_contra hno
    rw [Set.not_nonempty_iff_eq_empty] at hno
    refine hnc ⟨hc, hunseen, ?_⟩
    intro i hi hip heq
    have hmem : i ∈ {i | 1 ≤ i ∧ 2 * i ≤ p ∧
        c + a (p - 2 * i) = 2 * a (p - i)} := ⟨hi, hip, heq⟩
    rw [hno] at hmem
    exact hmem
  exact Nat.sInf_mem hex

private theorem first_block_right_injOn {v K : ℕ}
    {X : Finset ℕ} (hv : 1 ≤ v) (hX : ∀ p ∈ X, p < K ∧ v < a p)
    (hunseen : ∀ k, k < K → a k ≠ v) :
    Set.InjOn (fun p => a (p - 2 * blockIdx v p)) ↑X := by
  intro p hp q hq heq
  obtain ⟨hpK, hpv⟩ := hX p hp
  obtain ⟨hqK, hqv⟩ := hX q hq
  obtain ⟨hs1, hs2, hs3⟩ := blockIdx_spec hv (fun k hk => hunseen k (by omega)) hpv
  obtain ⟨ht1, ht2, ht3⟩ := blockIdx_spec hv (fun k hk => hunseen k (by omega)) hqv
  have hright : p - 2 * blockIdx v p = q - 2 * blockIdx v q := a_injective heq
  have htwomid : 2 * a (p - blockIdx v p) = 2 * a (q - blockIdx v q) := calc
    2 * a (p - blockIdx v p) = v + a (p - 2 * blockIdx v p) := hs3.symm
    _ = v + a (q - 2 * blockIdx v q) := congrArg (v + ·) heq
    _ = 2 * a (q - blockIdx v q) := ht3
  have hmidval : a (p - blockIdx v p) = a (q - blockIdx v q) := by omega
  have hmid : p - blockIdx v p = q - blockIdx v q := a_injective hmidval
  omega

private theorem first_block_mid_injOn {v K : ℕ}
    {X : Finset ℕ} (hv : 1 ≤ v) (hX : ∀ p ∈ X, p < K ∧ v < a p)
    (hunseen : ∀ k, k < K → a k ≠ v) :
    Set.InjOn (fun p => a (p - blockIdx v p)) ↑X := by
  intro p hp q hq heq
  obtain ⟨hpK, hpv⟩ := hX p hp
  obtain ⟨hqK, hqv⟩ := hX q hq
  obtain ⟨hs1, hs2, hs3⟩ := blockIdx_spec hv (fun k hk => hunseen k (by omega)) hpv
  obtain ⟨ht1, ht2, ht3⟩ := blockIdx_spec hv (fun k hk => hunseen k (by omega)) hqv
  have hmid : p - blockIdx v p = q - blockIdx v q := a_injective heq
  have htworight : 2 * a (p - blockIdx v p) = 2 * a (q - blockIdx v q) :=
    congrArg (2 * ·) heq
  have hrightsum : v + a (p - 2 * blockIdx v p) =
      v + a (q - 2 * blockIdx v q) := hs3.trans (htworight.trans ht3.symm)
  have hrightval : a (p - 2 * blockIdx v p) = a (q - 2 * blockIdx v q) := by omega
  have hright : p - 2 * blockIdx v p = q - 2 * blockIdx v q := a_injective hrightval
  omega

/-- **Hegarty, Theorem 3.3**, in the zero-indexing of `A094870.a`:
`3 * (n + 1) ≤ 8 * a n`.  Since `a n = πg(n+1)`, this is exactly the paper's
`3N/8 ≤ πg(N)` after clearing denominators. -/
theorem hegarty_three_eighths (n : ℕ) : 3 * (n + 1) ≤ 8 * a n := by
  let v := a n
  let K := 8 * v / 3
  have hv : 1 ≤ v := one_le_a n
  by_contra hbound
  have hKn : K ≤ n := by
    dsimp [K, v]
    omega
  have hunseen : ∀ p, p < K → a p ≠ v := by
    intro p hp heq
    have hpn : p < n := by omega
    exact a_ne_of_lt hpn heq
  let R := Finset.range K
  let X := R.filter (fun p => v < a p)
  have hX : ∀ p ∈ X, p < K ∧ v < a p := by
    intro p hp
    simpa only [X, R, Finset.mem_filter, Finset.mem_range] using hp
  have hblock : ∀ p ∈ X,
      1 ≤ blockIdx v p ∧ 2 * blockIdx v p ≤ p ∧
        v + a (p - 2 * blockIdx v p) = 2 * a (p - blockIdx v p) := by
    intro p hp
    obtain ⟨hpK, hpv⟩ := hX p hp
    exact blockIdx_spec hv (fun k hk => hunseen k (by omega)) hpv
  let L := R.filter (fun p => ¬ v < a p)
  have hLcard : L.card ≤ v - 1 := by
    have hmaps : Set.MapsTo a ↑L ↑(Finset.Ico 1 v) := by
      intro p hp
      have hp' : p ∈ L := hp
      have hpFilt := Finset.mem_filter.mp hp'
      have hpR : p ∈ R := hpFilt.1
      have hpv : ¬ v < a p := hpFilt.2
      have hpK : p < K := by
        exact Finset.mem_range.mp (show p ∈ Finset.range K by simpa only [R] using hpR)
      have hne := hunseen p hpK
      have hle : a p ≤ v := Nat.le_of_not_gt hpv
      have hlt : a p < v := lt_of_le_of_ne hle hne
      simpa only [Finset.coe_Ico, Set.mem_Ico] using
        (show 1 ≤ a p ∧ a p < v from ⟨one_le_a p, hlt⟩)
    have hc := Finset.card_le_card_of_injOn a hmaps a_injective.injOn
    rw [Nat.card_Ico] at hc
    omega
  have hXL : X.card + L.card = K := by
    simpa only [X, L, R, Finset.card_range] using
      (Finset.card_filter_add_card_filter_not (s := Finset.range K) (fun p => v < a p))
  have hXlarge : K - v + 1 ≤ X.card := by omega
  let Y := X.image (fun p => a (p - blockIdx v p))
  let Z := X.image (fun p => a (p - 2 * blockIdx v p))
  have hYcard : Y.card = X.card := by
    change (X.image (fun p => a (p - blockIdx v p))).card = X.card
    exact Finset.card_image_iff.mpr (first_block_mid_injOn hv hX hunseen)
  have hZcard : Z.card = X.card := by
    change (X.image (fun p => a (p - 2 * blockIdx v p))).card = X.card
    exact Finset.card_image_iff.mpr (first_block_right_injOn hv hX hunseen)
  have hYpos : ∀ y ∈ Y, v < 2 * y := by
    intro y hy
    change y ∈ X.image (fun p => a (p - blockIdx v p)) at hy
    rw [Finset.mem_image] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    have hs := hblock p hp
    have hz := one_le_a (p - 2 * blockIdx v p)
    omega
  have hZparity : ∀ z ∈ Z, z % 2 = v % 2 := by
    intro z hz
    change z ∈ X.image (fun p => a (p - 2 * blockIdx v p)) at hz
    rw [Finset.mem_image] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    have hs := hblock p hp
    omega
  have hYZsub : Y ∪ Z ⊆ (Finset.range K).image a := by
    intro w hw
    rw [Finset.mem_union] at hw
    rcases hw with hw | hw
    · change w ∈ X.image (fun p => a (p - blockIdx v p)) at hw
      rw [Finset.mem_image] at hw
      obtain ⟨p, hp, rfl⟩ := hw
      obtain ⟨hpK, hpv⟩ := hX p hp
      obtain ⟨hs1, hs2, hs3⟩ := hblock p hp
      exact Finset.mem_image.mpr ⟨p - blockIdx v p, Finset.mem_range.mpr (by omega), rfl⟩
    · change w ∈ X.image (fun p => a (p - 2 * blockIdx v p)) at hw
      rw [Finset.mem_image] at hw
      obtain ⟨p, hp, rfl⟩ := hw
      obtain ⟨hpK, hpv⟩ := hX p hp
      obtain ⟨hs1, hs2, hs3⟩ := hblock p hp
      exact Finset.mem_image.mpr ⟨p - 2 * blockIdx v p, Finset.mem_range.mpr (by omega), rfl⟩
  have hUnion : (Y ∪ Z).card ≤ K - v / 4 := by
    have hPcard : ((Finset.range K).image a).card = K := calc
      ((Finset.range K).image a).card = (Finset.range K).card :=
        Finset.card_image_iff.mpr a_injective.injOn
      _ = K := Finset.card_range K
    have htwoK : 2 * v ≤ K := by
      dsimp [K]
      omega
    by_cases hev : Even v
    · obtain ⟨r, hr⟩ := even_iff_exists_two_mul.mp hev
      let D := (Finset.range (v / 4)).image (fun k => 2 * k + 1)
      have hDcard : D.card = v / 4 := by
        change ((Finset.range (v / 4)).image (fun k => 2 * k + 1)).card = v / 4
        rw [Finset.card_image_of_injective]
        · exact Finset.card_range _
        · intro x y hxy
          apply Nat.mul_left_cancel (n := 2) (by omega)
          exact Nat.add_right_cancel hxy
      have hDsub : D ⊆ (Finset.range K).image a := by
        intro d hd
        change d ∈ (Finset.range (v / 4)).image (fun k => 2 * k + 1) at hd
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hd
        have hkv : k < v / 4 := Finset.mem_range.mp hk
        obtain ⟨p, hp, hap⟩ := thm_3_1 (v := 2 * k + 1) (by omega)
        exact Finset.mem_image.mpr ⟨p, Finset.mem_range.mpr (by omega), hap⟩
      have hDdis : Disjoint D (Y ∪ Z) := by
        rw [Finset.disjoint_left]
        intro d hd hdu
        change d ∈ (Finset.range (v / 4)).image (fun k => 2 * k + 1) at hd
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hd
        rcases Finset.mem_union.mp hdu with hY | hZ
        · have hy := hYpos (2 * k + 1) hY
          have hkv := Finset.mem_range.mp hk
          omega
        · have hzpar := hZparity (2 * k + 1) hZ
          have hvmod : v % 2 = 0 := Nat.even_iff.mp hev
          omega
      have hsub : (Y ∪ Z) ∪ D ⊆ (Finset.range K).image a := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact hYZsub hw
        · exact hDsub hw
      have hc := Finset.card_le_card hsub
      have hdis' : Disjoint (Y ∪ Z) D := hDdis.symm
      rw [Finset.card_union_of_disjoint hdis', hDcard, hPcard] at hc
      omega
    · have hvodd : v % 2 = 1 := Nat.not_even_iff.mp hev
      let D := (Finset.range (v / 4)).image (fun k => 2 * k + 2)
      have hDcard : D.card = v / 4 := by
        change ((Finset.range (v / 4)).image (fun k => 2 * k + 2)).card = v / 4
        rw [Finset.card_image_of_injective]
        · exact Finset.card_range _
        · intro x y hxy
          apply Nat.mul_left_cancel (n := 2) (by omega)
          exact Nat.add_right_cancel hxy
      have hDsub : D ⊆ (Finset.range K).image a := by
        intro d hd
        change d ∈ (Finset.range (v / 4)).image (fun k => 2 * k + 2) at hd
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hd
        have hkv : k < v / 4 := Finset.mem_range.mp hk
        obtain ⟨p, hp, hap⟩ := thm_3_1 (v := 2 * k + 2) (by omega)
        exact Finset.mem_image.mpr ⟨p, Finset.mem_range.mpr (by omega), hap⟩
      have hDdis : Disjoint D (Y ∪ Z) := by
        rw [Finset.disjoint_left]
        intro d hd hdu
        change d ∈ (Finset.range (v / 4)).image (fun k => 2 * k + 2) at hd
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hd
        rcases Finset.mem_union.mp hdu with hY | hZ
        · have hy := hYpos (2 * k + 2) hY
          have hkv := Finset.mem_range.mp hk
          omega
        · have hzpar := hZparity (2 * k + 2) hZ
          omega
      have hsub : (Y ∪ Z) ∪ D ⊆ (Finset.range K).image a := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact hYZsub hw
        · exact hDsub hw
      have hc := Finset.card_le_card hsub
      have hdis' : Disjoint (Y ∪ Z) D := hDdis.symm
      rw [Finset.card_union_of_disjoint hdis', hDcard, hPcard] at hc
      omega
  let I := X.filter (fun p => a (p - blockIdx v p) ∈ Z)
  have hIcard : I.card = (Y ∩ Z).card := by
    have himage : I.image (fun p => a (p - blockIdx v p)) = Y ∩ Z := by
      ext y
      simp only [I, Y, Finset.mem_image, Finset.mem_filter, Finset.mem_inter]
      constructor
      · rintro ⟨p, ⟨hp, hpZ⟩, rfl⟩
        exact ⟨⟨p, hp, rfl⟩, hpZ⟩
      · rintro ⟨⟨p, hp, rfl⟩, hpZ⟩
        exact ⟨p, ⟨hp, hpZ⟩, rfl⟩
    rw [← himage]
    symm
    exact Finset.card_image_iff.mpr ((first_block_mid_injOn hv hX hunseen).mono (by
      intro p hp
      exact (Finset.mem_filter.mp hp).1))
  have hIlarge : K - 2 * v + 2 + v / 4 ≤ I.card := by
    have hcards := Finset.card_union_add_card_inter Y Z
    rw [← hIcard, hYcard, hZcard] at hcards
    omega
  have hj : ∃ p ∈ I, 11 * v / 3 < a (p - 2 * blockIdx v p) := by
    by_contra hno
    push Not at hno
    have hrem4 : ∀ p ∈ I, a (p - 2 * blockIdx v p) % 4 = v % 4 := by
      intro p hp
      have hpX : p ∈ X := (Finset.mem_filter.mp hp).1
      have hmidZ : a (p - blockIdx v p) ∈ Z := (Finset.mem_filter.mp hp).2
      have hzpar := hZparity (a (p - 2 * blockIdx v p))
        (Finset.mem_image.mpr ⟨p, hpX, rfl⟩)
      have hmidpar := hZparity (a (p - blockIdx v p)) hmidZ
      have hs := hblock p hpX
      omega
    have hqinj : Set.InjOn (fun p => a (p - 2 * blockIdx v p) / 4) ↑I := by
      intro p hp q hq heq
      have hprem := hrem4 p hp
      have hqrem := hrem4 q hq
      have hpdiv := Nat.mod_add_div (a (p - 2 * blockIdx v p)) 4
      have hqdiv := Nat.mod_add_div (a (q - 2 * blockIdx v q)) 4
      change a (p - 2 * blockIdx v p) / 4 =
        a (q - 2 * blockIdx v q) / 4 at heq
      have hzval : a (p - 2 * blockIdx v p) = a (q - 2 * blockIdx v q) := calc
        a (p - 2 * blockIdx v p) =
            a (p - 2 * blockIdx v p) % 4 + 4 * (a (p - 2 * blockIdx v p) / 4) :=
          (Nat.mod_add_div _ _).symm
        _ = a (q - 2 * blockIdx v q) % 4 + 4 * (a (q - 2 * blockIdx v q) / 4) := by
          rw [hprem, hqrem, heq]
        _ = a (q - 2 * blockIdx v q) := Nat.mod_add_div _ _
      exact first_block_right_injOn hv hX hunseen (Finset.mem_filter.mp hp).1
        (Finset.mem_filter.mp hq).1 hzval
    let M := 11 * v / 3
    have hle : ∀ p ∈ I, a (p - 2 * blockIdx v p) ≤ M := by
      intro p hp
      dsimp [M]
      exact hno p hp
    by_cases hs : M % 4 < v % 4
    · have hmaps : Set.MapsTo (fun p => a (p - 2 * blockIdx v p) / 4) ↑I
          ↑(Finset.range (M / 4)) := by
        intro p hp
        have hpI : p ∈ I := hp
        have hzle := hle p hpI
        have hzrem := hrem4 p hpI
        have hzdiv := Nat.mod_add_div (a (p - 2 * blockIdx v p)) 4
        have hMdiv := Nat.mod_add_div M 4
        simp only [Finset.coe_range, Set.mem_Iio]
        omega
      have hc := Finset.card_le_card_of_injOn
        (fun p => a (p - 2 * blockIdx v p) / 4) hmaps hqinj
      rw [Finset.card_range] at hc
      have hK2 : 2 * v ≤ K := by
        dsimp [K]
        omega
      have hIlower : K + 2 + v / 4 ≤ I.card + 2 * v := by omega
      dsimp [M, K] at hc hIlower hs
      omega
    · by_cases hvrem : v % 4 = 0
      · have hmaps : Set.MapsTo (fun p => a (p - 2 * blockIdx v p) / 4 - 1) ↑I
            ↑(Finset.range (M / 4)) := by
          intro p hp
          have hpI : p ∈ I := hp
          have hzle := hle p hpI
          have hzrem := hrem4 p hpI
          have hzpos := one_le_a (p - 2 * blockIdx v p)
          have hzdiv := Nat.mod_add_div (a (p - 2 * blockIdx v p)) 4
          have hMdiv := Nat.mod_add_div M 4
          simp only [Finset.coe_range, Set.mem_Iio]
          omega
        have hinj : Set.InjOn (fun p => a (p - 2 * blockIdx v p) / 4 - 1) ↑I := by
          intro p hp q hq heq
          have hprem := hrem4 p hp
          have hqrem := hrem4 q hq
          have hpdiv := Nat.mod_add_div (a (p - 2 * blockIdx v p)) 4
          have hqdiv := Nat.mod_add_div (a (q - 2 * blockIdx v q)) 4
          have hppos := one_le_a (p - 2 * blockIdx v p)
          have hqpos := one_le_a (q - 2 * blockIdx v q)
          change a (p - 2 * blockIdx v p) / 4 - 1 =
            a (q - 2 * blockIdx v q) / 4 - 1 at heq
          have hpqpos : 1 ≤ a (p - 2 * blockIdx v p) / 4 := by omega
          have hqqpos : 1 ≤ a (q - 2 * blockIdx v q) / 4 := by omega
          have hdiv : a (p - 2 * blockIdx v p) / 4 =
              a (q - 2 * blockIdx v q) / 4 := by omega
          exact hqinj hp hq hdiv
        have hc := Finset.card_le_card_of_injOn
          (fun p => a (p - 2 * blockIdx v p) / 4 - 1) hmaps hinj
        rw [Finset.card_range] at hc
        have hK2 : 2 * v ≤ K := by
          dsimp [K]
          omega
        have hIlower : K + 2 + v / 4 ≤ I.card + 2 * v := by omega
        dsimp [M, K] at hc hIlower hvrem
        omega
      · have hmaps : Set.MapsTo (fun p => a (p - 2 * blockIdx v p) / 4) ↑I
            ↑(Finset.range (M / 4 + 1)) := by
          intro p hp
          have hpI : p ∈ I := hp
          have hzle := hle p hpI
          have hzdiv := Nat.mod_add_div (a (p - 2 * blockIdx v p)) 4
          have hMdiv := Nat.mod_add_div M 4
          simp only [Finset.coe_range, Set.mem_Iio]
          omega
        have hc := Finset.card_le_card_of_injOn
          (fun p => a (p - 2 * blockIdx v p) / 4) hmaps hqinj
        rw [Finset.card_range] at hc
        have hvrempos : 0 < v % 4 := by omega
        have hMrem : v % 4 ≤ M % 4 := by omega
        have hK2 : 2 * v ≤ K := by
          dsimp [K]
          omega
        have hIlower : K + 2 + v / 4 ≤ I.card + 2 * v := by omega
        dsimp [M, K] at hc hIlower hvrempos hMrem
        omega
  obtain ⟨j, hjI, hzj⟩ := hj
  have hjX : j ∈ X := (Finset.mem_filter.mp hjI).1
  let z := a (j - 2 * blockIdx v j)
  have hz : z = a (j - 2 * blockIdx v j) := rfl
  have hzZ : z ∈ Z := by
    exact Finset.mem_image.mpr ⟨j, hjX, rfl⟩
  have hjblock := hblock j hjX
  let p₀ := j - 2 * blockIdx v j
  have hp₀K : p₀ < K := by
    obtain ⟨hjK, hjv⟩ := hX j hjX
    dsimp [p₀]
    omega
  let B := (Finset.range K).image a |>.filter (fun w => w % 2 ≠ v % 2)
  have hBcard : B.card < v := by
    have hZsubBcompl : Z ⊆ ((Finset.range K).image a).filter (fun w => ¬ w % 2 ≠ v % 2) := by
      intro w hw
      have hwP := hYZsub (Finset.mem_union_right Y hw)
      rw [Finset.mem_filter]
      exact ⟨hwP, by simpa only [not_not] using hZparity w hw⟩
    have hpart := Finset.card_filter_add_card_filter_not
      (s := (Finset.range K).image a) (fun w => w % 2 ≠ v % 2)
    have hZle := Finset.card_le_card hZsubBcompl
    have hPcard : ((Finset.range K).image a).card = K := calc
      ((Finset.range K).image a).card = (Finset.range K).card :=
        Finset.card_image_iff.mpr a_injective.injOn
      _ = K := Finset.card_range K
    dsimp only [B]
    rw [hPcard] at hpart
    rw [hZcard] at hZle
    omega
  let off : ℕ → Finset ℕ := fun T =>
    if Even v then (Finset.range (T / 2)).image (fun k => 2 * k + 1)
    else (Finset.range (T / 2)).image (fun k => 2 * k + 2)
  have hoff_card (T : ℕ) : (off T).card = T / 2 := by
    by_cases hev : Even v
    · simp only [off, if_pos hev]
      rw [Finset.card_image_of_injective]
      · exact Finset.card_range _
      · intro x y hxy
        apply Nat.mul_left_cancel (n := 2) (by omega)
        exact Nat.add_right_cancel hxy
    · simp only [off, if_neg hev]
      rw [Finset.card_image_of_injective]
      · exact Finset.card_range _
      · intro x y hxy
        apply Nat.mul_left_cancel (n := 2) (by omega)
        exact Nat.add_right_cancel hxy
  have hoff_spec {T w : ℕ} (hw : w ∈ off T) : 1 ≤ w ∧ w ≤ T ∧ w % 2 ≠ v % 2 := by
    by_cases hev : Even v
    · have hvmod : v % 2 = 0 := Nat.even_iff.mp hev
      simp only [off, if_pos hev, Finset.mem_image] at hw
      obtain ⟨k, hk, rfl⟩ := hw
      have hkT := Finset.mem_range.mp hk
      omega
    · have hvodd : v % 2 = 1 := Nat.not_even_iff.mp hev
      simp only [off, if_neg hev, Finset.mem_image] at hw
      obtain ⟨k, hk, rfl⟩ := hw
      have hkT := Finset.mem_range.mp hk
      omega
  let M := 11 * v / 3
  let C := off M \ B
  have hCcard : 5 * v < 6 * C.card := by
    have hparts := Finset.card_sdiff_add_card_inter (off M) B
    have hinter : ((off M) ∩ B).card ≤ B.card :=
      Finset.card_le_card (Finset.inter_subset_right)
    change C.card + ((off M) ∩ B).card = (off M).card at hparts
    rw [hoff_card] at hparts
    dsimp [M] at hparts hinter
    omega
  have hCspec : ∀ c ∈ C, 1 ≤ c ∧ c < z ∧ c % 2 ≠ v % 2 := by
    intro c hc
    have hcOff : c ∈ off M := (Finset.mem_sdiff.mp hc).1
    obtain ⟨hc1, hcM, hcpar⟩ := hoff_spec hcOff
    dsimp [M] at hcM
    exact ⟨hc1, by omega, hcpar⟩
  have hCnotB : ∀ c ∈ C, c ∉ B := by
    intro c hc
    exact (Finset.mem_sdiff.mp hc).2
  have hCunseen : ∀ c ∈ C, ∀ k < p₀, a k ≠ c := by
    intro c hc k hk heq
    have hcpar := (hCspec c hc).2.2
    apply hCnotB c hc
    dsimp only [B]
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), heq⟩, ?_⟩
    simpa only [heq] using hcpar
  have hCblock : ∀ c ∈ C,
      1 ≤ blockIdx c p₀ ∧ 2 * blockIdx c p₀ ≤ p₀ ∧
        c + a (p₀ - 2 * blockIdx c p₀) = 2 * a (p₀ - blockIdx c p₀) := by
    intro c hc
    have hpval : a p₀ = z := by exact hz.symm
    exact blockIdx_spec (hCspec c hc).1 (hCunseen c hc)
      (by rw [hpval]; exact (hCspec c hc).2.1)
  have hbetaInB : ∀ c ∈ C, a (p₀ - 2 * blockIdx c p₀) ∈ B := by
    intro c hc
    obtain ⟨hs1, hs2, hs3⟩ := hCblock c hc
    have hcpar := (hCspec c hc).2.2
    dsimp only [B]
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_image.mpr ⟨p₀ - 2 * blockIdx c p₀,
      Finset.mem_range.mpr (by omega), rfl⟩, ?_⟩
    omega
  have hbetaParity : ∀ c ∈ C, (p₀ - 2 * blockIdx c p₀) % 2 = p₀ % 2 := by
    intro c hc
    have hs := hCblock c hc
    omega
  have hbetaInj : Set.InjOn (fun c => p₀ - 2 * blockIdx c p₀) ↑C := by
    intro c hc d hd heq
    obtain ⟨hc1, hc2, hc3⟩ := hCblock c hc
    obtain ⟨hd1, hd2, hd3⟩ := hCblock d hd
    change p₀ - 2 * blockIdx c p₀ = p₀ - 2 * blockIdx d p₀ at heq
    have hcsub : p₀ - 2 * blockIdx c p₀ + 2 * blockIdx c p₀ = p₀ :=
      Nat.sub_add_cancel hc2
    have hdsub : p₀ - 2 * blockIdx d p₀ + 2 * blockIdx d p₀ = p₀ :=
      Nat.sub_add_cancel hd2
    rw [heq] at hcsub
    have hmul : 2 * blockIdx c p₀ = 2 * blockIdx d p₀ :=
      Nat.add_left_cancel (hcsub.trans hdsub.symm)
    have hs : blockIdx c p₀ = blockIdx d p₀ :=
      Nat.mul_left_cancel (by omega) hmul
    rw [hs] at hc3
    omega
  let Ψ := C.image (fun c => p₀ - 2 * blockIdx c p₀)
  have hPsiCard : Ψ.card = C.card := by
    change (C.image (fun c => p₀ - 2 * blockIdx c p₀)).card = C.card
    exact Finset.card_image_iff.mpr hbetaInj
  have hPsiRange : Ψ ⊆ Finset.range K := by
    intro b hb
    change b ∈ C.image (fun c => p₀ - 2 * blockIdx c p₀) at hb
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_range.mpr (by have hs := hCblock c hc; omega)
  have hPsiParity : ∀ b ∈ Ψ, b % 2 = p₀ % 2 := by
    intro b hb
    change b ∈ C.image (fun c => p₀ - 2 * blockIdx c p₀) at hb
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
    exact hbetaParity c hc
  have hlargeParity : ∀ e < K, 7 * v / 3 < a e → e % 2 = p₀ % 2 := by
    intro e heK heLarge
    by_contra hpar
    let H := 7 * v / 3
    let E := off H \ B
    have hEcard : v < 6 * E.card := by
      have hparts := Finset.card_sdiff_add_card_inter (off H) B
      have hinter : ((off H) ∩ B).card ≤ B.card :=
        Finset.card_le_card Finset.inter_subset_right
      change E.card + ((off H) ∩ B).card = (off H).card at hparts
      rw [hoff_card] at hparts
      dsimp [H] at hparts hinter
      omega
    have hEspec : ∀ c ∈ E, 1 ≤ c ∧ c < a e ∧ c % 2 ≠ v % 2 := by
      intro c hc
      have hcOff : c ∈ off H := (Finset.mem_sdiff.mp hc).1
      obtain ⟨hc1, hcH, hcpar⟩ := hoff_spec hcOff
      dsimp [H] at hcH
      exact ⟨hc1, by omega, hcpar⟩
    have hEnotB : ∀ c ∈ E, c ∉ B := by
      intro c hc
      exact (Finset.mem_sdiff.mp hc).2
    have hEunseen : ∀ c ∈ E, ∀ k < e, a k ≠ c := by
      intro c hc k hk heq
      apply hEnotB c hc
      dsimp only [B]
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), heq⟩, ?_⟩
      simpa only [heq] using (hEspec c hc).2.2
    have hEblock : ∀ c ∈ E,
        1 ≤ blockIdx c e ∧ 2 * blockIdx c e ≤ e ∧
          c + a (e - 2 * blockIdx c e) = 2 * a (e - blockIdx c e) := by
      intro c hc
      exact blockIdx_spec (hEspec c hc).1 (hEunseen c hc) (hEspec c hc).2.1
    have hEbetaInB : ∀ c ∈ E, a (e - 2 * blockIdx c e) ∈ B := by
      intro c hc
      obtain ⟨hs1, hs2, hs3⟩ := hEblock c hc
      dsimp only [B]
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_image.mpr ⟨e - 2 * blockIdx c e,
        Finset.mem_range.mpr (by omega), rfl⟩, ?_⟩
      have hcpar := (hEspec c hc).2.2
      omega
    have hEbetaInj : Set.InjOn (fun c => e - 2 * blockIdx c e) ↑E := by
      intro c hc d hd heq
      obtain ⟨hc1, hc2, hc3⟩ := hEblock c hc
      obtain ⟨hd1, hd2, hd3⟩ := hEblock d hd
      change e - 2 * blockIdx c e = e - 2 * blockIdx d e at heq
      have hcsub : e - 2 * blockIdx c e + 2 * blockIdx c e = e :=
        Nat.sub_add_cancel hc2
      have hdsub : e - 2 * blockIdx d e + 2 * blockIdx d e = e :=
        Nat.sub_add_cancel hd2
      rw [heq] at hcsub
      have hmul : 2 * blockIdx c e = 2 * blockIdx d e :=
        Nat.add_left_cancel (hcsub.trans hdsub.symm)
      have hs : blockIdx c e = blockIdx d e :=
        Nat.mul_left_cancel (by omega) hmul
      rw [hs] at hc3
      omega
    let W := E.image (fun c => a (e - 2 * blockIdx c e))
    have hWcard : W.card = E.card := by
      have hidx : Set.InjOn (fun c => e - 2 * blockIdx c e) ↑E := hEbetaInj
      have hval : Set.InjOn (fun c => a (e - 2 * blockIdx c e)) ↑E :=
        a_injective.injOn.comp hidx (Set.mapsTo_univ _ _)
      change (E.image (fun c => a (e - 2 * blockIdx c e))).card = E.card
      exact Finset.card_image_iff.mpr hval
    let V := C.image (fun c => a (p₀ - 2 * blockIdx c p₀))
    have hVcard : V.card = C.card := by
      have hval : Set.InjOn (fun c => a (p₀ - 2 * blockIdx c p₀)) ↑C :=
        a_injective.injOn.comp hbetaInj (Set.mapsTo_univ _ _)
      change (C.image (fun c => a (p₀ - 2 * blockIdx c p₀))).card = C.card
      exact Finset.card_image_iff.mpr hval
    have hWsub : W ⊆ B := by
      intro w hw
      change w ∈ E.image (fun c => a (e - 2 * blockIdx c e)) at hw
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hw
      exact hEbetaInB c hc
    have hVsub : V ⊆ B := by
      intro w hw
      change w ∈ C.image (fun c => a (p₀ - 2 * blockIdx c p₀)) at hw
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hw
      exact hbetaInB c hc
    have hWVdis : Disjoint W V := by
      rw [Finset.disjoint_left]
      intro w hwW hwV
      change w ∈ E.image (fun c => a (e - 2 * blockIdx c e)) at hwW
      change w ∈ C.image (fun c => a (p₀ - 2 * blockIdx c p₀)) at hwV
      obtain ⟨c, hc, hcw⟩ := Finset.mem_image.mp hwW
      obtain ⟨d, hd, hdw⟩ := Finset.mem_image.mp hwV
      have hidx : e - 2 * blockIdx c e = p₀ - 2 * blockIdx d p₀ :=
        a_injective (hcw.trans hdw.symm)
      have hepar : (e - 2 * blockIdx c e) % 2 = e % 2 := by
        have hs := hEblock c hc
        omega
      have hppar := hbetaParity d hd
      exact hpar (by omega)
    have hsub : W ∪ V ⊆ B := Finset.union_subset hWsub hVsub
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hWVdis, hWcard, hVcard] at hc
    omega
  let Φ := (Finset.range K).filter (fun e => a e ∈ Z ∧ 7 * v / 3 < a e)
  have hPhiCard : Φ.card = (Z.filter (fun w => 7 * v / 3 < w)).card := by
    have himage : Φ.image a = Z.filter (fun w => 7 * v / 3 < w) := by
      apply Finset.ext
      intro w
      constructor
      · intro hw
        obtain ⟨e, hePhi, hew⟩ := Finset.mem_image.mp hw
        obtain ⟨heK, heZ, heLarge⟩ := Finset.mem_filter.mp hePhi
        exact Finset.mem_filter.mpr ⟨hew ▸ heZ, hew ▸ heLarge⟩
      · intro hw
        obtain ⟨hwZ, hwLarge⟩ := Finset.mem_filter.mp hw
        have hwP := hYZsub (Finset.mem_union_right Y hwZ)
        obtain ⟨e, heK, hew⟩ := Finset.mem_image.mp hwP
        refine Finset.mem_image.mpr ⟨e, ?_, hew⟩
        exact Finset.mem_filter.mpr ⟨heK, hew ▸ hwZ, hew ▸ hwLarge⟩
    have hcardImage : (Φ.image a).card = Φ.card :=
      Finset.card_image_iff.mpr a_injective.injOn
    calc
      Φ.card = (Φ.image a).card := hcardImage.symm
      _ = (Z.filter (fun w => 7 * v / 3 < w)).card := congrArg Finset.card himage
  have hPhiLarge : v < 2 * Φ.card := by
    have hsmall : (Z.filter (fun w => ¬ 7 * v / 3 < w)).card ≤
        if Even v then (7 * v / 3) / 2 else (7 * v / 3 + 1) / 2 := by
      by_cases hev : Even v
      · have hvrem : v % 2 = 0 := Nat.even_iff.mp hev
        have hc := card_pos_even_le (Z.filter (fun w => ¬ 7 * v / 3 < w))
          (7 * v / 3) (by
            intro w hw
            obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hw).1
            exact one_le_a _) (by
            intro w hw
            exact Nat.le_of_not_gt (Finset.mem_filter.mp hw).2) (by
            intro w hw
            simpa only [hvrem] using hZparity w (Finset.mem_filter.mp hw).1)
        simpa only [if_pos hev] using hc
      · have hvrem : v % 2 = 1 := Nat.not_even_iff.mp hev
        have hc := card_pos_odd_le (Z.filter (fun w => ¬ 7 * v / 3 < w))
          (7 * v / 3) (by
            intro w hw
            exact Nat.le_of_not_gt (Finset.mem_filter.mp hw).2) (by
            intro w hw
            simpa only [hvrem] using hZparity w (Finset.mem_filter.mp hw).1)
        simpa only [if_neg hev] using hc
    have hparts := Finset.card_filter_add_card_filter_not
      (s := Z) (fun w => 7 * v / 3 < w)
    rw [← hPhiCard, hZcard] at hparts
    by_cases hev : Even v
    · simp only [if_pos hev] at hsmall
      omega
    · simp only [if_neg hev] at hsmall
      have hvrem : v % 2 = 1 := Nat.not_even_iff.mp hev
      have harith : v + 2 * ((7 * v / 3 + 1) / 2) < 2 * (K - v + 1) := by
        dsimp [K]
        omega
      omega
  have hPhiRange : Φ ⊆ Finset.range K := by
    intro e he
    exact (Finset.mem_filter.mp he).1
  have hPhiParity : ∀ e ∈ Φ, e % 2 = p₀ % 2 := by
    intro e he
    have heSpec := (Finset.mem_filter.mp he).2
    exact hlargeParity e (Finset.mem_range.mp (Finset.mem_filter.mp he).1) heSpec.2
  have hPhiPsiDis : Disjoint Φ Ψ := by
    rw [Finset.disjoint_left]
    intro e hePhi hePsi
    have heVal : a e ∈ Z := (Finset.mem_filter.mp hePhi).2.1
    change e ∈ C.image (fun c => p₀ - 2 * blockIdx c p₀) at hePsi
    obtain ⟨c, hc, heq⟩ := Finset.mem_image.mp hePsi
    have hvalB := hbetaInB c hc
    have hvaleq : a e = a (p₀ - 2 * blockIdx c p₀) := congrArg a heq.symm
    dsimp only [B] at hvalB
    have hparB := (Finset.mem_filter.mp hvalB).2
    have hparZ := hZparity (a e) heVal
    exact hparB (hvaleq ▸ hparZ)
  have hAllRange : Φ ∪ Ψ ⊆ (Finset.range K).filter (fun e => e % 2 = p₀ % 2) := by
    intro e he
    rw [Finset.mem_filter]
    rcases Finset.mem_union.mp he with hePhi | hePsi
    · exact ⟨hPhiRange hePhi, hPhiParity e hePhi⟩
    · exact ⟨hPsiRange hePsi, hPsiParity e hePsi⟩
  have hParityCard := card_filter_range_mod_two_eq_le K p₀
  have hc := Finset.card_le_card hAllRange
  rw [Finset.card_union_of_disjoint hPhiPsiDis, hPsiCard] at hc
  dsimp [K] at hc hParityCard
  omega

/-- The prefix-parity count includes the empty prefix boundary. -/
example : ((Finset.range 0).filter (fun e => e % 2 = 0)).card ≤ (0 + 1) / 2 :=
  card_filter_range_mod_two_eq_le 0 0

/-- The bound is nonvacuous at the OEIS boundary term `a 0 = 1`. -/
example : 3 * (0 + 1) ≤ 8 * a 0 := hegarty_three_eighths 0

#check @card_filter_range_mod_two_eq_le
#print axioms card_filter_range_mod_two_eq_le
#check @hegarty_three_eighths
#print axioms hegarty_three_eighths

end A094870
