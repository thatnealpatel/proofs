import Mathlib

/-!
# Zumkeller identity

For each `k ≥ 1`, the number of nonempty subsets of `{1,…,k}` with
sum ≡ 0 (mod k) equals the number of subsets of `{1,…,k}` containing
k whose mean is an integer:

  `#{nonempty S ⊆ {1,…,k} : k | sum(S)} = #{S ⊆ {1,…,k} : k ∈ S, |S| | sum(S)}`

First observed without proof on OEIS:
- A082550 formula `a(n) = A063776(n) - 1` (2003, original submission)
- Zumkeller (2006): `A082550(n) = A051293(n+1) - A051293(n)`
- Papadopoulos (2016): equivalence noted explicitly
- Wiseman (2019): restated on A063776

This file contains the first formal proof.
-/

open Finset BigOperators

namespace A051293

/-- The set of subsets of `Finset.range k` (representing {0,…,k-1})
    whose elements, shifted by 1, sum to 0 mod k. -/
def modSubsets (k : ℕ) : Finset (Finset ℕ) :=
  (Finset.range k).powerset.filter (fun S =>
    k ∣ (S.sum (· + 1)))

/-- `b_comb(k) = #{S ⊆ {1,…,k} : k | sum(S)}`. -/
def b_comb (k : ℕ) : ℕ := (modSubsets k).card

section StepA

/-! ### Step (A): Per-k identity (Wiseman's observation)

For each `k ≥ 1`:
  `#{nonempty S ⊆ {1,…,k} : k | sum(S)}`
  `= #{S ⊆ {1,…,k} : k ∈ S, |S| | sum(S)}`

The LHS is `b_comb(k) − 1`. The RHS counts subsets of `{1,…,k}`
containing k with integer mean.

Computationally verified through k = 22 (`cmd/51293/perk.go`).
No published proof is known; Wiseman (OEIS A063776, 2019) observed
the equality without proof. -/

/-- Subsets of `{1,…,k}` containing k with integer mean. -/
def maxKIntMeanSubsets (k : ℕ) : Finset (Finset ℕ) :=
  (Finset.range k).powerset.filter (fun S =>
    (k - 1) ∈ S ∧ S.card ∣ (S.sum (· + 1)))

private def rotateSet (k r : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.image (fun s => (s + r) % k)

private lemma rotateSet_subset_range {k r : ℕ} {S : Finset ℕ} (hk : 0 < k)
    (_hS : S ⊆ Finset.range k) : rotateSet k r S ⊆ Finset.range k := by
  intro x hx
  simp only [rotateSet, Finset.mem_image] at hx
  obtain ⟨s, _, hs_eq⟩ := hx
  rw [← hs_eq, Finset.mem_range]
  exact Nat.mod_lt _ hk

private lemma rotateSet_injOn {k r : ℕ} (_hk : 0 < k)
    {S : Finset ℕ} (hS : S ⊆ Finset.range k) :
    Set.InjOn (fun s => (s + r) % k) ↑S := by
  intro a ha b hb hab
  have ha' : a < k := Finset.mem_range.mp (hS ha)
  have hb' : b < k := Finset.mem_range.mp (hS hb)
  exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_right_cancel' r hab) ha' hb'

private lemma rotateSet_card {k r : ℕ} (hk : 0 < k)
    {S : Finset ℕ} (hS : S ⊆ Finset.range k) : (rotateSet k r S).card = S.card :=
  Finset.card_image_of_injOn (rotateSet_injOn hk hS)

private lemma rotateSet_dvd_iff (k r : ℕ) (hk : 0 < k) (S : Finset ℕ)
    (hS : S ⊆ Finset.range k) :
    k ∣ (rotateSet k r S).sum (· + 1) ↔ k ∣ (S.sum (· + 1) + r * S.card) := by
  simp only [rotateSet, Finset.sum_image (rotateSet_injOn hk hS)]
  have h_term : ∀ s, s + r + 1 = (s + r) % k + 1 + k * ((s + r) / k) := by
    intro s; have := Nat.div_add_mod (s + r) k; omega
  have key : S.sum (· + 1) + r * S.card =
      (∑ s ∈ S, ((s + r) % k + 1)) + k * (∑ s ∈ S, (s + r) / k) := by
    trans ∑ s ∈ S, (s + r + 1)
    · trans (∑ s ∈ S, (s + 1)) + ∑ _s ∈ S, r
      · congr 1; rw [Finset.sum_const, smul_eq_mul, mul_comm]
      · rw [← Finset.sum_add_distrib]; congr 1; ext s; omega
    · rw [Finset.sum_congr rfl (fun s _ => h_term s), Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [key, add_comm]
  exact (Nat.dvd_add_right (dvd_mul_right k _)).symm

private lemma gcd_dvd_of_dvd_add_mul (a b m r : ℕ) (h : m ∣ (b + a * r)) :
    Nat.gcd a m ∣ b := by
  have h1 : Nat.gcd a m ∣ a * r := dvd_mul_of_dvd_left (Nat.gcd_dvd_left a m) r
  rw [add_comm] at h
  exact (Nat.dvd_add_right h1).mp (dvd_trans (Nat.gcd_dvd_right a m) h)

private lemma card_filter_dvd_add_mul_empty (b a m : ℕ) (_hm : 0 < m)
    (hndvd : ¬ Nat.gcd a m ∣ b) :
    ((Finset.range m).filter (fun r => m ∣ (b + a * r))).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro r _
  exact fun h => hndvd (gcd_dvd_of_dvd_add_mul a b m r h)

private lemma dvd_mul_iff_q_dvd (a m : ℕ) (hm : 0 < m) (r : ℕ) :
    m ∣ a * r ↔ m / Nat.gcd a m ∣ r := by
  set g := Nat.gcd a m
  set q := m / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_right a hm
  have hgm : g ∣ m := Nat.gcd_dvd_right a m
  have hga : g ∣ a := Nat.gcd_dvd_left a m
  have hcoprime : Nat.Coprime (a / g) (m / g) :=
    Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right a hm)
  rw [show m = q * g from (Nat.div_mul_cancel hgm).symm,
    show a = a / g * g from (Nat.div_mul_cancel hga).symm,
    show a / g * g * r = (a / g * r) * g from by ring,
    Nat.mul_dvd_mul_iff_right hg]
  exact ⟨fun h => hcoprime.symm.dvd_of_dvd_mul_left h,
    fun h => dvd_mul_of_dvd_right h _⟩

private lemma card_filter_q_dvd (m : ℕ) (_hm : 0 < m) (q : ℕ) (hq : 0 < q) (hqm : q ∣ m) :
    ((Finset.range m).filter (fun r => q ∣ r)).card = m / q := by
  have h_eq : (Finset.range m).filter (fun r => q ∣ r) =
      (Finset.range (m / q)).image (· * q) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · intro ⟨hr, hdvd⟩
      exact ⟨r / q, Nat.div_lt_div_of_lt_of_dvd hqm hr, Nat.div_mul_cancel hdvd⟩
    · intro ⟨i, hi, hir⟩
      subst hir
      constructor
      · calc i * q < m / q * q := (Nat.mul_lt_mul_right hq).mpr hi
          _ = m := Nat.div_mul_cancel hqm
      · exact dvd_mul_left q i
  rw [h_eq, Finset.card_image_of_injective _
    (fun a b h => Nat.eq_of_mul_eq_mul_right hq h), Finset.card_range]

private lemma card_filter_dvd_mul_zero (a m : ℕ) (hm : 0 < m) :
    ((Finset.range m).filter (fun r => m ∣ a * r)).card = Nat.gcd a m := by
  set g := Nat.gcd a m
  set q := m / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_right a hm
  have hgm : g ∣ m := Nat.gcd_dvd_right a m
  have hq_pos : 0 < q := Nat.div_pos (Nat.le_of_dvd hm hgm) hg
  have hqm : q ∣ m := by exact Nat.div_dvd_of_dvd hgm
  have h_iff : ∀ r, m ∣ a * r ↔ q ∣ r := dvd_mul_iff_q_dvd a m hm
  have : (Finset.range m).filter (fun r => m ∣ a * r) =
      (Finset.range m).filter (fun r => q ∣ r) := by
    ext r; simp [h_iff]
  rw [this, card_filter_q_dvd m hm q hq_pos hqm]
  exact Nat.div_div_self hgm hm.ne'

private lemma coprime_unique_solution (b c q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime c q) :
    ∃! r₀, r₀ < q ∧ q ∣ (b + c * r₀) := by
  have h_exists : ∃ r₀ < q, q ∣ (b + c * r₀) := by
    have h_inj : Function.Injective (fun r : Fin q => (⟨(b + c * r.val) % q,
        Nat.mod_lt _ hq⟩ : Fin q)) := by
      intro ⟨r₁, hr₁⟩ ⟨r₂, hr₂⟩ h
      simp only [Fin.mk.injEq] at h ⊢
      have h₁ : b + c * r₁ ≡ b + c * r₂ [MOD q] := h
      have h₂ : c * r₁ ≡ c * r₂ [MOD q] := Nat.ModEq.add_left_cancel (Nat.ModEq.refl b) h₁
      have h₃ : r₁ ≡ r₂ [MOD q] := by
        have := h₂.cancel_left_div_gcd hq
        rwa [Nat.gcd_comm, hcop, Nat.div_one] at this
      exact (h₃.eq_of_lt_of_lt hr₁ hr₂)
    have h_surj := Finite.surjective_of_injective h_inj
    obtain ⟨⟨r₀, hr₀_lt⟩, hr₀_eq⟩ := h_surj ⟨0, hq⟩
    simp only [Fin.mk.injEq] at hr₀_eq
    exact ⟨r₀, hr₀_lt, Nat.dvd_of_mod_eq_zero hr₀_eq⟩
  obtain ⟨r₀, hr₀_lt, hr₀_dvd⟩ := h_exists
  refine ⟨r₀, ⟨hr₀_lt, hr₀_dvd⟩, ?_⟩
  intro r₁ ⟨hr₁_lt, hr₁_dvd⟩
  have h₁ : q ∣ (b + c * r₀) := hr₀_dvd
  have h₂ : q ∣ (b + c * r₁) := hr₁_dvd
  by_cases h : r₀ ≤ r₁
  · have h₃ : q ∣ c * r₁ - c * r₀ := by
      have h₄ := Nat.dvd_sub h₂ h₁
      rwa [Nat.add_sub_add_left] at h₄
    rw [← Nat.mul_sub c r₁ r₀] at h₃
    have h₅ : q ∣ r₁ - r₀ := hcop.symm.dvd_of_dvd_mul_left h₃
    have h₆ : r₁ - r₀ < q := by omega
    have h₇ : r₁ - r₀ = 0 := Nat.eq_zero_of_dvd_of_lt h₅ h₆
    omega
  · have h₃ : q ∣ c * r₀ - c * r₁ := by
      have h₄ := Nat.dvd_sub h₁ h₂
      rwa [Nat.add_sub_add_left] at h₄
    rw [← Nat.mul_sub c r₀ r₁] at h₃
    have h₅ : q ∣ r₀ - r₁ := hcop.symm.dvd_of_dvd_mul_left h₃
    have h₆ : r₀ - r₁ < q := by omega
    have h₇ : r₀ - r₁ = 0 := Nat.eq_zero_of_dvd_of_lt h₅ h₆
    omega

private lemma card_filter_q_dvd_coprime (b c m q : ℕ) (_hm : 0 < m) (hq : 0 < q)
    (hqm : q ∣ m) (hcop : Nat.Coprime c q) :
    ((Finset.range m).filter (fun r => q ∣ (b + c * r))).card = m / q := by
  set p : ℕ → Prop := fun r => q ∣ (b + c * r) with hp_def
  have h_periodic : Function.Periodic p q := by
    intro r; show (q ∣ (b + c * (r + q))) = (q ∣ (b + c * r))
    rw [show b + c * (r + q) = b + c * r + c * q from by ring]
    rw [show b + c * r + c * q = c * q + (b + c * r) from by ring]
    exact propext (Nat.dvd_add_right (dvd_mul_left q c))
  obtain ⟨r₀, ⟨hr₀_lt, hr₀_dvd⟩, hr₀_unique⟩ := coprime_unique_solution b c q hq hcop
  have h_count : q.count p = 1 := by
    rw [Nat.count_eq_card_filter_range]
    have h_single : (Finset.range q).filter p = {r₀} := by
      ext r; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, hp_def]
      exact ⟨fun ⟨hr, hdvd⟩ => hr₀_unique r ⟨hr, hdvd⟩,
        fun h => by subst h; exact ⟨hr₀_lt, hr₀_dvd⟩⟩
    rw [h_single, Finset.card_singleton]
  set n := m / q with hn_def
  have hm_eq : m = n * q := by rw [hn_def]; exact (Nat.div_mul_cancel hqm).symm
  conv_lhs => rw [show Finset.range m = Finset.Ico 0 m from by simp, hm_eq]
  suffices h : ∀ k, ((Finset.Ico 0 (k * q)).filter p).card = k by
    convert h n using 2
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * q = k * q + q from by ring]
    have h_union : Finset.Ico 0 (k * q + q) = Finset.Ico 0 (k * q) ∪ Finset.Ico (k * q) (k * q + q) :=
      (Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)).symm
    rw [h_union, Finset.filter_union]
    have h_disj : Disjoint (Finset.Ico 0 (k * q)) (Finset.Ico (k * q) (k * q + q)) :=
      Finset.Ico_disjoint_Ico_consecutive 0 (k * q) (k * q + q)
    rw [Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h_disj)]
    linarith [Nat.filter_Ico_card_eq_of_periodic (k * q) q p h_periodic, h_count]

private lemma card_filter_dvd_add_mul (b a m : ℕ) (hm : 0 < m) :
    ((Finset.range m).filter (fun r => m ∣ (b + a * r))).card =
      if Nat.gcd a m ∣ b then Nat.gcd a m else 0 := by
  split_ifs with hdvd
  · set g := Nat.gcd a m
    set q := m / g
    have hg : 0 < g := Nat.gcd_pos_of_pos_right a hm
    have hgm : g ∣ m := Nat.gcd_dvd_right a m
    have hga : g ∣ a := Nat.gcd_dvd_left a m
    have hq_pos : 0 < q := Nat.div_pos (Nat.le_of_dvd hm hgm) hg
    have hm_eq : m = q * g := (Nat.div_mul_cancel hgm).symm
    have h_iff : ∀ r, m ∣ (b + a * r) ↔ q ∣ (b / g + a / g * r) := by
      intro r
      have hrewrite : b + a * r = g * (b / g + a / g * r) := by
        rw [mul_add, mul_comm g (b / g), Nat.div_mul_cancel hdvd,
          show g * (a / g * r) = a / g * g * r from by ring, Nat.div_mul_cancel hga]
      rw [hrewrite, hm_eq, show q * g = g * q from mul_comm q g, Nat.mul_dvd_mul_iff_left hg]
    have h_filter_eq : (Finset.range m).filter (fun r => m ∣ (b + a * r)) =
        (Finset.range m).filter (fun r => q ∣ (b / g + a / g * r)) := by
      ext r; simp [h_iff]
    rw [h_filter_eq]
    conv_rhs => rw [show g = m / q from (Nat.div_div_self hgm hm.ne').symm]
    exact card_filter_q_dvd_coprime (b / g) (a / g) m q hm hq_pos
      (Nat.div_dvd_of_dvd hgm)
      (Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right a hm))
  · exact card_filter_dvd_add_mul_empty b a m hm hdvd

private def α (k : ℕ) (S : Finset ℕ) : ℕ :=
  ((Finset.range k).filter (fun r => k ∣ (S.sum (· + 1) + r * S.card))).card

private def β (k : ℕ) (S : Finset ℕ) : ℕ :=
  ((Finset.range S.card).filter (fun j => S.card ∣ (S.sum (· + 1) + k * j))).card

private lemma alpha_eq_beta (k : ℕ) (S : Finset ℕ) (hk : 0 < k) (hne : S.Nonempty) :
    α k S = β k S := by
  have hd : 0 < S.card := Finset.card_pos.mpr hne
  set s := S.sum (· + 1)
  simp only [α, β]
  have h1 : ((Finset.range k).filter (fun r => k ∣ (s + r * S.card))).card =
      ((Finset.range k).filter (fun r => k ∣ (s + S.card * r))).card := by
    congr 1; ext r; simp [mul_comm]
  rw [h1, card_filter_dvd_add_mul s S.card k hk, card_filter_dvd_add_mul s k S.card hd,
    Nat.gcd_comm]

private lemma rotateSet_mem_powerset {k r : ℕ} (hk : 0 < k)
    {S : Finset ℕ} (hS : S ∈ (Finset.range k).powerset) :
    rotateSet k r S ∈ (Finset.range k).powerset := by
  rw [Finset.mem_powerset] at hS ⊢
  exact rotateSet_subset_range hk hS

private lemma rotateSet_nonempty {k r : ℕ} (_hk : 0 < k)
    {S : Finset ℕ} (_hS : S ⊆ Finset.range k) (hne : S.Nonempty) :
    (rotateSet k r S).Nonempty := by
  rw [Finset.Nonempty] at hne ⊢
  obtain ⟨x, hx⟩ := hne
  exact ⟨(x + r) % k, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩

private lemma rotateSet_injOn_powerset (k r : ℕ) (_hk : 0 < k) :
    Set.InjOn (rotateSet k r) ↑((Finset.range k).powerset) := by
  intro S hS T hT hST
  rw [Finset.mem_coe, Finset.mem_powerset] at hS hT
  ext x
  constructor <;> intro hx
  · have : (x + r) % k ∈ rotateSet k r T := hST ▸
      Finset.mem_image.mpr ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp this
    have := Finset.mem_range.mp (hS hx)
    have := Finset.mem_range.mp (hT hy)
    have : x = y := by
      have : (x + r) % k = (y + r) % k := hxy.symm
      exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_right_cancel' r this) ‹x < k› ‹y < k›
    rwa [this]
  · have : (x + r) % k ∈ rotateSet k r S := hST ▸
      Finset.mem_image.mpr ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp this
    have := Finset.mem_range.mp (hT hx)
    have := Finset.mem_range.mp (hS hy)
    have : x = y := by
      have : (x + r) % k = (y + r) % k := hxy.symm
      exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_right_cancel' r this) ‹x < k› ‹y < k›
    rwa [this]

private lemma count_per_rotation (k r : ℕ) (hk : 0 < k) :
    ((Finset.range k).powerset.filter (fun S =>
      S.Nonempty ∧ k ∣ (S.sum (· + 1) + r * S.card))).card =
    b_comb k - 1 := by
  set P := (Finset.range k).powerset
  -- Step 1: The condition is equivalent under rotation
  have hcong : ∀ S ∈ P, (S.Nonempty ∧ k ∣ (S.sum (· + 1) + r * S.card)) ↔
      ((rotateSet k r S).Nonempty ∧ k ∣ (rotateSet k r S).sum (· + 1)) := by
    intro S hS
    have hSsub := Finset.mem_powerset.mp hS
    constructor
    · rintro ⟨hne, hdvd⟩
      exact ⟨rotateSet_nonempty hk hSsub hne, (rotateSet_dvd_iff k r hk S hSsub).mpr hdvd⟩
    · rintro ⟨hne, hdvd⟩
      refine ⟨?_, (rotateSet_dvd_iff k r hk S hSsub).mp hdvd⟩
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      simp [hempty, rotateSet] at hne
  rw [Finset.filter_congr hcong]
  -- Step 2: rotateSet k r is a bijection on P, so |P.filter(Q∘f)| = |P.filter(Q)|
  have hinj := rotateSet_injOn_powerset k r hk
  have hmaps : Set.MapsTo (rotateSet k r) ↑P ↑P := fun S hS =>
    Finset.mem_coe.mpr (Finset.mem_powerset.mpr
      (rotateSet_subset_range hk (Finset.mem_powerset.mp (Finset.mem_coe.mp hS))))
  have hsurj := Finset.surjOn_of_injOn_of_card_le (rotateSet k r) hmaps hinj le_rfl
  set Q := fun S : Finset ℕ => S.Nonempty ∧ k ∣ S.sum (· + 1)
  show (P.filter (Q ∘ rotateSet k r)).card = b_comb k - 1
  have hsrc_inj : Set.InjOn (rotateSet k r) ↑(P.filter (Q ∘ rotateSet k r)) :=
    hinj.mono (fun _ h => (Finset.mem_filter.mp h).1)
  have hcard_eq : (P.filter (Q ∘ rotateSet k r)).card = (P.filter Q).card := by
    rw [← Finset.card_image_of_injOn hsrc_inj]
    congr 1
    ext T
    rw [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨S, hS, rfl⟩
      have := Finset.mem_filter.mp hS
      exact ⟨Finset.mem_powerset.mpr (rotateSet_subset_range hk
        (Finset.mem_powerset.mp this.1)), this.2⟩
    · intro ⟨hTP, hTQ⟩
      obtain ⟨S, hSP, hST⟩ := hsurj (Finset.mem_coe.mpr hTP)
      rw [Finset.mem_coe] at hSP
      exact ⟨S, Finset.mem_filter.mpr ⟨hSP, show Q (rotateSet k r S) by rwa [hST]⟩, hST⟩
  rw [hcard_eq]
  -- Step 3: |P.filter(Q)| = b_comb k - 1
  simp only [Q, b_comb, modSubsets]
  have hmem : ∅ ∈ P.filter (fun S => k ∣ S.sum (· + 1)) :=
    Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, dvd_zero k⟩
  have : (P.filter (fun S => S.Nonempty ∧ k ∣ S.sum (· + 1))).card =
      (P.filter (fun S => k ∣ S.sum (· + 1))).card - 1 := by
    rw [show P.filter (fun S => S.Nonempty ∧ k ∣ S.sum (· + 1)) =
        (P.filter (fun S => k ∣ S.sum (· + 1))).filter Finset.Nonempty from by
      rw [Finset.filter_filter]; congr 1; ext S; exact and_comm]
    rw [show (P.filter (fun S => k ∣ S.sum (· + 1))).filter Finset.Nonempty =
        (P.filter (fun S => k ∣ S.sum (· + 1))).erase ∅ from by
      ext S; simp [Finset.mem_erase, Finset.mem_filter, Finset.nonempty_iff_ne_empty, and_comm]]
    exact Finset.card_erase_of_mem hmem
  exact this

private lemma sum_alpha_eq (k : ℕ) (hk : 0 < k) :
    ∑ S ∈ (Finset.range k).powerset.filter Finset.Nonempty, α k S =
      k * (b_comb k - 1) := by
  set X := (Finset.range k).powerset.filter Finset.Nonempty
  -- α(k, S) = ∑_r indicator
  have hα : ∀ S ∈ X, α k S =
      ∑ r ∈ Finset.range k, if k ∣ (S.sum (· + 1) + r * S.card) then 1 else 0 := by
    intro S _; simp only [α, Finset.card_filter]
  rw [Finset.sum_congr rfl hα, Finset.sum_comm]
  have h_inner : ∀ r ∈ Finset.range k,
      ∑ S ∈ X, (if k ∣ (S.sum (· + 1) + r * S.card) then 1 else 0) = b_comb k - 1 := by
    intro r _
    rw [← Finset.card_filter]
    rw [show X.filter (fun S => k ∣ (S.sum (· + 1) + r * S.card)) =
        (Finset.range k).powerset.filter (fun S =>
          S.Nonempty ∧ k ∣ (S.sum (· + 1) + r * S.card)) from by
      ext S; simp [X, Finset.mem_filter, and_assoc]]
    exact count_per_rotation k r hk
  rw [Finset.sum_congr rfl h_inner, Finset.sum_const, Finset.card_range, smul_eq_mul]

private def reflectSet (k : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.image (fun s => k - 1 - s)

private lemma reflectSet_subset_range {k : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range k) :
    reflectSet k S ⊆ Finset.range k := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
  have := Finset.mem_range.mp (hS hs)
  exact Finset.mem_range.mpr (by omega)

private lemma reflectSet_injOn {k : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range k) :
    Set.InjOn (fun s => k - 1 - s) ↑S := by
  intro a ha b hb hab
  have ha' := Finset.mem_range.mp (hS ha)
  have hb' := Finset.mem_range.mp (hS hb)
  have : k - 1 - a = k - 1 - b := hab
  omega

private lemma reflectSet_card {k : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range k) :
    (reflectSet k S).card = S.card :=
  Finset.card_image_of_injOn (reflectSet_injOn hS)

private lemma reflectSet_dvd_iff {k : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range k) :
    S.card ∣ (reflectSet k S).sum (· + 1) ↔ S.card ∣ S.sum (· + 1) := by
  simp only [reflectSet, Finset.sum_image (reflectSet_injOn hS)]
  have hsub : ∀ s ∈ S, k - 1 - s + 1 = k - s := by
    intro s hs; have := Finset.mem_range.mp (hS hs); omega
  rw [Finset.sum_congr rfl (fun s hs => hsub s hs)]
  have hsum_add : ∑ s ∈ S, (k - s) + ∑ s ∈ S, (s + 1) = (k + 1) * S.card := by
    rw [← Finset.sum_add_distrib, show ∑ s ∈ S, (k - s + (s + 1)) = ∑ _s ∈ S, (k + 1) from
      Finset.sum_congr rfl (fun s hs => by have := Finset.mem_range.mp (hS hs); omega)]
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  set A := ∑ s ∈ S, (k - s)
  set B := ∑ s ∈ S, (s + 1)
  have hdvd_total : S.card ∣ A + B := hsum_add ▸ dvd_mul_left _ _
  exact ⟨fun h => (Nat.dvd_add_right h).mp hdvd_total,
    fun h => (Nat.dvd_add_left h).mp hdvd_total⟩

/-- Reflection bijects {S : 0∈S, |S||sum_S} with maxKIntMeanSubsets. -/
private lemma reflect_zero_eq_maxK (k : ℕ) (hk : 0 < k) :
    ((Finset.range k).powerset.filter (fun S =>
      0 ∈ S ∧ S.card ∣ S.sum (· + 1))).card = (maxKIntMeanSubsets k).card := by
  -- reflectSet is an injective endofunction on powerset(range k)
  -- mapping 0 to k-1 and preserving |S| | sum_S
  have hinj : Set.InjOn (reflectSet k) ↑((Finset.range k).powerset) := by
    intro S hS T hT hST
    rw [Finset.mem_coe, Finset.mem_powerset] at hS hT
    ext x; constructor <;> intro hx
    · have : k - 1 - x ∈ reflectSet k T := hST ▸ Finset.mem_image.mpr ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp this
      have hxk := Finset.mem_range.mp (hS hx)
      have hyk := Finset.mem_range.mp (hT hy)
      have : x = y := by omega
      rwa [this]
    · have : k - 1 - x ∈ reflectSet k S := hST ▸ Finset.mem_image.mpr ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp this
      have hxk := Finset.mem_range.mp (hT hx)
      have hyk := Finset.mem_range.mp (hS hy)
      have : x = y := by omega
      rwa [this]
  have hmaps : Set.MapsTo (reflectSet k) ↑(Finset.range k).powerset
      ↑(Finset.range k).powerset := fun S hS =>
    Finset.mem_coe.mpr (Finset.mem_powerset.mpr (reflectSet_subset_range
      (Finset.mem_powerset.mp (Finset.mem_coe.mp hS))))
  have hsurj := Finset.surjOn_of_injOn_of_card_le (reflectSet k) hmaps hinj le_rfl
  set P := (Finset.range k).powerset
  -- reflection maps "0 ∈ S" to "k-1 ∈ S" and preserves divisibility
  have hcond : ∀ S ∈ P, (0 ∈ S ∧ S.card ∣ S.sum (· + 1)) ↔
      ((k - 1) ∈ reflectSet k S ∧ (reflectSet k S).card ∣ (reflectSet k S).sum (· + 1)) := by
    intro S hS
    have hSsub := Finset.mem_powerset.mp hS
    constructor
    · rintro ⟨h0, hdvd⟩
      refine ⟨Finset.mem_image.mpr ⟨0, h0, by omega⟩,
        (reflectSet_card hSsub) ▸ (reflectSet_dvd_iff hSsub).mpr hdvd⟩
    · rintro ⟨hk1, hdvd⟩
      refine ⟨?_, (reflectSet_dvd_iff hSsub).mp ((reflectSet_card hSsub) ▸ hdvd)⟩
      obtain ⟨s, hs, hsk⟩ := Finset.mem_image.mp hk1
      have := Finset.mem_range.mp (hSsub hs)
      have : s = 0 := by omega
      rwa [this] at hs
  -- Same card-image argument as count_per_rotation
  rw [Finset.filter_congr hcond]
  have hsrc_inj : Set.InjOn (reflectSet k) ↑(P.filter (fun S =>
      (k - 1) ∈ reflectSet k S ∧ (reflectSet k S).card ∣ (reflectSet k S).sum (· + 1))) :=
    hinj.mono (fun _ h => (Finset.mem_filter.mp h).1)
  rw [← Finset.card_image_of_injOn hsrc_inj]
  congr 1
  ext T; rw [Finset.mem_image, maxKIntMeanSubsets, Finset.mem_filter]
  constructor
  · rintro ⟨S, hS, rfl⟩
    have := Finset.mem_filter.mp hS
    exact ⟨Finset.mem_powerset.mpr (reflectSet_subset_range
      (Finset.mem_powerset.mp this.1)), this.2⟩
  · intro ⟨hTP, hTcond⟩
    obtain ⟨S, hSP, hST⟩ := hsurj (Finset.mem_coe.mpr hTP)
    rw [Finset.mem_coe] at hSP
    exact ⟨S, Finset.mem_filter.mpr ⟨hSP, hST ▸ hTcond⟩, hST⟩

/-- β can be evaluated using card_filter_dvd_add_mul. -/
private lemma beta_eq_gcd (k : ℕ) (S : Finset ℕ) (hne : S.Nonempty) :
    β k S = if Nat.gcd k S.card ∣ S.sum (· + 1) then Nat.gcd k S.card else 0 := by
  simp only [β]
  have hcard : 0 < S.card := Finset.card_pos.mpr hne
  rw [show ((Finset.range S.card).filter (fun j => S.card ∣ (S.sum (· + 1) + k * j))).card =
      if Nat.gcd k S.card ∣ S.sum (· + 1) then Nat.gcd k S.card else 0 from by
    exact card_filter_dvd_add_mul (S.sum (· + 1)) k S.card hcard]

/-- α can be evaluated using card_filter_dvd_add_mul. -/
private lemma alpha_eq_gcd (k : ℕ) (S : Finset ℕ) (hk : 0 < k) :
    α k S = if Nat.gcd S.card k ∣ S.sum (· + 1) then Nat.gcd S.card k else 0 := by
  simp only [α]
  have : ∀ r, S.sum (· + 1) + r * S.card = S.sum (· + 1) + S.card * r := by
    intro r; ring
  simp_rw [this]
  exact card_filter_dvd_add_mul (S.sum (· + 1)) S.card k hk

private lemma sum_beta_eq_sum_alpha (k : ℕ) (hk : 0 < k) :
    ∑ S ∈ (Finset.range k).powerset.filter Finset.Nonempty, β k S =
    ∑ S ∈ (Finset.range k).powerset.filter Finset.Nonempty, α k S := by
  apply Finset.sum_congr rfl
  intro S hS
  exact (alpha_eq_beta k S hk (Finset.mem_filter.mp hS).2).symm

/-- The per-k identity: #{nonempty S ⊆ {1,...,k} : k|sum(S)} = #{S ⊆ {1,...,k} : k∈S, |S||sum(S)}.

This is the hard combinatorial content. The proof proceeds by showing
∑_S α(k,S) = ∑_S β(k,S) (from alpha_eq_beta) and evaluating each side:
- ∑ α = k·(b_comb k - 1) via rotation double-counting (sum_alpha_eq)
- ∑ β = k·maxKIntMean via host-element decomposition with rotation uniformity
  and reflection bijection (reflect_zero_eq_maxK)

The host decomposition: β(k,S) = ∑_{e∈S} [|S| | (sum_S + k·rank(e,S))].
Rotation by 1 cyclically permutes host elements preserving the condition.
Each host contributes equally; host 0 count = maxKIntMean by reflection. -/
private def hostSet (k e : ℕ) : Finset (Finset ℕ) :=
  ((Finset.range k).powerset).filter (fun S =>
    e ∈ S ∧ S.card ∣ (S.sum (· + 1) + k * (S.filter (· < e)).card))

private lemma rotateSet_sum_eq (k r : ℕ) (hk : 0 < k) (S : Finset ℕ)
    (hS : S ⊆ Finset.range k) :
    S.sum (· + 1) + r * S.card =
      (rotateSet k r S).sum (· + 1) + k * (∑ s ∈ S, (s + r) / k) := by
  simp only [rotateSet, Finset.sum_image (rotateSet_injOn hk hS)]
  have h_term : ∀ s, s + r + 1 = (s + r) % k + 1 + k * ((s + r) / k) := by
    intro s; have := Nat.div_add_mod (s + r) k; omega
  trans ∑ s ∈ S, (s + r + 1)
  · trans (∑ s ∈ S, (s + 1)) + ∑ _s ∈ S, r
    · congr 1; rw [Finset.sum_const, smul_eq_mul, mul_comm]
    · rw [← Finset.sum_add_distrib]; congr 1; ext s; omega
  · rw [Finset.sum_congr rfl (fun s _ => h_term s), Finset.sum_add_distrib, ← Finset.mul_sum]

private lemma rotateSet_host_forward {k : ℕ} (hk : 0 < k) {S : Finset ℕ}
    (hS : S ⊆ Finset.range k) {e : ℕ} (he : e ∈ S)
    (hdvd : S.card ∣ (S.sum (· + 1) + k * (S.filter (· < e)).card)) :
    let S' := rotateSet k 1 S
    (e + 1) % k ∈ S' ∧
    S'.card ∣ (S'.sum (· + 1) + k * (S'.filter (· < (e + 1) % k)).card) := by
  intro S'
  have he_lt : e < k := Finset.mem_range.mp (hS he)
  have hmem : (e + 1) % k ∈ S' :=
    Finset.mem_image.mpr ⟨e, he, rfl⟩
  refine ⟨hmem, ?_⟩
  have hcard_eq : S'.card = S.card := rotateSet_card hk hS
  rw [hcard_eq]
  -- Suffices: show the target expression ≡ hdvd's LHS (mod S.card)
  by_cases he_max : e = k - 1
  · -- Case e = k-1: (e+1)%k = 0, rank(0, S') = 0
    subst he_max
    have hmod : (k - 1 + 1) % k = 0 := Nat.sub_add_cancel hk ▸ Nat.mod_self k
    rw [hmod, Finset.filter_false_of_mem (fun x _ => Nat.not_lt_zero x)]
    simp only [Finset.card_empty, Nat.mul_zero, Nat.add_zero]
    -- Goal: S.card ∣ S'.sum (· + 1)
    -- From rotateSet_sum_eq: S.sum(·+1) + S.card = S'.sum(·+1) + k * (∑ s ∈ S, (s+1)/k)
    have hsum := rotateSet_sum_eq k 1 hk S hS
    simp only [one_mul] at hsum
    -- ∑ s ∈ S, (s+1)/k = 1 when k-1 ∈ S and all s < k
    have hdiv_sum : ∑ s ∈ S, (s + 1) / k = 1 := by
      have h_val : ∀ s ∈ S, (s + 1) / k = if s = k - 1 then 1 else 0 := by
        intro s hs
        have hs_lt : s < k := Finset.mem_range.mp (hS hs)
        split
        · next h => subst h; exact Nat.div_eq_of_lt_le (by omega) (by omega)
        · next h => exact Nat.div_eq_of_lt (by omega)
      rw [Finset.sum_congr rfl h_val, Finset.sum_ite_eq' S (k - 1)]
      simp [he]
    rw [hdiv_sum, Nat.mul_one] at hsum
    -- hsum: S.sum(·+1) + S.card = S'.sum(·+1) + k
    -- hdvd: S.card ∣ (S.sum(·+1) + k * (S.filter (· < k-1)).card)
    -- rank(k-1, S) = S.card - 1
    have hrank : (S.filter (· < k - 1)).card = S.card - 1 := by
      have : S.filter (· < k - 1) = S.erase (k - 1) := by
        ext x; simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · intro ⟨hx, hlt⟩; exact ⟨by omega, hx⟩
        · intro ⟨hne, hx⟩
          have hx_lt : x < k := Finset.mem_range.mp (hS hx)
          exact ⟨hx, Nat.lt_of_le_of_ne (by omega) hne⟩
      rw [this, Finset.card_erase_of_mem he]
    rw [hrank] at hdvd
    -- hsum: S.sum(·+1) + S.card = S'.sum(·+1) + k
    -- hdvd: S.card ∣ S.sum(·+1) + k * (S.card - 1)
    -- Goal: S.card ∣ S'.sum(·+1)
    have hcard_pos : 0 < S.card := Finset.card_pos.mpr ⟨_, he⟩
    refine Int.ofNat_dvd.mp ?_
    have hsum_int : (S.sum (· + 1) : ℤ) + S.card = S'.sum (· + 1) + k := by
      exact_mod_cast hsum
    have hdvd_int : (S.card : ℤ) ∣ ((S.sum (· + 1) : ℤ) + k * (S.card - 1)) := by
      have h1 : 1 ≤ S.card := hcard_pos
      have h2 : (k * (↑S.card - 1 : ℤ)) = ↑(k * (S.card - 1)) := by
        rw [Nat.cast_mul]; congr 1
        exact (Int.ofNat_sub h1).symm
      rw [h2]; exact_mod_cast hdvd
    -- In ℤ: S'.sum(·+1) = S.sum(·+1) + S.card - k, and S.card ∣ S.sum(·+1) + k*(S.card - 1)
    -- S.sum(·+1) + k*(S.card-1) = S'.sum(·+1) + k - S.card + k*(S.card-1)
    --                            = S'.sum(·+1) + k*S.card - S.card
    --                            = S'.sum(·+1) + (k-1)*S.card
    -- So S.card ∣ S'.sum(·+1) + (k-1)*S.card and S.card ∣ (k-1)*S.card → S.card ∣ S'.sum(·+1)
    have : (S.sum (· + 1) : ℤ) + ↑k * (↑S.card - 1) = S'.sum (· + 1) + (↑k - 1) * ↑S.card := by
      linarith
    rw [this, add_comm] at hdvd_int
    exact (dvd_add_right (dvd_mul_left (↑S.card : ℤ) (↑k - 1))).mp hdvd_int
  · -- Case e < k-1: (e+1)%k = e+1 (no wrapping)
    have he_lt2 : e + 1 < k := by omega
    have hmod : (e + 1) % k = e + 1 := Nat.mod_eq_of_lt he_lt2
    rw [hmod]
    -- Goal: S.card ∣ S'.sum(·+1) + k * (S'.filter (· < e+1)).card
    -- Strategy: lift to ℤ, show target = S.sum(·+1) + k*rank(e,S) + S.card
    -- Step 1: sum identity from rotateSet_sum_eq
    have hsum := rotateSet_sum_eq k 1 hk S hS
    simp only [one_mul] at hsum
    change S.sum (· + 1) + S.card =
      S'.sum (· + 1) + k * (∑ s ∈ S, (s + 1) / k) at hsum
    -- Step 2: rank identity
    have hrank_rot : (S'.filter (· < e + 1)).card =
        (S.filter (· < e)).card + (∑ s ∈ S, (s + 1) / k) := by
      -- S'.filter(· < e+1) has same card as S.filter(fun s => (s+1)%k < e+1) by injectivity
      have hinj := @rotateSet_injOn k 1 hk S hS
      have hcard_filter : (S'.filter (· < e + 1)).card =
          (S.filter (fun s => (s + 1) % k < e + 1)).card := by
        rw [show S' = S.image (fun s => (s + 1) % k) from rfl]
        rw [Finset.filter_image]
        exact Finset.card_image_of_injOn (hinj.mono (fun s hs =>
          (Finset.mem_filter.mp hs).1))
      rw [hcard_filter]
      -- For s ∈ S (so s < k): (s+1)%k < e+1 ⟺ s < e ∨ s = k-1
      have h_cond : ∀ s ∈ S, ((s + 1) % k < e + 1) = (s < e ∨ s = k - 1) := by
        intro s hs
        have hs_lt : s < k := Finset.mem_range.mp (hS hs)
        ext; constructor
        · intro h
          by_cases hsk : s = k - 1
          · exact Or.inr hsk
          · left; have : (s + 1) % k = s + 1 := Nat.mod_eq_of_lt (by omega)
            omega
        · intro h
          rcases h with hlt | heq
          · have : (s + 1) % k = s + 1 := Nat.mod_eq_of_lt (by omega)
            omega
          · subst heq
            rw [show k - 1 + 1 = k from by omega, Nat.mod_self]
            omega
      rw [show (S.filter (fun s => (s + 1) % k < e + 1)) =
          S.filter (fun s => s < e ∨ s = k - 1) from
        Finset.filter_congr (fun s hs => (h_cond s hs).symm ▸ Iff.rfl)]
      rw [show S.filter (fun s => s < e ∨ s = k - 1) =
          S.filter (· < e) ∪ S.filter (· = k - 1) from
        Finset.filter_or _ _ _]
      have h_disj : Disjoint (S.filter (· < e)) (S.filter (· = k - 1)) :=
        Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by omega)
      rw [Finset.card_union_of_disjoint h_disj]
      congr 1
      -- ∑ s ∈ S, (s+1)/k = (S.filter (· = k-1)).card
      have h_val : ∀ s ∈ S, (s + 1) / k = if s = k - 1 then 1 else 0 := by
        intro s hs
        have hs_lt : s < k := Finset.mem_range.mp (hS hs)
        split
        · next h => subst h; exact Nat.div_eq_of_lt_le (by omega) (by omega)
        · next h => exact Nat.div_eq_of_lt (by omega)
      rw [Finset.sum_congr rfl h_val, Finset.sum_boole, Finset.filter_eq']
      split
      · simp
      · simp_all
    -- Now close the goal using hrank_rot and hsum
    -- Goal: S.card ∣ S'.sum(·+1) + k * (S'.filter (· < e+1)).card
    rw [hrank_rot]
    -- Goal: S.card ∣ S'.sum(·+1) + k * ((S.filter (· < e)).card + ∑ s ∈ S, (s+1)/k)
    -- = S'.sum(·+1) + k*(S.filter(·<e)).card + k*∑(s+1)/k
    -- From hsum: S.sum(·+1) + S.card = S'.sum(·+1) + k*∑(s+1)/k
    -- So S'.sum(·+1) + k*∑(s+1)/k = S.sum(·+1) + S.card
    -- Target = S.sum(·+1) + S.card + k*(S.filter(·<e)).card - k*∑(s+1)/k + k*∑(s+1)/k
    --        = S.sum(·+1) + k*(S.filter(·<e)).card + S.card
    -- Lift to ℤ
    refine Int.ofNat_dvd.mp ?_
    have hsum_int : (S.sum (· + 1) : ℤ) + S.card =
        S'.sum (· + 1) + k * (∑ s ∈ S, (s + 1) / k) := by exact_mod_cast hsum
    have hdvd_int : (S.card : ℤ) ∣ (↑(S.sum (· + 1)) + ↑k * ↑(S.filter (· < e)).card) := by
      exact_mod_cast hdvd
    -- Target in ℤ: S.card ∣ S'.sum(·+1) + k * ((S.filter(·<e)).card + ∑(s+1)/k)
    -- = S'.sum(·+1) + k*(S.filter(·<e)).card + k*∑(s+1)/k
    -- = (from hsum) S.sum(·+1) + S.card + k*(S.filter(·<e)).card - k*∑(s+1)/k + k*∑(s+1)/k ... hmm
    -- Actually: S'.sum(·+1) + k*∑(s+1)/k = S.sum(·+1) + S.card (from hsum)
    -- So target = S.sum(·+1) + S.card + k*(S.filter(·<e)).card - k*∑(s+1)/k + k*∑(s+1)/k ... no
    -- More directly: target = S'.sum(·+1) + k*((S.filter(·<e)).card + ∑(s+1)/k)
    --   = S'.sum(·+1) + k*(S.filter(·<e)).card + k*∑(s+1)/k
    -- And S'.sum(·+1) + k*∑(s+1)/k = S.sum(·+1) + S.card (hsum rewritten)
    -- So target = S.sum(·+1) + S.card + k*(S.filter(·<e)).card
    --           = (S.sum(·+1) + k*(S.filter(·<e)).card) + S.card
    -- S.card ∣ first term (hdvd) and S.card ∣ S.card, done.
    have : (↑(S'.sum (· + 1) + k * ((S.filter (· < e)).card + ∑ s ∈ S, (s + 1) / k)) : ℤ) =
        (S.sum (· + 1) + k * (S.filter (· < e)).card : ℤ) + S.card := by
      push_cast; linarith
    rw [this]
    exact dvd_add hdvd_int (dvd_refl _)

private lemma rotateSet_host_backward {k : ℕ} (hk : 0 < k) {S : Finset ℕ}
    (hS : S ⊆ Finset.range k) {e : ℕ} (he_lt : e < k)
    {e' : ℕ} (he' : e' = (e + 1) % k) (he'_mem : e' ∈ S)
    (hdvd : S.card ∣ (S.sum (· + 1) + k * (S.filter (· < e')).card)) :
    let T := rotateSet k (k - 1) S
    e ∈ T ∧
    T.card ∣ (T.sum (· + 1) + k * (T.filter (· < e)).card) := by
  intro T
  have he'_lt : e' < k := he' ▸ Nat.mod_lt _ hk
  -- Membership: (e' + (k-1)) % k = e
  have hmem_eq : (e' + (k - 1)) % k = e := by
    subst he'
    by_cases h : e + 1 = k
    · rw [h, Nat.mod_self, zero_add, show k - 1 = e from by omega, Nat.mod_eq_of_lt he_lt]
    · have h1 : (e + 1) % k = e + 1 := Nat.mod_eq_of_lt (by omega)
      rw [h1, show e + 1 + (k - 1) = e + k from by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt he_lt]
  have hmem : e ∈ T := hmem_eq ▸ Finset.mem_image.mpr ⟨e', he'_mem, rfl⟩
  refine ⟨hmem, ?_⟩
  have hcard_eq : T.card = S.card := rotateSet_card hk hS
  rw [hcard_eq]
  -- Sum identity from rotateSet_sum_eq with r = k-1
  have hsum := rotateSet_sum_eq k (k - 1) hk S hS
  change S.sum (· + 1) + (k - 1) * S.card = T.sum (· + 1) + k * (∑ s ∈ S, (s + (k - 1)) / k) at hsum
  -- For s < k: (s+k-1)/k = 1 if s ≥ 1, 0 if s = 0
  have hdiv_sum : ∀ s ∈ S, (s + (k - 1)) / k = if s = 0 then 0 else 1 := by
    intro s hs
    have hs_lt : s < k := Finset.mem_range.mp (hS hs)
    split
    · next h => subst h; exact Nat.div_eq_of_lt (by omega)
    · next h => exact Nat.div_eq_of_lt_le (by omega) (by omega)
  -- Same technique as forward: lift to ℤ, show target ≡ source (mod S.card)
  have hcard_pos : 0 < S.card := Finset.card_pos.mpr ⟨_, he'_mem⟩
  -- Rank identity for backward rotation:
  -- T.filter(· < e) corresponds to {s ∈ S : (s+k-1)%k < e}
  have hinj := @rotateSet_injOn k (k - 1) hk S hS
  have hrank_rot : (T.filter (· < e)).card =
      (S.filter (fun s => (s + (k - 1)) % k < e)).card := by
    rw [show T = S.image (fun s => (s + (k - 1)) % k) from rfl, Finset.filter_image]
    exact Finset.card_image_of_injOn (hinj.mono (fun s hs =>
      (Finset.mem_filter.mp hs).1))
  -- For s < k: (s+k-1)%k < e iff 1 ≤ s ∧ s ≤ e (when e < k)
  -- because (s+k-1)%k = s-1 for s ≥ 1, and k-1 for s = 0
  -- and k-1 < e is impossible (since e < k, we'd need e > k-1, i.e. e ≥ k)
  have h_rank_cond : ∀ s ∈ S, ((s + (k - 1)) % k < e) =
      (1 ≤ s ∧ s ≤ e) := by
    intro s hs
    have hs_lt : s < k := Finset.mem_range.mp (hS hs)
    ext; constructor
    · intro h
      by_cases hs0 : s = 0
      · subst hs0; rw [show 0 + (k - 1) = k - 1 from by omega, Nat.mod_eq_of_lt (by omega)] at h
        omega
      · have : (s + (k - 1)) % k = s - 1 := by
          rw [show s + (k - 1) = s - 1 + k from by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
        rw [this] at h; omega
    · intro ⟨h1, h2⟩
      have : (s + (k - 1)) % k = s - 1 := by
        rw [show s + (k - 1) = s - 1 + k from by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
      rw [this]; omega
  rw [hrank_rot, show (S.filter (fun s => (s + (k - 1)) % k < e)) =
      S.filter (fun s => 1 ≤ s ∧ s ≤ e) from
    Finset.filter_congr (fun s hs => (h_rank_cond s hs).symm ▸ Iff.rfl)]
  -- Identity: ∑(s+k-1)/k = (S.filter (· ≠ 0)).card
  have h_divsum_eq : (∑ s ∈ S, (s + (k - 1)) / k) = (S.filter (· ≠ 0)).card := by
    rw [Finset.sum_congr rfl (fun s hs => hdiv_sum s hs)]
    simp only [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, smul_eq_mul, mul_one,
      zero_add, Finset.filter_ne']
  -- Case split on e'
  by_cases he'_zero : e' = 0
  · -- e' = 0 means e = k-1, 0 ∈ S
    have he_eq : e = k - 1 := by
      subst he'; by_cases h : e + 1 = k
      · omega
      · have : (e + 1) % k = e + 1 := Nat.mod_eq_of_lt (by omega)
        omega
    -- #{s ∈ S : 1 ≤ s ≤ k-1} = #{s ∈ S : s ≠ 0} = ∑(s+k-1)/k
    have hrank_target : (S.filter (fun s => 1 ≤ s ∧ s ≤ e)).card =
        ∑ s ∈ S, (s + (k - 1)) / k := by
      rw [h_divsum_eq]; congr 1; ext s; simp only [Finset.mem_filter]
      constructor
      · intro ⟨hs, h1, _h2⟩; exact ⟨hs, by omega⟩
      · intro ⟨hs, hne⟩
        have hs_lt : s < k := Finset.mem_range.mp (hS hs)
        exact ⟨hs, by omega, by omega⟩
    rw [hrank_target]
    -- Goal: S.card ∣ T.sum(·+1) + k * ∑(s+k-1)/k
    -- From hsum: T.sum(·+1) + k*∑(s+k-1)/k = S.sum(·+1) + (k-1)*S.card
    -- hdvd with e'=0: S.card ∣ S.sum(·+1) + k*0 = S.sum(·+1)
    have hrank_e' : (S.filter (· < e')).card = 0 := by
      rw [he'_zero]; exact Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr
        (fun x _ => Nat.not_lt_zero x))
    rw [hrank_e', Nat.mul_zero, Nat.add_zero] at hdvd
    -- hdvd: S.card ∣ S.sum(·+1)
    -- hsum: S.sum(·+1) + (k-1)*S.card = T.sum(·+1) + k*∑(s+k-1)/k
    have h_target_eq : T.sum (· + 1) + k * ∑ s ∈ S, (s + (k - 1)) / k =
        S.sum (· + 1) + (k - 1) * S.card := by linarith
    rw [h_target_eq]
    exact Nat.dvd_add hdvd (Nat.dvd_mul_left S.card _)
  · -- e' > 0 (so e < k-1 and e' = e+1): target + S.card = hdvd_LHS
    have he_lt2 : e + 1 < k := by
      by_contra h; push Not at h
      have : (e + 1) % k = 0 := by rw [show e + 1 = k from by omega]; exact Nat.mod_self k
      exact he'_zero (he' ▸ this)
    have he'_eq : e' = e + 1 := he' ▸ Nat.mod_eq_of_lt he_lt2
    -- Key ℕ identity: target + S.card = hdvd_LHS
    -- i.e. T.sum(·+1) + k*#{1≤s≤e} + S.card = S.sum(·+1) + k*(S.filter(·<e')).card
    -- Proof: both sides equal S.sum(·+1) + k*(S.filter(·≤e)).card
    -- LHS: T.sum(·+1) + k*#{1≤s≤e} + S.card
    --     = (S.sum(·+1) + (k-1)*S.card - k*divsum) + k*#{1≤s≤e} + S.card (from hsum)
    -- Prove in ℕ: target + S.card = hdvd_LHS (then conclude divisibility)
    -- Filter identities
    have hrank_rel : (S.filter (· < e')).card = (S.filter (· ≤ e)).card := by
      congr 1; ext s; simp only [Finset.mem_filter]
      exact and_congr_right (fun _ => by rw [he'_eq]; omega)
    have h_filter_split : (S.filter (fun s => 1 ≤ s ∧ s ≤ e)).card +
        (if (0 : ℕ) ∈ S then 1 else 0) = (S.filter (· ≤ e)).card := by
      by_cases h0 : (0 : ℕ) ∈ S
      · simp only [h0, if_true]
        have hdisj : Disjoint (S.filter (fun s => 1 ≤ s ∧ s ≤ e)) {0} := by
          simp [Finset.disjoint_singleton_right, Finset.mem_filter]
        have hunion : S.filter (· ≤ e) = S.filter (fun s => 1 ≤ s ∧ s ≤ e) ∪ {0} := by
          ext s; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton]
          constructor
          · intro ⟨hs, hle⟩
            by_cases h : s = 0
            · right; exact h
            · left; exact ⟨hs, by omega, hle⟩
          · rintro (⟨hs, _, hle⟩ | rfl)
            · exact ⟨hs, hle⟩
            · exact ⟨h0, Nat.zero_le _⟩
        rw [hunion, Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
      · simp only [h0, if_false, Nat.add_zero]
        congr 1; ext s; simp only [Finset.mem_filter]
        constructor
        · intro ⟨hs, _, hle⟩; exact ⟨hs, hle⟩
        · intro ⟨hs, hle⟩
          have hne : s ≠ 0 := fun h => h0 (h ▸ hs)
          exact ⟨hs, by omega, hle⟩
    -- Also: divsum + [0∈S] = S.card
    have h_divsum_card : (∑ s ∈ S, (s + (k - 1)) / k) + (if (0 : ℕ) ∈ S then 1 else 0) =
        S.card := by
      rw [h_divsum_eq]
      by_cases h0 : (0 : ℕ) ∈ S
      · simp only [h0, if_true]
        have : S.filter (· ≠ 0) = S.erase 0 := by ext s; simp [Finset.mem_erase, and_comm]
        rw [this]; exact Finset.card_erase_add_one h0
      · simp only [h0, if_false, Nat.add_zero]
        congr 1; ext s; simp only [Finset.mem_filter]
        exact ⟨fun ⟨hs, _⟩ => hs, fun hs => ⟨hs, fun h => h0 (h ▸ hs)⟩⟩
    -- Prove in ℕ: T.sum(·+1) + k*f + S.card = S.sum(·+1) + k*r
    have h_nat : T.sum (· + 1) + k * (S.filter (fun s => 1 ≤ s ∧ s ≤ e)).card + S.card =
        S.sum (· + 1) + k * (S.filter (· < e')).card := by
      nlinarith [Nat.sub_add_cancel hk, Nat.mul_sub_one k S.card,
        h_filter_split, h_divsum_card, hrank_rel]
    have h3 : S.card ∣ (T.sum (· + 1) + k * (S.filter (fun s => 1 ≤ s ∧ s ≤ e)).card + S.card) :=
      h_nat ▸ hdvd
    rw [show T.sum (· + 1) + k * (S.filter (fun s => 1 ≤ s ∧ s ≤ e)).card + S.card =
        S.card + (T.sum (· + 1) + k * (S.filter (fun s => 1 ≤ s ∧ s ≤ e)).card) from by omega] at h3
    exact (Nat.dvd_add_right (dvd_refl S.card)).mp h3

private lemma host_rotation (k : ℕ) (hk : 0 < k) (e : ℕ) (he : e < k) :
    (hostSet k e).card = (hostSet k ((e + 1) % k)).card := by
  set e' := (e + 1) % k
  apply le_antisymm
  · have h_inj : Set.InjOn (rotateSet k 1) ↑(hostSet k e) :=
      (rotateSet_injOn_powerset k 1 hk).mono (fun S hS => by
        simp only [hostSet, Finset.mem_filter, Finset.mem_coe] at hS; exact hS.1)
    calc (hostSet k e).card
        = ((hostSet k e).image (rotateSet k 1)).card :=
          (Finset.card_image_of_injOn h_inj).symm
      _ ≤ (hostSet k e').card := Finset.card_le_card (fun T hT => by
          obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
          simp only [hostSet, Finset.mem_filter, Finset.mem_powerset] at hS ⊢
          exact ⟨rotateSet_subset_range hk hS.1,
            rotateSet_host_forward hk hS.1 hS.2.1 hS.2.2⟩)
  · have h_inj : Set.InjOn (rotateSet k (k - 1)) ↑(hostSet k e') :=
      (rotateSet_injOn_powerset k (k - 1) hk).mono (fun S hS => by
        simp only [hostSet, Finset.mem_filter, Finset.mem_coe] at hS; exact hS.1)
    calc (hostSet k e').card
        = ((hostSet k e').image (rotateSet k (k - 1))).card :=
          (Finset.card_image_of_injOn h_inj).symm
      _ ≤ (hostSet k e).card := Finset.card_le_card (fun T hT => by
          obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
          simp only [hostSet, Finset.mem_filter, Finset.mem_powerset] at hS ⊢
          exact ⟨rotateSet_subset_range hk hS.1,
            rotateSet_host_backward hk hS.1 he rfl hS.2.1 hS.2.2⟩)

private lemma hostSet_zero_eq (k : ℕ) (hk : 0 < k) :
    (hostSet k 0).card = (maxKIntMeanSubsets k).card := by
  have h1 : hostSet k 0 = (Finset.range k).powerset.filter (fun S =>
      0 ∈ S ∧ S.card ∣ S.sum (· + 1)) := by
    simp only [hostSet]
    congr 1; ext S
    simp
  rw [h1]
  exact reflect_zero_eq_maxK k hk

private lemma hostSet_card_const (k : ℕ) (hk : 0 < k) (e : ℕ) (he : e < k) :
    (hostSet k e).card = (maxKIntMeanSubsets k).card := by
  have h0 := hostSet_zero_eq k hk
  suffices (hostSet k e).card = (hostSet k 0).card by rw [this, h0]
  induction e with
  | zero => rfl
  | succ n ih =>
    have hn : n < k := by omega
    have hmod : (n + 1) % k = n + 1 := Nat.mod_eq_of_lt (by omega)
    rw [← hmod, ← host_rotation k hk n hn, ih hn]

private lemma beta_eq_host_filter (k : ℕ) (S : Finset ℕ) (_hS : S ⊆ Finset.range k) :
    β k S = (S.filter (fun e => S.card ∣ (S.sum (· + 1) + k * (S.filter (· < e)).card))).card := by
  simp only [β]
  set rank := fun e => (S.filter (· < e)).card
  -- rank is strictly monotone on S, hence injective
  have h_mono : ∀ a ∈ S, ∀ b ∈ S, a < b → rank a < rank b := by
    intro a ha b _ hlt
    exact Finset.card_lt_card ⟨Finset.monotone_filter_right S (by intro x; omega),
      Finset.not_subset.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hlt⟩, by simp⟩⟩
  have h_inj : Set.InjOn rank ↑S := by
    intro a ha b hb hab
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact absurd hab (Nat.ne_of_lt (h_mono a ha b hb hlt))
    · exact heq
    · exact absurd hab.symm (Nat.ne_of_lt (h_mono b hb a ha hgt))
  have h_lt : ∀ e ∈ S, rank e < S.card :=
    fun e he => Finset.card_lt_card ⟨Finset.filter_subset _ S,
      Finset.not_subset.mpr ⟨e, he, by simp⟩⟩
  have h_image : S.image rank = Finset.range S.card :=
    Finset.eq_of_subset_of_card_le
      (fun j hj => Finset.mem_range.mpr (by
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj; exact h_lt e he))
      (by rw [Finset.card_range, Finset.card_image_of_injOn h_inj])
  rw [← h_image, Finset.filter_image, Finset.card_image_of_injOn
    (h_inj.mono (fun e he => (Finset.mem_filter.mp he).1))]

private lemma sum_beta_as_hostSet (k : ℕ) (_hk : 0 < k) :
    ∑ S ∈ (Finset.range k).powerset.filter Finset.Nonempty, β k S =
    ∑ e ∈ Finset.range k, (hostSet k e).card := by
  set P := (Finset.range k).powerset.filter Finset.Nonempty
  have hP : ∀ S ∈ P, S ⊆ Finset.range k := fun S hS =>
    Finset.mem_powerset.mp ((Finset.mem_filter.mp hS).1)
  -- Step 1: rewrite β using beta_eq_host_filter
  conv_lhs => rw [Finset.sum_congr rfl (fun S hS => beta_eq_host_filter k S (hP S hS))]
  -- Step 2: extend inner card_filter to sum over range k
  have hlhs : ∀ S ∈ P, (S.filter (fun e =>
      S.card ∣ (S.sum (· + 1) + k * (S.filter (· < e)).card))).card =
      ∑ e ∈ Finset.range k, if e ∈ S ∧
        S.card ∣ (S.sum (· + 1) + k * (S.filter (· < e)).card) then 1 else 0 := by
    intro S hSP
    rw [← Finset.card_filter]; congr 1; ext e
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun ⟨he, hd⟩ => ⟨Finset.mem_range.mp (hP S hSP he), he, hd⟩,
      fun ⟨_, he, hd⟩ => ⟨he, hd⟩⟩
  conv_lhs => rw [Finset.sum_congr rfl hlhs]
  rw [Finset.sum_comm]
  simp_rw [← Finset.card_filter]
  -- Now LHS = ∑_e (P.filter (fun S => e ∈ S ∧ cond S e)).card
  -- RHS = ∑_e (hostSet k e).card
  congr 1; ext e; congr 1
  ext S; simp only [Finset.mem_filter, hostSet, P]
  constructor
  · intro ⟨⟨hpow, hne⟩, he, hdvd⟩
    exact ⟨hpow, he, hdvd⟩
  · intro ⟨hpow, he, hdvd⟩
    exact ⟨⟨hpow, ⟨_, he⟩⟩, he, hdvd⟩


theorem zumkeller_identity (k : ℕ) (hk : 0 < k) :
    b_comb k - 1 = (maxKIntMeanSubsets k).card := by
  have h_sum_beta : ∑ S ∈ (Finset.range k).powerset.filter Finset.Nonempty, β k S =
      k * (maxKIntMeanSubsets k).card := by
    rw [sum_beta_as_hostSet k hk]
    rw [Finset.sum_congr rfl (fun e he => hostSet_card_const k hk e (Finset.mem_range.mp he))]
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h_sum_alpha : ∑ S ∈ (Finset.range k).powerset.filter Finset.Nonempty, α k S =
      k * (b_comb k - 1) := sum_alpha_eq k hk
  have h_eq : ∑ S ∈ (Finset.range k).powerset.filter Finset.Nonempty, β k S =
      ∑ S ∈ (Finset.range k).powerset.filter Finset.Nonempty, α k S :=
    sum_beta_eq_sum_alpha k hk
  have : k * (b_comb k - 1) = k * (maxKIntMeanSubsets k).card := by linarith
  exact Nat.eq_of_mul_eq_mul_left hk this

end StepA

end A051293
