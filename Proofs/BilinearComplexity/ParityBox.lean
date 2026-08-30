import Mathlib

set_option autoImplicit false

/-!
# Parity equations as bounded integer box equations

This file isolates the coordinatewise passage from equations over `ZMod 2` on a finite
selected set to integer equations with even slack.  Cast compatibility and bit assumptions
are required only on selected entries and row targets.  The construction does not require
either index type to be nonempty and makes no assumption on entries outside the selected set.
-/

namespace BilinearComplexity.ParityBox

universe u v

/-- The integer-valued membership indicator of a finite set. -/
def integerIndicator {ι : Type u} [DecidableEq ι] (D : Finset ι) (i : ι) : ℤ :=
  if i ∈ D then 1 else 0

example : integerIndicator ({true} : Finset Bool) true = 1 := by
  simp [integerIndicator]

example : integerIndicator ({true} : Finset Bool) false = 0 := by
  simp [integerIndicator]

/-- Every value of the integer indicator lies in the literal integer box `[0, 1]`. -/
theorem integerIndicator_box {ι : Type u} [DecidableEq ι] (D : Finset ι) (i : ι) :
    0 ≤ integerIndicator D i ∧ integerIndicator D i ≤ 1 := by
  by_cases hi : i ∈ D <;> simp [integerIndicator, hi]

/-- Equality of integer casts modulo two is equivalent to an unrestricted even-slack
integer equation. -/
theorem intCast_zmodTwo_eq_iff_exists_slack (a b : ℤ) :
    (a : ZMod 2) = (b : ZMod 2) ↔ ∃ s : ℤ, a = b + 2 * s := by
  constructor
  · intro hcast
    have hdvd : (2 : ℤ) ∣ b - a :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub a b 2).mp hcast
    obtain ⟨t, ht⟩ := hdvd
    refine ⟨-t, ?_⟩
    omega
  · rintro ⟨s, heq⟩
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub a b 2).mpr
    exact ⟨-s, by omega⟩

/-- Selected-entry and target cast compatibility identifies the coordinatewise `ZMod 2`
equations with integer equations having an unrestricted integer slack in every row. -/
theorem parity_iff_exists_slack
    {ι : Type u} {κ : Type v} (D : Finset ι)
    (A₂ : κ → ι → ZMod 2) (m₂ : κ → ZMod 2)
    (A : κ → ι → ℤ) (m : κ → ℤ)
    (hA : ∀ r i, i ∈ D → (A r i : ZMod 2) = A₂ r i)
    (hm : ∀ r, (m r : ZMod 2) = m₂ r) :
    (∀ r, ∑ i ∈ D, A₂ r i = m₂ r) ↔
      ∃ s : κ → ℤ, ∀ r, ∑ i ∈ D, A r i = m r + 2 * s r := by
  constructor
  · intro hparity
    have hrow : ∀ r, ∃ sr : ℤ, ∑ i ∈ D, A r i = m r + 2 * sr := by
      intro r
      have hsumCast :
          ((∑ i ∈ D, A r i : ℤ) : ZMod 2) = ∑ i ∈ D, A₂ r i := by
        rw [Int.cast_sum]
        apply Finset.sum_congr rfl
        intro i hi
        exact hA r i hi
      have hcast :
          ((∑ i ∈ D, A r i : ℤ) : ZMod 2) = (m r : ZMod 2) := by
        calc
          ((∑ i ∈ D, A r i : ℤ) : ZMod 2) = ∑ i ∈ D, A₂ r i := hsumCast
          _ = m₂ r := hparity r
          _ = (m r : ZMod 2) := (hm r).symm
      exact (intCast_zmodTwo_eq_iff_exists_slack _ _).mp hcast
    classical
    let s : κ → ℤ := fun r => Classical.choose (hrow r)
    refine ⟨s, fun r => ?_⟩
    exact Classical.choose_spec (hrow r)
  · rintro ⟨s, hs⟩
    intro r
    have hsumCast :
        ((∑ i ∈ D, A r i : ℤ) : ZMod 2) = ∑ i ∈ D, A₂ r i := by
      rw [Int.cast_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact hA r i hi
    have hcast :
        ((∑ i ∈ D, A r i : ℤ) : ZMod 2) = (m r : ZMod 2) :=
      (intCast_zmodTwo_eq_iff_exists_slack _ _).mpr ⟨s r, hs r⟩
    calc
      ∑ i ∈ D, A₂ r i = ((∑ i ∈ D, A r i : ℤ) : ZMod 2) := hsumCast.symm
      _ = (m r : ZMod 2) := hcast
      _ = m₂ r := hm r

/-- If all selected summands and the target are literal integer bits, an integer slack in
the selected-sum equation lies between zero and half the selected-set cardinality. -/
theorem slack_bounds_of_integer_bits
    {ι : Type u} (D : Finset ι) (a : ι → ℤ) (target slack : ℤ)
    (ha : ∀ i, i ∈ D → a i = 0 ∨ a i = 1)
    (htarget : target = 0 ∨ target = 1)
    (hequation : ∑ i ∈ D, a i = target + 2 * slack) :
    0 ≤ slack ∧ slack ≤ ((D.card / 2 : ℕ) : ℤ) := by
  have hsumNonneg : 0 ≤ ∑ i ∈ D, a i := by
    apply Finset.sum_nonneg
    intro i hi
    rcases ha i hi with hai | hai <;> omega
  have hsumUpper : (∑ i ∈ D, a i) ≤ (D.card : ℤ) := by
    calc
      (∑ i ∈ D, a i) ≤ ∑ _i ∈ D, (1 : ℤ) := by
        apply Finset.sum_le_sum
        intro i hi
        rcases ha i hi with hai | hai <;> omega
      _ = (D.card : ℤ) := by simp
  rcases htarget with htarget | htarget <;> subst target <;>
    constructor <;> omega

/-- Under literal-bit hypotheses, the parity equations are equivalent to integer equations
whose row slacks lie in the selected-set cardinality bound. -/
theorem parity_iff_exists_bounded_slack
    {ι : Type u} {κ : Type v} (D : Finset ι)
    (A₂ : κ → ι → ZMod 2) (m₂ : κ → ZMod 2)
    (A : κ → ι → ℤ) (m : κ → ℤ)
    (hAcast : ∀ r i, i ∈ D → (A r i : ZMod 2) = A₂ r i)
    (hmcast : ∀ r, (m r : ZMod 2) = m₂ r)
    (hAbit : ∀ r i, i ∈ D → A r i = 0 ∨ A r i = 1)
    (hmbit : ∀ r, m r = 0 ∨ m r = 1) :
    (∀ r, ∑ i ∈ D, A₂ r i = m₂ r) ↔
      ∃ s : κ → ℤ, ∀ r,
        (∑ i ∈ D, A r i = m r + 2 * s r) ∧
          0 ≤ s r ∧ s r ≤ ((D.card / 2 : ℕ) : ℤ) := by
  constructor
  · intro hparity
    obtain ⟨s, hs⟩ :=
      (parity_iff_exists_slack D A₂ m₂ A m hAcast hmcast).mp hparity
    refine ⟨s, fun r => ⟨hs r, ?_⟩⟩
    exact slack_bounds_of_integer_bits D (A r) (m r) (s r)
      (hAbit r) (hmbit r) (hs r)
  · rintro ⟨s, hs⟩
    apply (parity_iff_exists_slack D A₂ m₂ A m hAcast hmcast).mpr
    exact ⟨s, fun r => (hs r).1⟩

/-- Two integer slack functions satisfying the same selected row equations are equal. -/
theorem slack_unique
    {ι : Type u} {κ : Type v} (D : Finset ι)
    (A : κ → ι → ℤ) (m : κ → ℤ) (s t : κ → ℤ)
    (hs : ∀ r, ∑ i ∈ D, A r i = m r + 2 * s r)
    (ht : ∀ r, ∑ i ∈ D, A r i = m r + 2 * t r) :
    s = t := by
  funext r
  have hsr := hs r
  have htr := ht r
  omega

/-- Summing integer coefficients over the full finite carrier against the membership
indicator equals summing those coefficients over the selected finite set. -/
theorem sum_mul_integerIndicator
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (D : Finset ι) (f : ι → ℤ) :
    ∑ i, f i * integerIndicator D i = ∑ i ∈ D, f i := by
  simp [integerIndicator]

/-- A selected parity solution with literal-bit lifts supplies a full-carrier integer box
witness and row slacks bounded uniformly by half the ambient carrier cardinality. -/
theorem exists_carrier_box_of_parity
    {ι : Type u} {κ : Type v} [Fintype ι] [DecidableEq ι]
    (D : Finset ι)
    (A₂ : κ → ι → ZMod 2) (m₂ : κ → ZMod 2)
    (A : κ → ι → ℤ) (m : κ → ℤ)
    (hAcast : ∀ r i, i ∈ D → (A r i : ZMod 2) = A₂ r i)
    (hmcast : ∀ r, (m r : ZMod 2) = m₂ r)
    (hAbit : ∀ r i, i ∈ D → A r i = 0 ∨ A r i = 1)
    (hmbit : ∀ r, m r = 0 ∨ m r = 1)
    (hparity : ∀ r, ∑ i ∈ D, A₂ r i = m₂ r) :
    ∃ x : ι → ℤ, ∃ s : κ → ℤ,
      (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
        ∀ r, (∑ i, A r i * x i = m r + 2 * s r) ∧
          0 ≤ s r ∧ s r ≤ ((Fintype.card ι / 2 : ℕ) : ℤ) := by
  obtain ⟨s, hs⟩ :=
    (parity_iff_exists_bounded_slack D A₂ m₂ A m hAcast hmcast hAbit hmbit).mp hparity
  refine ⟨integerIndicator D, s, integerIndicator_box D, fun r => ?_⟩
  refine ⟨?_, (hs r).2.1, ?_⟩
  · calc
      ∑ i, A r i * integerIndicator D i = ∑ i ∈ D, A r i :=
        sum_mul_integerIndicator D (A r)
      _ = m r + 2 * s r := (hs r).1
  · have hcard : D.card / 2 ≤ Fintype.card ι / 2 :=
      Nat.div_le_div_right (Finset.card_le_univ D)
    exact (hs r).2.2.trans (by exact_mod_cast hcard)

/-- Selected parity equations are equivalent to a full-carrier integer box formulation
whose box vector is explicitly the membership indicator of the selected set. -/
theorem parity_iff_exists_carrier_box
    {ι : Type u} {κ : Type v} [Fintype ι] [DecidableEq ι]
    (D : Finset ι)
    (A₂ : κ → ι → ZMod 2) (m₂ : κ → ZMod 2)
    (A : κ → ι → ℤ) (m : κ → ℤ)
    (hAcast : ∀ r i, i ∈ D → (A r i : ZMod 2) = A₂ r i)
    (hmcast : ∀ r, (m r : ZMod 2) = m₂ r)
    (hAbit : ∀ r i, i ∈ D → A r i = 0 ∨ A r i = 1)
    (hmbit : ∀ r, m r = 0 ∨ m r = 1) :
    (∀ r, ∑ i ∈ D, A₂ r i = m₂ r) ↔
      ∃ x : ι → ℤ, ∃ s : κ → ℤ,
        x = integerIndicator D ∧
          (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
            ∀ r, (∑ i, A r i * x i = m r + 2 * s r) ∧
              0 ≤ s r ∧ s r ≤ ((Fintype.card ι / 2 : ℕ) : ℤ) := by
  constructor
  · intro hparity
    obtain ⟨s, hs⟩ :=
      (parity_iff_exists_bounded_slack D A₂ m₂ A m hAcast hmcast hAbit hmbit).mp hparity
    refine ⟨integerIndicator D, s, rfl, integerIndicator_box D, fun r => ?_⟩
    refine ⟨?_, (hs r).2.1, ?_⟩
    · calc
        ∑ i, A r i * integerIndicator D i = ∑ i ∈ D, A r i :=
          sum_mul_integerIndicator D (A r)
        _ = m r + 2 * s r := (hs r).1
    · have hcard : D.card / 2 ≤ Fintype.card ι / 2 :=
        Nat.div_le_div_right (Finset.card_le_univ D)
      exact (hs r).2.2.trans (by exact_mod_cast hcard)
  · rintro ⟨x, s, hx, _hbox, hrows⟩
    subst x
    apply (parity_iff_exists_slack D A₂ m₂ A m hAcast hmcast).mpr
    refine ⟨s, fun r => ?_⟩
    calc
      ∑ i ∈ D, A r i = ∑ i, A r i * integerIndicator D i :=
        (sum_mul_integerIndicator D (A r)).symm
      _ = m r + 2 * s r := (hrows r).1

/- The cast, bit, and parity assumptions are jointly satisfiable on a selected nonempty row. -/
example :
    let D : Finset Unit := {()}
    let A₂ : Unit → Unit → ZMod 2 := fun _ _ => 1
    let m₂ : Unit → ZMod 2 := fun _ => 1
    let A : Unit → Unit → ℤ := fun _ _ => 1
    let m : Unit → ℤ := fun _ => 1
    (∀ r i, i ∈ D → (A r i : ZMod 2) = A₂ r i) ∧
      (∀ r, (m r : ZMod 2) = m₂ r) ∧
      (∀ r i, i ∈ D → A r i = 0 ∨ A r i = 1) ∧
      (∀ r, m r = 0 ∨ m r = 1) ∧
      (∀ r, ∑ i ∈ D, A₂ r i = m₂ r) := by
  simp

/- Empty carriers, empty selected sets, empty row types, and literal zero rows all retain the
stated behavior; these examples guard the intended degenerate cases. -/
example :
    ∃ s : Unit → ℤ, ∀ r,
      (∑ i ∈ (∅ : Finset Empty), (0 : Unit → Empty → ℤ) r i =
        (0 : Unit → ℤ) r + 2 * s r) ∧
      0 ≤ s r ∧ s r ≤ ((((∅ : Finset Empty).card) / 2 : ℕ) : ℤ) := by
  rw [← parity_iff_exists_bounded_slack
    (∅ : Finset Empty)
    (0 : Unit → Empty → ZMod 2) (0 : Unit → ZMod 2)
    (0 : Unit → Empty → ℤ) (0 : Unit → ℤ)]
  all_goals simp

example :
    ∃ s : Unit → ℤ, ∀ r,
      (∑ i ∈ (∅ : Finset Unit), (0 : Unit → Unit → ℤ) r i =
        (0 : Unit → ℤ) r + 2 * s r) ∧
      0 ≤ s r ∧ s r ≤ ((((∅ : Finset Unit).card) / 2 : ℕ) : ℤ) := by
  rw [← parity_iff_exists_bounded_slack
    (∅ : Finset Unit)
    (0 : Unit → Unit → ZMod 2) (0 : Unit → ZMod 2)
    (0 : Unit → Unit → ℤ) (0 : Unit → ℤ)]
  all_goals simp

example :
    (∀ r : Empty, ∑ i ∈ ({()} : Finset Unit),
      (0 : Empty → Unit → ZMod 2) r i = (0 : Empty → ZMod 2) r) ↔
      ∃ s : Empty → ℤ, ∀ r,
        ∑ i ∈ ({()} : Finset Unit), (0 : Empty → Unit → ℤ) r i =
          (0 : Empty → ℤ) r + 2 * s r := by
  apply parity_iff_exists_slack
  · simp
  · simp

example :
    ∃ s : Unit → ℤ, ∀ r,
      (∑ i ∈ ({()} : Finset Unit), (0 : Unit → Unit → ℤ) r i =
        (0 : Unit → ℤ) r + 2 * s r) ∧
      0 ≤ s r ∧ s r ≤ (((({()} : Finset Unit).card) / 2 : ℕ) : ℤ) := by
  refine ⟨0, ?_⟩
  simp

end BilinearComplexity.ParityBox
