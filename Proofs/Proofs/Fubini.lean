import Mathlib

/-!
# Fubini Numbers and the Polylogarithmic Identity

Defines the Fubini numbers (ordered Bell numbers, A000670) and proves
  `∑_{j≥0} j^m/2^j = 2 · fubini(m)`.

This identity connects polylogarithmic series to the Fubini recurrence
via strong induction and the binomial difference expansion.
-/

open Finset BigOperators

namespace A051293

section Fubini

/-- Fubini numbers (A000670), also called ordered Bell numbers.
    fubini(n) = ∑_{k=0}^{n-1} C(n,k) · fubini(k), with fubini(0) = 1. -/
def fubini : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ k : Fin (n + 1), (n + 1).choose k.val * fubini k.val
termination_by n => n
decreasing_by exact k.isLt

@[simp] lemma fubini_zero : fubini 0 = 1 := by native_decide
lemma fubini_one : fubini 1 = 1 := by native_decide
lemma fubini_two : fubini 2 = 3 := by native_decide
lemma fubini_three : fubini 3 = 13 := by native_decide
lemma fubini_four : fubini 4 = 75 := by native_decide
lemma fubini_five : fubini 5 = 541 := by native_decide

end Fubini

/-! ## Polylogarithmic identity

The e.g.f. of the Fubini numbers is `1/(2 − eˣ)`. Since
`∑_{j≥0} e^{jx}/2^{j+1} = 1/(2 − eˣ)` for `x < log 2`,
comparing `x^m/m!` coefficients gives
`∑_{j≥0} j^m/2^{j+1} = fubini(m)`, i.e.
`∑_{j≥0} j^m/2^j = 2 · fubini(m)`. -/
section CoefficientIdentity

theorem polylog_summable (m : ℕ) :
    Summable (fun j : ℕ => (↑j : ℝ) ^ m / (2 : ℝ) ^ j) := by
  have : ∀ j : ℕ, (↑j : ℝ) ^ m / (2 : ℝ) ^ j = (↑j : ℝ) ^ m * ((2 : ℝ)⁻¹) ^ j := by
    intro j; rw [inv_pow, div_eq_mul_inv]
  simp_rw [this]
  exact summable_pow_mul_geometric_of_norm_lt_one m (by simp; norm_num)

theorem polylog_shift_tsum (m : ℕ) (hm : 0 < m) :
    ∑' j : ℕ, (↑(j + 1) : ℝ) ^ m / (2 : ℝ) ^ j =
      2 * ∑' j : ℕ, (↑j : ℝ) ^ m / (2 : ℝ) ^ j := by
  have h_summ := polylog_summable m
  have h0 : (↑(0 : ℕ) : ℝ) ^ m / (2 : ℝ) ^ (0 : ℕ) = 0 := by
    simp [Nat.pos_iff_ne_zero.mp hm]
  have h_shift : ∑' j : ℕ, (↑j : ℝ) ^ m / (2 : ℝ) ^ j =
      (↑(0 : ℕ) : ℝ) ^ m / (2 : ℝ) ^ (0 : ℕ) +
        ∑' j : ℕ, (↑(j + 1) : ℝ) ^ m / (2 : ℝ) ^ (j + 1) := by
    exact h_summ.tsum_eq_zero_add
  rw [h0, zero_add] at h_shift
  have h_factor : ∀ j : ℕ, (↑(j + 1) : ℝ) ^ m / (2 : ℝ) ^ (j + 1) =
      (1 / 2) * ((↑(j + 1) : ℝ) ^ m / (2 : ℝ) ^ j) := by
    intro j; rw [pow_succ]; field_simp
  simp_rw [h_factor] at h_shift
  rw [tsum_mul_left] at h_shift
  linarith

private lemma binomial_diff (j m : ℕ) :
    (↑(j + 1) : ℝ) ^ (m + 1) - (↑j : ℝ) ^ (m + 1) =
      ∑ k ∈ Finset.range (m + 1), ↑((m + 1).choose k) * (↑j : ℝ) ^ k := by
  have hcast : (↑(j + 1) : ℝ) = (↑j : ℝ) + 1 := by push_cast; ring
  rw [hcast, add_pow (↑j : ℝ) 1 (m + 1)]
  simp only [one_pow, mul_one]
  rw [Finset.sum_range_succ]
  simp [Nat.choose_self, mul_comm]

private lemma hasSum_finset_sum (s : Finset ι) [DecidableEq ι]
    (f : ι → ℕ → ℝ) (a : ι → ℝ) (hf : ∀ i ∈ s, HasSum (f i) (a i)) :
    HasSum (fun j => ∑ i ∈ s, f i j) (∑ i ∈ s, a i) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s' ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf _ (Finset.mem_insert_self _ _)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- The load-bearing identity: `∑_{j≥0} j^m/2^j = 2 · fubini(m)`.

  Proof by strong induction. The shift identity `∑ (j+1)^m/2^j = 2·∑ j^m/2^j`
  (for m ≥ 1) combined with the binomial expansion `(j+1)^{m+1} − j^{m+1} =
  ∑_{k<m+1} C(m+1,k) j^k` and the Fubini recurrence pins the sum. -/
theorem fubini_polylog (m : ℕ) :
    HasSum (fun j : ℕ => (↑j : ℝ) ^ m / (2 : ℝ) ^ j)
      (2 * ↑(fubini m)) := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    cases m with
    | zero =>
      simp only [fubini_zero, Nat.cast_one, mul_one, pow_zero]
      simpa [one_div, inv_pow] using hasSum_geometric_two
    | succ m =>
      have h_summ := polylog_summable (m + 1)
      suffices h : ∑' (j : ℕ), (↑j : ℝ) ^ (m + 1) / (2 : ℝ) ^ j =
          2 * ↑(fubini (m + 1)) by
        exact h ▸ h_summ.hasSum
      -- Step 1: shift identity
      have h_shift := polylog_shift_tsum (m + 1) (by omega)
      -- Step 2: the binomial difference has a HasSum via IH
      have h_lc : HasSum (fun j : ℕ =>
          ∑ k ∈ Finset.range (m + 1),
            ↑((m + 1).choose k) * ((↑j : ℝ) ^ k / (2 : ℝ) ^ j))
          (∑ k ∈ Finset.range (m + 1),
            ↑((m + 1).choose k) * (2 * ↑(fubini k))) := by
        apply hasSum_finset_sum
        intro k hk
        exact (ih k (Finset.mem_range.mp hk)).mul_left _
      -- Step 3: rewrite function via binomial_diff
      have h_eq : ∀ j : ℕ, ((↑(j + 1) : ℝ) ^ (m + 1) - (↑j : ℝ) ^ (m + 1)) /
          (2 : ℝ) ^ j = ∑ k ∈ Finset.range (m + 1),
            ↑((m + 1).choose k) * ((↑j : ℝ) ^ k / (2 : ℝ) ^ j) := by
        intro j
        rw [binomial_diff, Finset.sum_div]
        apply Finset.sum_congr rfl; intro k _; ring
      -- Step 4: compute the value via Fubini recurrence
      have h_fubini_rec : (∑ k ∈ Finset.range (m + 1),
          (↑((m + 1).choose k) : ℝ) * (2 * ↑(fubini k))) =
          2 * ↑(fubini (m + 1)) := by
        have h_unfold : fubini (m + 1) =
            ∑ k : Fin (m + 1), (m + 1).choose k.val * fubini k.val := by
          simp only [fubini]
        rw [h_unfold, Fin.sum_univ_eq_sum_range (fun k => (m + 1).choose k * fubini k)]
        push_cast
        simp_rw [show ∀ (k : ℕ), (↑((m + 1).choose k) : ℝ) * (2 * ↑(fubini k)) =
            2 * (↑((m + 1).choose k) * ↑(fubini k)) from fun k => by ring]
        exact (Finset.mul_sum _ _ _).symm
      -- Step 5: the diff-tsum equals 2*fubini(m+1)
      have h_binom := ((h_lc.congr_fun h_eq).tsum_eq).trans h_fubini_rec
      -- Step 6: the diff-tsum also equals s (from shift)
      have h_sub : ∑' (j : ℕ), ((↑(j + 1) : ℝ) ^ (m + 1) - (↑j : ℝ) ^ (m + 1)) /
          (2 : ℝ) ^ j = ∑' (j : ℕ), (↑j : ℝ) ^ (m + 1) / (2 : ℝ) ^ j := by
        have h_eq2 : ∀ j : ℕ, ((↑(j + 1) : ℝ) ^ (m + 1) - (↑j : ℝ) ^ (m + 1)) /
            (2 : ℝ) ^ j = (↑(j + 1) : ℝ) ^ (m + 1) / (2 : ℝ) ^ j -
            (↑j : ℝ) ^ (m + 1) / (2 : ℝ) ^ j := fun j => sub_div _ _ _
        simp_rw [h_eq2]
        have h_diff_summable := (h_lc.congr_fun h_eq).summable
        have h_s1 : Summable (fun j : ℕ => (↑(j + 1) : ℝ) ^ (m + 1) / (2 : ℝ) ^ j) := by
          have : (fun j : ℕ => (↑(j + 1) : ℝ) ^ (m + 1) / (2 : ℝ) ^ j) = fun (j : ℕ) =>
              ((↑(j + 1) : ℝ) ^ (m + 1) - (↑j : ℝ) ^ (m + 1)) / (2 : ℝ) ^ j +
              (↑j : ℝ) ^ (m + 1) / (2 : ℝ) ^ j := by
            ext j; rw [sub_div, sub_add_cancel]
          rw [this]; exact h_diff_summable.add h_summ
        rw [h_s1.tsum_sub h_summ]
        linarith
      linarith

end CoefficientIdentity

end A051293
