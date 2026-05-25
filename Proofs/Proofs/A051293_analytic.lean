import Mathlib
import Proofs.Fubini

/-!
# A051293: Asymptotic Expansion of the Divisor-Sum Formula

Proves that for
  `a(n) := ∑_{k=1}^n ((1/k) ∑_{d|k, d odd} 2^{k/d}·φ(d) − 1)`,
the generating formula for OEIS A051293, we have
  `a(n) = (2^{n+1}/n) ∑_{k=0}^{M} fubini(k)/n^k + o(2^n / n^{M+1})`
for all M, where `fubini(k)` are the ordered Bell numbers (A000670).

This establishes Cloitre's conjecture (2002) for the analytic formula.
The connection to the combinatorial definition (nonempty subsets with
integer mean) is in `A051293_counting.lean`.

## Proof: discrete Laplace method

1. The divisor-sum formula `b(k) = (1/k) ∑_{d|k, d odd} 2^(k/d) φ(d)` is
   dominated by `d = 1`, reducing to `S(n) = ∑_{k=1}^n 2^k/k`.
2. Reindex `S(n) = 2^n ∑_j 1/(2^j(n−j))` and expand `1/(n−j)` in
   powers of `j/n`.
3. The coefficient identity `∑_{j≥0} j^m/2^j = 2·fubini(m)` yields
   the Fubini expansion directly.
-/

open Finset BigOperators Filter Asymptotics

namespace A051293

section Defs

/-- `b(k) = (1/k) ∑_{d|k, d odd} 2^(k/d) · φ(d)`. -/
noncomputable def b (k : ℕ) : ℝ :=
  (∑ d ∈ k.divisors.filter Odd,
    (2 : ℝ) ^ (k / d) * (d.totient : ℝ)) / (k : ℝ)

/-- `a(n) = ∑_{k=1}^n (b(k) − 1)`, the count of nonempty subsets
    of `{1,…,n}` whose elements have an integer average. -/
noncomputable def a (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (b (k + 1) - 1)

/-- `S(n) = ∑_{k=1}^n 2^k/k`, the dominant partial sum after
    extracting the `d = 1` term from the divisor-sum formula. -/
noncomputable def S (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (2 : ℝ) ^ (k + 1) / (↑(k + 1) : ℝ)

end Defs

/-! ## Step 1: d = 1 dominance

The `d = 1` term in `b(k)` contributes `2^k/k`. Every odd divisor
`d ≥ 3` contributes `2^(k/d) · φ(d) / k ≤ 2^(k/3) · d / k`.
Summing the error over `k = 1,…,n` yields `O(2^{n/3})`, which is
exponentially negligible against `S(n) ∼ 2^{n+1}/n`. -/
section Dominance

/-- The `d = 1` term in `b(k)` is `2^k/k`. -/
lemma b_eq_main_plus_tail (k : ℕ) (hk : 0 < k) :
    b k = (2 : ℝ) ^ k / ↑k +
      (∑ d ∈ (k.divisors.filter Odd).erase 1,
        (2 : ℝ) ^ (k / d) * (d.totient : ℝ)) / ↑k := by
  have h1 : (1 : ℕ) ∈ k.divisors.filter Odd :=
    Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨one_dvd k, hk.ne'⟩, odd_one⟩
  simp only [b, ← Finset.add_sum_erase _ _ h1, Nat.div_one, Nat.totient_one, Nat.cast_one,
    mul_one, add_div]

/-- Each odd divisor `d ≥ 3` of `k` contributes at most `2^(k/3)` to
    the numerator of `b(k)`, since `k/d ≤ k/3` and `φ(d) < d`. -/
lemma tail_term_bound (k d : ℕ) (hd : d ∈ (k.divisors.filter Odd).erase 1) :
    (2 : ℝ) ^ (k / d) * (d.totient : ℝ) ≤ ↑d * (2 : ℝ) ^ (k / 3) := by
  have hd_mem := Finset.mem_erase.mp hd
  have hd_filter := Finset.mem_filter.mp hd_mem.2
  have hd_dvd : d ∣ k := (Nat.mem_divisors.mp hd_filter.1).1
  have hk_pos : 0 < k := Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd_filter.1).2
  have hd_odd : Odd d := hd_filter.2
  have hd_ne : d ≠ 1 := hd_mem.1
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd hk_pos
  have hd_ge : 3 ≤ d := by
    obtain ⟨m, hm⟩ := hd_odd; omega
  have hkd : k / d ≤ k / 3 := Nat.div_le_div_left hd_ge (by omega)
  calc (2 : ℝ) ^ (k / d) * (d.totient : ℝ)
      ≤ (2 : ℝ) ^ (k / 3) * ↑d := by
        gcongr
        · exact one_le_two
        · exact_mod_cast Nat.totient_le d
    _ = ↑d * (2 : ℝ) ^ (k / 3) := mul_comm _ _

/-- `a(n) = S(n) − n` up to an exponentially small error. -/
private lemma tail_sum_bound (k : ℕ) (hk : 0 < k) :
    |b k - (2 : ℝ) ^ k / ↑k| ≤
      (∑ d ∈ (k.divisors.filter Odd).erase 1,
        ↑d * (2 : ℝ) ^ (k / 3)) / ↑k := by
  rw [b_eq_main_plus_tail k hk, add_sub_cancel_left]
  have hk' : (0 : ℝ) < ↑k := Nat.cast_pos.mpr hk
  rw [abs_div, abs_of_pos hk']
  gcongr
  calc |∑ d ∈ (k.divisors.filter Odd).erase 1, (2 : ℝ) ^ (k / d) * ↑d.totient|
      ≤ ∑ d ∈ (k.divisors.filter Odd).erase 1, |(2 : ℝ) ^ (k / d) * ↑d.totient| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ d ∈ (k.divisors.filter Odd).erase 1, (2 : ℝ) ^ (k / d) * ↑d.totient := by
        congr 1; ext d; rw [abs_of_nonneg]; positivity
    _ ≤ ∑ d ∈ (k.divisors.filter Odd).erase 1, ↑d * (2 : ℝ) ^ (k / 3) :=
        Finset.sum_le_sum (fun d hd => tail_term_bound k d hd)

/-- The error `a(n) − (S(n) − n)` is `O(2^{n/3})`, hence `o(2^n/n^M)` for any `M`. -/
theorem a_sub_S_isLittleO (M : ℕ) :
    (fun n : ℕ => a n - (S n - ↑n))
    =o[atTop] (fun n : ℕ => (2 : ℝ) ^ n / (↑n : ℝ) ^ (M + 2)) := by
  -- Crude bound: |a(n) - (S(n) - n)| ≤ n² · 2^{n/3}, then n²·2^{n/3} = o(2^n/n^{M+2}).
  -- Part A: the error bound
  -- The difference is a sum of tail terms
  have h_diff_eq : ∀ n : ℕ, a n - (S n - ↑n) =
      ∑ k ∈ Finset.range n, (b (k + 1) - (2 : ℝ) ^ (k + 1) / (↑(k + 1))) := by
    intro n; simp only [a, S, Finset.sum_sub_distrib]
    have : (∑ _ ∈ Finset.range n, (1 : ℝ)) = ↑n := by
      simp [Finset.sum_const, Finset.card_range]
    linarith
  -- Each tail term is bounded by (k+1)·2^{(k+1)/3}
  have h_term_bound : ∀ k : ℕ, |b (k + 1) - (2 : ℝ) ^ (k + 1) / ↑(k + 1)| ≤
      ↑(k + 1) * (2 : ℝ) ^ ((k + 1) / 3) := by
    intro k
    set m := k + 1 with hm_def
    have hm : 0 < m := by omega
    have h := tail_sum_bound m hm
    have hm' : (0 : ℝ) < ↑m := Nat.cast_pos.mpr hm
    have h_num : (∑ d ∈ (m.divisors.filter Odd).erase 1,
        ↑d * (2 : ℝ) ^ (m / 3)) ≤ ↑m ^ 2 * (2 : ℝ) ^ (m / 3) := by
      have h_each : ∀ d ∈ (m.divisors.filter Odd).erase 1,
          ↑d * (2 : ℝ) ^ (m / 3) ≤ ↑m * (2 : ℝ) ^ (m / 3) := by
        intro d hd
        gcongr
        have := (Finset.mem_erase.mp hd).2
        have := Finset.mem_filter.mp this
        exact_mod_cast Nat.divisor_le this.1
      calc ∑ d ∈ (m.divisors.filter Odd).erase 1, ↑d * (2 : ℝ) ^ (m / 3)
          ≤ ∑ _ ∈ (m.divisors.filter Odd).erase 1, ↑m * (2 : ℝ) ^ (m / 3) :=
            Finset.sum_le_sum h_each
        _ = ((m.divisors.filter Odd).erase 1).card * (↑m * (2 : ℝ) ^ (m / 3)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ m * (↑m * (2 : ℝ) ^ (m / 3)) := by
            gcongr
            calc ((m.divisors.filter Odd).erase 1).card
                ≤ m.divisors.card := by
                  exact (Finset.card_erase_le).trans (Finset.card_filter_le _ _)
              _ ≤ m := Nat.card_divisors_le_self m
        _ = ↑m ^ 2 * (2 : ℝ) ^ (m / 3) := by ring
    calc |b m - (2 : ℝ) ^ m / ↑m|
        ≤ (∑ d ∈ (m.divisors.filter Odd).erase 1, ↑d * (2 : ℝ) ^ (m / 3)) / ↑m := h
      _ ≤ ↑m ^ 2 * (2 : ℝ) ^ (m / 3) / ↑m := by gcongr
      _ = ↑m * (2 : ℝ) ^ (m / 3) := by rw [show (↑m : ℝ) ^ 2 = ↑m * ↑m from by ring]; field_simp
  have h_err : ∀ n : ℕ, 0 < n →
      |a n - (S n - ↑n)| ≤ ↑n ^ 2 * (2 : ℝ) ^ (n / 3) := by
    intro n hn
    rw [h_diff_eq]
    calc |∑ k ∈ Finset.range n, (b (k + 1) - (2 : ℝ) ^ (k + 1) / ↑(k + 1))|
        ≤ ∑ k ∈ Finset.range n, |b (k + 1) - (2 : ℝ) ^ (k + 1) / ↑(k + 1)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range n, (↑(k + 1) * (2 : ℝ) ^ ((k + 1) / 3)) :=
          Finset.sum_le_sum (fun k _ => h_term_bound k)
      _ ≤ ∑ k ∈ Finset.range n, (↑n * (2 : ℝ) ^ (n / 3)) := by
          apply Finset.sum_le_sum; intro k hk
          have hk' : k < n := Finset.mem_range.mp hk
          have h1 : (↑(k + 1) : ℝ) ≤ ↑n := by exact_mod_cast Nat.succ_le_of_lt hk'
          have h2 : (2 : ℝ) ^ ((k + 1) / 3) ≤ (2 : ℝ) ^ (n / 3) :=
            pow_le_pow_right₀ (by norm_num) (Nat.div_le_div_right (by omega))
          exact mul_le_mul h1 h2 (pow_nonneg (by norm_num) _) (Nat.cast_nonneg' n)
      _ = ↑n * (↑n * (2 : ℝ) ^ (n / 3)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ↑n ^ 2 * (2 : ℝ) ^ (n / 3) := by ring
  -- Part B: n²·2^{n/3} = o(2^n/n^{M+2})
  -- Equiv: n^{M+4} = o(2^{2n/3}). Since 2^{2n/3} ≥ (√2)^n for large n,
  -- and n^{M+4} = o((√2)^n), done.
  have h_exp : (fun n : ℕ => (↑n : ℝ) ^ 2 * (2 : ℝ) ^ (n / 3))
      =o[atTop] (fun n : ℕ => (2 : ℝ) ^ n / (↑n : ℝ) ^ (M + 2)) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have h_poly := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) (M + 4)
      Real.one_lt_sqrt_two).bound (half_pos hc)
    rw [Filter.eventually_atTop] at h_poly ⊢
    obtain ⟨N, hN⟩ := h_poly
    refine ⟨max N 1, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := le_of_max_le_right hn
    have hnN : N ≤ n := le_of_max_le_left hn
    have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
    have hpoly := hN n hnN
    rw [Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg' n) _),
      Real.norm_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)] at hpoly
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    -- (√2)^n ≤ 2^{n/2+1}
    have h_sqrt_le : Real.sqrt 2 ^ n ≤ (2 : ℝ) ^ (n / 2 + 1) := by
      have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      calc Real.sqrt 2 ^ n
          = Real.sqrt 2 ^ (2 * (n / 2) + n % 2) := by congr 1; omega
        _ = (Real.sqrt 2 ^ 2) ^ (n / 2) * Real.sqrt 2 ^ (n % 2) := by rw [pow_add, pow_mul]
        _ = (2 : ℝ) ^ (n / 2) * Real.sqrt 2 ^ (n % 2) := by rw [hsq]
        _ ≤ (2 : ℝ) ^ (n / 2) * 2 := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
            calc Real.sqrt 2 ^ (n % 2)
                ≤ Real.sqrt 2 ^ 1 := pow_le_pow_right₀ Real.one_lt_sqrt_two.le (by omega)
              _ ≤ 2 := by
                  rw [pow_one]
                  have : Real.sqrt 4 = 2 := by
                    rw [show (4:ℝ) = 2^2 from by norm_num, Real.sqrt_sq (by norm_num)]
                  linarith [Real.sqrt_le_sqrt (show (2:ℝ) ≤ 4 by norm_num)]
        _ = (2 : ℝ) ^ (n / 2 + 1) := by rw [pow_succ]
    have h2pos : (0:ℝ) ≤ (2:ℝ) ^ (n / 3) := pow_nonneg (by norm_num) _
    -- n^{M+4}*2^{n/3} ≤ c*2^n
    have h1 : (↑n : ℝ) ^ (M + 4) * (2 : ℝ) ^ (n / 3) ≤ c * (2 : ℝ) ^ n := by
      calc (↑n : ℝ) ^ (M + 4) * (2 : ℝ) ^ (n / 3)
          ≤ c / 2 * Real.sqrt 2 ^ n * (2 : ℝ) ^ (n / 3) :=
            mul_le_mul_of_nonneg_right hpoly h2pos
        _ = c / 2 * (Real.sqrt 2 ^ n * (2 : ℝ) ^ (n / 3)) := by ring
        _ ≤ c / 2 * ((2 : ℝ) ^ (n / 2 + 1) * (2 : ℝ) ^ (n / 3)) := by gcongr
        _ ≤ c / 2 * (2 : ℝ) ^ (n + 1) := by
            gcongr; rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
        _ = c * (2 : ℝ) ^ n := by rw [pow_succ]; ring
    calc (↑n : ℝ) ^ 2 * (2 : ℝ) ^ (n / 3)
        = (↑n : ℝ) ^ (M + 4) * (2 : ℝ) ^ (n / 3) / (↑n : ℝ) ^ (M + 2) := by
          rw [show (M : ℕ) + 4 = 2 + (M + 2) from by omega, pow_add]; field_simp
      _ ≤ c * (2 : ℝ) ^ n / (↑n : ℝ) ^ (M + 2) :=
          div_le_div_of_nonneg_right h1 (pow_nonneg (Nat.cast_nonneg' n) _)
      _ = c * ((2 : ℝ) ^ n / (↑n : ℝ) ^ (M + 2)) := by ring
  -- Combine: f =O h (from h_err) and h =o g (from h_exp)
  have h_bigO : (fun n : ℕ => a n - (S n - ↑n))
      =O[atTop] (fun n : ℕ => (↑n : ℝ) ^ 2 * (2 : ℝ) ^ (n / 3)) := by
    apply Asymptotics.IsBigO.of_bound 1
    rw [Filter.eventually_atTop]
    refine ⟨1, fun n hn => ?_⟩
    rw [one_mul]
    exact (h_err n (by omega)).trans (le_abs_self _)
  exact h_bigO.trans_isLittleO h_exp

end Dominance

/-! ## Step 3: discrete Laplace expansion

Reindex `S(n) = 2^n ∑_{j=0}^{n−1} 1/(2^j(n−j))`. The `j`-th term
decays as `1/2^j`, so the sum is dominated by small `j`. Expand
`1/(n−j) = (1/n) ∑_{m=0}^M (j/n)^m + (j/n)^{M+1}/(n−j)`,
interchange the finite `j`-sum with the `m`-sum. The `m`-th
coefficient becomes `∑_j j^m/2^j · 1/n^{m+1} = 2·fubini(m)/n^{m+1}`
by Step 2. -/
section DiscreteLaplace

/-- Reindexing: `S(n) = 2^n · ∑_{j<n} 1/(2^j · (n − j))`. -/
theorem S_reindex (n : ℕ) (_hn : 0 < n) :
    S n = (2 : ℝ) ^ n *
      ∑ j ∈ Finset.range n,
        1 / ((2 : ℝ) ^ j * (↑n - ↑j : ℝ)) := by
  simp only [S]
  rw [← Finset.sum_range_reflect (fun j => 1 / ((2 : ℝ) ^ j * (↑n - ↑j))) n,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < n := Finset.mem_range.mp hk
  have hcast : (↑n : ℝ) - ↑(n - 1 - k) = ↑(k + 1) := by
    rw [← Nat.cast_sub (by omega : n - 1 - k ≤ n)]; congr 1; omega
  have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1 - k) * (2 : ℝ) ^ (k + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [hcast, hpow]
  have : (k : ℝ) + 1 ≠ 0 := by positivity
  have : (2 : ℝ) ^ (n - 1 - k) ≠ 0 := pow_ne_zero _ two_ne_zero
  field_simp

/-- Tail bound: `∑_{j=J+1}^{n−1} 1/(2^j(n−j)) ≤ 1/2^J`.
    Allows truncating the Laplace sum at any fixed `J`. -/
theorem laplace_tail_bound (n J : ℕ) (_hJ : J < n) :
    |∑ j ∈ Finset.Ico (J + 1) n,
      1 / ((2 : ℝ) ^ j * (↑n - ↑j : ℝ))| ≤ 1 / (2 : ℝ) ^ J := by
  have hpos : ∀ j ∈ Finset.Ico (J + 1) n,
      0 < 1 / ((2 : ℝ) ^ j * (↑n - ↑j : ℝ)) := by
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    have : (0 : ℝ) < ↑n - ↑j := by
      have : j < n := hj'.2
      have : (↑j : ℝ) < ↑n := Nat.cast_lt.mpr this
      linarith
    positivity
  rw [abs_of_nonneg (Finset.sum_nonneg (fun j hj => le_of_lt (hpos j hj)))]
  calc ∑ j ∈ Finset.Ico (J + 1) n, 1 / ((2 : ℝ) ^ j * (↑n - ↑j))
      ≤ ∑ j ∈ Finset.Ico (J + 1) n, 1 / (2 : ℝ) ^ j := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_Ico.mp hj
        have hnjpos : 1 ≤ (↑n : ℝ) - ↑j := by
          have : j + 1 ≤ n := hj'.2
          have : (↑j : ℝ) + 1 ≤ ↑n := by exact_mod_cast this
          linarith
        have h2j : (0 : ℝ) < (2 : ℝ) ^ j := pow_pos (by norm_num) j
        apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) h2j
        exact le_mul_of_one_le_right (le_of_lt h2j) hnjpos
    _ = ∑ j ∈ Finset.Ico (J + 1) n, ((1 : ℝ) / 2) ^ j := by
        congr 1; ext j; simp [div_eq_inv_mul]
    _ ≤ ((1 : ℝ) / 2) ^ (J + 1) / (1 - (1 : ℝ) / 2) :=
        geom_sum_Ico_le_of_lt_one (by positivity) (by norm_num)
    _ = 1 / (2 : ℝ) ^ J := by
        simp [one_div, pow_succ, inv_mul_eq_div]
        ring

/-- Finite geometric expansion of `1/(n − j)`. -/
theorem geom_expand (n j M : ℕ) (hn : 0 < n) (hj : j < n) :
    1 / (↑n - ↑j : ℝ) =
      1 / (↑n : ℝ) * ∑ i ∈ Finset.range (M + 1), ((↑j : ℝ) / ↑n) ^ i +
      ((↑j : ℝ) / ↑n) ^ (M + 1) / (↑n - ↑j : ℝ) := by
  have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hjn : (j : ℝ) < (n : ℝ) := by exact_mod_cast hj
  have hsub : (0 : ℝ) < (n : ℝ) - (j : ℝ) := by linarith
  have hk : (n : ℝ) ≠ 0 := ne_of_gt hn'
  have hd : (n : ℝ) - (j : ℝ) ≠ 0 := ne_of_gt hsub
  have hne : (j : ℝ) / (n : ℝ) ≠ 1 := ne_of_lt (div_lt_one hn' |>.mpr hjn)
  set r := (j : ℝ) / n with hr_def
  have key := geom_sum_mul_neg r (M + 1)
  have sum_eq : (∑ i ∈ Finset.range (M + 1), r ^ i) = (1 - r ^ (M + 1)) / (1 - r) := by
    rw [eq_div_iff (sub_ne_zero.mpr (ne_comm.mpr hne))]
    linarith
  rw [sum_eq]
  have hr : 1 - r = ((n : ℝ) - j) / n := by rw [hr_def]; field_simp
  rw [hr]
  field_simp
  ring

/-- The finite polylog partial sum `∑_{j<n} j^m/2^j` converges to the
    infinite series `2·fubini(m)` as `n → ∞`. -/
private lemma partial_polylog_tendsto (m : ℕ) :
    Filter.Tendsto (fun n : ℕ => ∑ j ∈ Finset.range n,
      (↑j : ℝ) ^ m / (2 : ℝ) ^ j)
      atTop (nhds (2 * ↑(fubini m))) :=
  (fubini_polylog m).tendsto_sum_nat

/-- The remainder from truncating the geometric expansion of `1/(n-j)`
    is `o(1/n^{M+1})` after summing over `j`. -/
private lemma remainder_term_nonneg (n j M : ℕ) (hj : j < n) :
    0 ≤ ((↑j : ℝ) / ↑n) ^ (M + 1) / ((2 : ℝ) ^ j * (↑n - ↑j)) := by
  apply div_nonneg (pow_nonneg (div_nonneg (Nat.cast_nonneg' j) (Nat.cast_nonneg' n)) _)
  exact mul_nonneg (pow_nonneg (by norm_num) _)
    (by have : (↑j : ℝ) < ↑n := Nat.cast_lt.mpr hj; linarith)

private lemma remainder_term_le_polylog (n j M : ℕ) (hn : 0 < n) (hj : j < n)
    (hjn : 2 * j ≤ n) :
    ((↑j : ℝ) / ↑n) ^ (M + 1) / ((2 : ℝ) ^ j * (↑n - ↑j)) ≤
      2 * (↑j : ℝ) ^ (M + 1) / ((↑n : ℝ) ^ (M + 2) * (2 : ℝ) ^ j) := by
  have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hjn' : (↑j : ℝ) < ↑n := Nat.cast_lt.mpr hj
  have hsub : (0 : ℝ) < ↑n - ↑j := by linarith
  have h2jn : 2 * (↑j : ℝ) ≤ ↑n := by exact_mod_cast hjn
  have hn2 : (↑n : ℝ) / 2 ≤ ↑n - ↑j := by linarith
  have hj0 : (0:ℝ) ≤ ↑j := Nat.cast_nonneg j
  have h2j : (0:ℝ) < (2:ℝ) ^ j := pow_pos (by norm_num) j
  have hjM : (0:ℝ) ≤ (↑j : ℝ) ^ (M + 1) := pow_nonneg hj0 _
  have hnM : (0:ℝ) < (↑n : ℝ) ^ (M + 1) := pow_pos hn' _
  have hden : (0:ℝ) < (↑n : ℝ) ^ (M + 2) * (2 : ℝ) ^ j :=
    mul_pos (pow_pos hn' _) h2j
  rw [div_pow, div_div, div_le_div_iff₀
    (mul_pos hnM (mul_pos h2j hsub)) hden]
  rw [show (↑n : ℝ) ^ (M + 2) = (↑n : ℝ) ^ (M + 1) * ↑n from by ring_nf]
  nlinarith [mul_le_mul_of_nonneg_left hn2
    (mul_nonneg (mul_nonneg hjM hnM.le) h2j.le)]

private lemma remainder_sum_isBigO (M : ℕ) :
    (fun n : ℕ => ∑ j ∈ Finset.range n,
      ((↑j : ℝ) / ↑n) ^ (M + 1) / ((2 : ℝ) ^ j * (↑n - ↑j)))
    =O[atTop] (fun n : ℕ => 1 / (↑n : ℝ) ^ (M + 2)) := by
  -- Each term ≤ j^{M+1}/(n^{M+1}·2^j) since 1/(n-j) ≤ 1.
  -- Sum ≤ (1/n^{M+1}) · C. But we need O(1/n^{M+2}).
  -- For j ≤ n/2: use remainder_term_le_polylog to get ≤ 2·j^{M+1}/(n^{M+2}·2^j).
  -- For j > n/2: each term ≤ 1/2^j, sum ≤ 2/2^{n/2} = o(1/n^k).
  -- Total: O(1/n^{M+2}).
  -- Split the sum at n/2. Low part: O(1/n^{M+2}) via remainder_term_le_polylog.
  -- High part: exponentially small, hence o(1/n^{M+2}).
  have h_low_part : (fun n : ℕ => ∑ j ∈ Finset.range (n / 2 + 1),
      ((↑j : ℝ) / ↑n) ^ (M + 1) / ((2 : ℝ) ^ j * (↑n - ↑j)))
    =O[atTop] (fun n : ℕ => 1 / (↑n : ℝ) ^ (M + 2)) := by
    apply Asymptotics.IsBigO.of_bound (2 * (2 * ↑(fubini (M + 1))))
    rw [Filter.eventually_atTop]
    refine ⟨2, fun n hn => ?_⟩
    have hn1 : 0 < n := by omega
    have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn1
    have hnn : 0 ≤ ∑ j ∈ Finset.range (n / 2 + 1),
        ((↑j : ℝ) / ↑n) ^ (M + 1) / ((2 : ℝ) ^ j * (↑n - ↑j)) :=
      Finset.sum_nonneg (fun j hj => remainder_term_nonneg n j M (by
        have := Finset.mem_range.mp hj; omega))
    rw [Real.norm_of_nonneg hnn, Real.norm_of_nonneg (by positivity)]
    calc ∑ j ∈ Finset.range (n / 2 + 1),
          ((↑j : ℝ) / ↑n) ^ (M + 1) / ((2 : ℝ) ^ j * (↑n - ↑j))
        ≤ ∑ j ∈ Finset.range (n / 2 + 1),
          2 * (↑j : ℝ) ^ (M + 1) / ((↑n : ℝ) ^ (M + 2) * (2 : ℝ) ^ j) := by
          apply Finset.sum_le_sum; intro j hj
          exact remainder_term_le_polylog n j M hn1
            (by have := Finset.mem_range.mp hj; omega)
            (by have := Finset.mem_range.mp hj; omega)
      _ = (2 / (↑n : ℝ) ^ (M + 2)) * ∑ j ∈ Finset.range (n / 2 + 1),
            (↑j : ℝ) ^ (M + 1) / (2 : ℝ) ^ j := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
          rw [mul_div_assoc]; ring_nf
      _ ≤ (2 / (↑n : ℝ) ^ (M + 2)) * (2 * ↑(fubini (M + 1))) := by
          gcongr
          calc ∑ j ∈ Finset.range (n / 2 + 1), (↑j : ℝ) ^ (M + 1) / (2 : ℝ) ^ j
              ≤ ∑' j : ℕ, (↑j : ℝ) ^ (M + 1) / (2 : ℝ) ^ j :=
                (polylog_summable _).sum_le_tsum _
                  (fun j _ => div_nonneg (pow_nonneg (Nat.cast_nonneg' j) _)
                    (pow_nonneg (by norm_num) _))
            _ = 2 * ↑(fubini (M + 1)) := (fubini_polylog _).tsum_eq
      _ = 2 * (2 * ↑(fubini (M + 1))) * (1 / (↑n : ℝ) ^ (M + 2)) := by
          field_simp
  have h_high_part : (fun n : ℕ => ∑ j ∈ Finset.Ico (n / 2 + 1) n,
      ((↑j : ℝ) / ↑n) ^ (M + 1) / ((2 : ℝ) ^ j * (↑n - ↑j)))
    =O[atTop] (fun n : ℕ => 1 / (↑n : ℝ) ^ (M + 2)) := by
    -- Bound: high sum ≤ 2/2^{n/2}, which is o(1/n^{M+2})
    -- First bound the sum by 2/2^{n/2+1}
    have h_bound : ∀ᶠ n : ℕ in atTop,
        ‖∑ j ∈ Finset.Ico (n / 2 + 1) n,
          ((↑j : ℝ) / ↑n) ^ (M + 1) / ((2 : ℝ) ^ j * (↑n - ↑j))‖ ≤
        2 / (2 : ℝ) ^ (n / 2 + 1) := by
      rw [Filter.eventually_atTop]
      refine ⟨2, fun n hn => ?_⟩
      have hn1 : 0 < n := by omega
      have hnn : 0 ≤ ∑ j ∈ Finset.Ico (n / 2 + 1) n,
          ((↑j : ℝ) / ↑n) ^ (M + 1) / ((2 : ℝ) ^ j * (↑n - ↑j)) :=
        Finset.sum_nonneg (fun j hj =>
          remainder_term_nonneg n j M ((Finset.mem_Ico.mp hj).2))
      rw [Real.norm_of_nonneg hnn]
      calc ∑ j ∈ Finset.Ico (n / 2 + 1) n,
            ((↑j : ℝ) / ↑n) ^ (M + 1) / ((2 : ℝ) ^ j * (↑n - ↑j))
          ≤ ∑ j ∈ Finset.Ico (n / 2 + 1) n, 1 / (2 : ℝ) ^ j := by
            apply Finset.sum_le_sum; intro j hj
            have hj' := Finset.mem_Ico.mp hj
            have hjn : (↑j : ℝ) < ↑n := Nat.cast_lt.mpr hj'.2
            have hnjpos : 1 ≤ (↑n : ℝ) - ↑j := by
              have : (↑j : ℝ) + 1 ≤ ↑n := by exact_mod_cast hj'.2
              linarith
            have h2j : (0 : ℝ) < (2 : ℝ) ^ j := pow_pos (by norm_num) j
            calc ((↑j : ℝ) / ↑n) ^ (M + 1) / ((2 : ℝ) ^ j * (↑n - ↑j))
                ≤ 1 / ((2 : ℝ) ^ j * (↑n - ↑j)) := by
                  gcongr
                  exact pow_le_one₀ (div_nonneg (Nat.cast_nonneg' j) (Nat.cast_nonneg' n))
                    (div_le_one_of_le₀ (le_of_lt hjn) (Nat.cast_nonneg' n))
              _ ≤ 1 / (2 : ℝ) ^ j := by
                  apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) h2j
                  exact le_mul_of_one_le_right (le_of_lt h2j) hnjpos
        _ ≤ ∑ j ∈ Finset.Ico (n / 2 + 1) n, ((1 : ℝ) / 2) ^ j := by
            apply Finset.sum_le_sum; intro j _; simp [one_div, inv_pow]
        _ ≤ ((1 : ℝ) / 2) ^ (n / 2 + 1) / (1 - (1 : ℝ) / 2) :=
            geom_sum_Ico_le_of_lt_one (by positivity) (by norm_num)
        _ = 2 / (2 : ℝ) ^ (n / 2 + 1) := by
            simp [one_div, pow_succ, inv_mul_eq_div]; ring
    -- Show 2/2^{n/2+1} = o(1/n^{M+2}) via n^k = o(2^n)
    -- Strategy: high_sum =O 1/2^{n/2+1}, and 1/2^{n/2+1} =o 1/n^{M+2}
    have h_geom_o : (fun n : ℕ => (2 : ℝ) / (2 : ℝ) ^ (n / 2 + 1))
        =o[atTop] (fun n : ℕ => 1 / (↑n : ℝ) ^ (M + 2)) := by
      rw [Asymptotics.isLittleO_iff]
      intro c hc
      have h_poly_sqrt := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) (M + 2)
        Real.one_lt_sqrt_two).bound (half_pos hc)
      rw [Filter.eventually_atTop] at h_poly_sqrt ⊢
      obtain ⟨N, hN⟩ := h_poly_sqrt
      refine ⟨max N 2, fun n hn => ?_⟩
      have hn2 : 2 ≤ n := le_of_max_le_right hn
      have hnN : N ≤ n := le_of_max_le_left hn
      have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
      have hnM : (0 : ℝ) < (↑n : ℝ) ^ (M + 2) := pow_pos hn' _
      have h2n : (0 : ℝ) < (2 : ℝ) ^ (n / 2 + 1) := pow_pos (by norm_num) _
      rw [Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (↑n : ℝ) ^ (M + 2)),
        show c * (1 / (↑n : ℝ) ^ (M + 2)) = c / (↑n : ℝ) ^ (M + 2) from by ring]
      -- From IH: n^{M+2} ≤ (c/2) * (√2)^n
      have hpoly := hN n hnN
      rw [Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg' n) _),
        Real.norm_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)] at hpoly
      -- Key: (√2)^n ≤ 2 * 2^{n/2} = 2^{n/2+1}
      have h_sqrt_bound : Real.sqrt 2 ^ n ≤ (2 : ℝ) ^ (n / 2 + 1) := by
        have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        have hsqrt_le : Real.sqrt 2 ≤ 2 := by
          calc Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
            _ = 2 := by rw [show (4:ℝ) = 2^2 from by norm_num, Real.sqrt_sq (by norm_num)]
        have hsqrt_pos : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
        calc Real.sqrt 2 ^ n
            = Real.sqrt 2 ^ (2 * (n / 2) + n % 2) := by congr 1; omega
          _ = Real.sqrt 2 ^ (2 * (n / 2)) * Real.sqrt 2 ^ (n % 2) := pow_add _ _ _
          _ = (Real.sqrt 2 ^ 2) ^ (n / 2) * Real.sqrt 2 ^ (n % 2) := by rw [pow_mul]
          _ = (2 : ℝ) ^ (n / 2) * Real.sqrt 2 ^ (n % 2) := by rw [hsq]
          _ ≤ (2 : ℝ) ^ (n / 2) * 2 := by
              apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
              calc Real.sqrt 2 ^ (n % 2) ≤ Real.sqrt 2 ^ 1 :=
                    pow_le_pow_right₀ Real.one_lt_sqrt_two.le (by omega)
                _ ≤ 2 := by rw [pow_one]; exact hsqrt_le
          _ = (2 : ℝ) ^ (n / 2 + 1) := by rw [pow_succ]
      -- Now: 2 * n^{M+2} ≤ c * (√2)^n ≤ c * 2^{n/2+1}
      rw [div_le_div_iff₀ h2n hnM]
      calc (2 : ℝ) * (↑n : ℝ) ^ (M + 2) ≤ c * Real.sqrt 2 ^ n := by linarith
        _ ≤ c * (2 : ℝ) ^ (n / 2 + 1) := by gcongr
    have h_big : (fun n : ℕ => ∑ j ∈ Finset.Ico (n / 2 + 1) n,
        ((↑j : ℝ) / ↑n) ^ (M + 1) / ((2 : ℝ) ^ j * (↑n - ↑j)))
      =O[atTop] (fun n : ℕ => (2 : ℝ) / (2 : ℝ) ^ (n / 2 + 1)) :=
      Asymptotics.IsBigO.of_bound' (h_bound.mono fun n hn =>
        hn.trans (le_abs_self _))
    exact (h_big.trans_isLittleO h_geom_o).isBigO
  -- Combine: the full sum equals low + high eventually
  have h_eq : (fun n : ℕ => ∑ j ∈ Finset.range n,
      ((↑j : ℝ) / ↑n) ^ (M + 1) / ((2 : ℝ) ^ j * (↑n - ↑j))) =ᶠ[atTop]
    (fun n => (∑ j ∈ Finset.range (n / 2 + 1),
        ((↑j : ℝ) / ↑n) ^ (M + 1) / ((2 : ℝ) ^ j * (↑n - ↑j))) +
      ∑ j ∈ Finset.Ico (n / 2 + 1) n,
        ((↑j : ℝ) / ↑n) ^ (M + 1) / ((2 : ℝ) ^ j * (↑n - ↑j))) := by
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    exact ⟨2, fun n hn =>
      (Finset.sum_range_add_sum_Ico _ (by omega : n / 2 + 1 ≤ n)).symm⟩
  exact (h_low_part.add h_high_part).congr' h_eq.symm (Filter.EventuallyEq.refl _ _)

private lemma inv_pow_isLittleO (M : ℕ) :
    (fun n : ℕ => 1 / (↑n : ℝ) ^ (M + 2))
    =o[atTop] (fun n : ℕ => 1 / (↑n : ℝ) ^ (M + 1)) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  rw [Filter.eventually_atTop]
  refine ⟨max (⌈1 / c⌉₊ + 1) 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  have hnc : ⌈1 / c⌉₊ + 1 ≤ n := le_of_max_le_left hn
  have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  have hnM1 : (0 : ℝ) < (↑n : ℝ) ^ (M + 1) := pow_pos hn' _
  have hnM2 : (0 : ℝ) < (↑n : ℝ) ^ (M + 2) := pow_pos hn' _
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
    show M + 2 = (M + 1) + 1 from by omega, pow_succ,
    show (1 : ℝ) / ((↑n : ℝ) ^ (M + 1) * ↑n) = (1 / ↑n) * (1 / (↑n : ℝ) ^ (M + 1)) from by
      field_simp]
  have h1n : 1 / (↑n : ℝ) ≤ c := by
    rw [one_div, inv_le_comm₀ hn' hc, (one_div c).symm]
    calc (1 / c : ℝ) ≤ ↑(⌈1 / c⌉₊) := Nat.le_ceil _
      _ ≤ ↑(⌈1 / c⌉₊ + 1) := by exact_mod_cast Nat.le_succ _
      _ ≤ ↑n := by exact_mod_cast hnc
  exact mul_le_mul_of_nonneg_right h1n (by positivity)

private lemma geom_remainder_isLittleO (M : ℕ) :
    (fun n : ℕ => ∑ j ∈ Finset.range n,
      ((↑j : ℝ) / ↑n) ^ (M + 1) / ((2 : ℝ) ^ j * (↑n - ↑j)))
    =o[atTop] (fun n : ℕ => 1 / (↑n : ℝ) ^ (M + 1)) :=
  (remainder_sum_isBigO M).trans_isLittleO (inv_pow_isLittleO M)

/-- The Fubini recurrence restated over `Finset.range`. -/
private lemma fubini_eq_sum_range (i : ℕ) :
    fubini (i + 1) = ∑ m ∈ Finset.range (i + 1), (i + 1).choose m * fubini m := by
  conv_lhs => unfold fubini
  exact Fin.sum_univ_eq_sum_range (fun k => (i + 1).choose k * fubini k) (i + 1)

/-- Binomial-Fubini identity (ℕ): `∑_{m=0}^i C(i,m)·fubini(m) = 2·fubini(i)` for `i ≥ 1`.
    The first `i` terms equal `fubini(i)` by the recurrence; the last term
    `C(i,i)·fubini(i) = fubini(i)`. -/
private lemma binomial_fubini_nat (i : ℕ) (hi : 1 ≤ i) :
    ∑ m ∈ Finset.range (i + 1), i.choose m * fubini m = 2 * fubini i := by
  rw [Finset.sum_range_succ, Nat.choose_self, one_mul]
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [fubini_eq_sum_range j]
  omega

/-- Binomial-Fubini identity (ℝ). -/
private lemma binomial_fubini (i : ℕ) (hi : 1 ≤ i) :
    (∑ m ∈ Finset.range (i + 1),
      ↑(i.choose m) * ↑(fubini m) : ℝ) = 2 * ↑(fubini i) := by
  exact_mod_cast binomial_fubini_nat i hi

/-- For `i = 0`: the sum is 1 ≤ 2·fubini(0) = 2. -/
private lemma binomial_fubini_le (i : ℕ) :
    (∑ m ∈ Finset.range (i + 1),
      ↑(i.choose m) * ↑(fubini m) : ℝ) ≤ 2 * ↑(fubini i) := by
  cases i with
  | zero => simp [fubini_zero]
  | succ j => exact le_of_eq (binomial_fubini (j + 1) (by omega))

/-- Summability of the shifted polylog `∑_{k≥0} (k+1)^i / 2^k`. -/
private lemma shifted_polylog_summable (i : ℕ) :
    Summable (fun k : ℕ => (↑(k + 1) : ℝ) ^ i / (2 : ℝ) ^ k) := by
  convert (((summable_nat_add_iff 1).mpr (polylog_summable i)).const_smul (2 : ℝ)) using 1
  ext k; rw [smul_eq_mul, pow_succ]; field_simp

/-- `∑_{k≥0} (k+1)^i / 2^k ≤ 4·fubini(i)`. Equality for `i ≥ 1`. -/
private lemma shifted_polylog_le (i : ℕ) :
    ∑' k : ℕ, (↑(k + 1) : ℝ) ^ i / (2 : ℝ) ^ k ≤ 4 * ↑(fubini i) := by
  cases i with
  | zero =>
    have h : ∑' k : ℕ, (↑(k + 1) : ℝ) ^ 0 / (2 : ℝ) ^ k = 2 := by
      have : (fun k : ℕ => (↑(k + 1) : ℝ) ^ 0 / (2 : ℝ) ^ k) =
          (fun k => ((1 : ℝ) / 2) ^ k) := by
        ext k; simp [pow_zero, one_div, inv_pow]
      rw [this, tsum_geometric_two]
    rw [h, fubini_zero, Nat.cast_one, mul_one]; norm_num
  | succ m =>
    have h1 := polylog_shift_tsum (m + 1) (by omega)
    have h2 := (fubini_polylog (m + 1)).tsum_eq
    linarith

private lemma polylog_tail_bound (i n : ℕ) (hn : 1 ≤ n) :
    |∑ j ∈ Finset.range n, (↑j : ℝ) ^ i / (2 : ℝ) ^ j - 2 * ↑(fubini i)| ≤
    4 * ↑(fubini i) * (↑n : ℝ) ^ i / (2 : ℝ) ^ n := by
  set f : ℕ → ℝ := (fun j => (↑j : ℝ) ^ i / (2 : ℝ) ^ j) with hf_def
  have h_summ := polylog_summable i
  have h_tsum : ∑' (j : ℕ), f j = 2 * ↑(fubini i) := (fubini_polylog i).tsum_eq
  have h_add := h_summ.sum_add_tsum_nat_add n
  have h_err : ∑ j ∈ Finset.range n, f j - 2 * ↑(fubini i) =
      -(∑' (k : ℕ), f (k + n)) := by linarith
  have h_tail_nn : 0 ≤ ∑' (k : ℕ), f (k + n) :=
    tsum_nonneg (fun k => by simp only [hf_def]; positivity)
  rw [h_err, abs_neg, abs_of_nonneg h_tail_nn]
  have h_tail_summ : Summable (fun k : ℕ => f (k + n)) :=
    (summable_nat_add_iff n).mpr h_summ
  set g : ℕ → ℝ := (fun k => (↑n : ℝ) ^ i / (2 : ℝ) ^ n * ((↑(k + 1) : ℝ) ^ i / (2 : ℝ) ^ k))
  have h_term : ∀ k : ℕ, f (k + n) ≤ g k := by
    intro k
    show (↑(k + n) : ℝ) ^ i / (2 : ℝ) ^ (k + n) ≤
      (↑n : ℝ) ^ i / (2 : ℝ) ^ n * ((↑(k + 1) : ℝ) ^ i / (2 : ℝ) ^ k)
    have hle : (↑(k + n) : ℝ) ^ i ≤ ((↑n : ℝ) * ↑(k + 1)) ^ i := by
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      have : (k + n : ℕ) ≤ n * (k + 1) := by nlinarith
      exact_mod_cast this
    calc (↑(k + n) : ℝ) ^ i / (2 : ℝ) ^ (k + n)
        ≤ ((↑n : ℝ) * ↑(k + 1)) ^ i / (2 : ℝ) ^ (k + n) :=
          div_le_div_of_nonneg_right hle (pow_nonneg two_pos.le _)
      _ = g k := by simp only [g, mul_pow, pow_add]; ring
  have h_g_summ : Summable g := (shifted_polylog_summable i).mul_left _
  calc ∑' (k : ℕ), f (k + n)
      ≤ ∑' (k : ℕ), g k := h_tail_summ.tsum_le_tsum h_term h_g_summ
    _ = (↑n : ℝ) ^ i / (2 : ℝ) ^ n *
        ∑' (k : ℕ), (↑(k + 1) : ℝ) ^ i / (2 : ℝ) ^ k := tsum_mul_left ..
    _ ≤ (↑n : ℝ) ^ i / (2 : ℝ) ^ n * (4 * ↑(fubini i)) := by
        gcongr; exact shifted_polylog_le i
    _ = 4 * ↑(fubini i) * (↑n : ℝ) ^ i / (2 : ℝ) ^ n := by ring

-- The partial-sum error ∑_{j<n} j^i/2^j - 2·fubini(i) is O(n^i/2^n),
-- hence exponentially small. After multiplying by 2^n/n^{i+1} and summing
-- over i ≤ M, the total contribution is O(1/n) = o(2^n/n^{M+1}).
private lemma polylog_partial_error_isLittleO (M : ℕ) :
    (fun n : ℕ => (2 : ℝ) ^ n / ↑n *
      ∑ i ∈ Finset.range (M + 1),
        (∑ j ∈ Finset.range n, (↑j : ℝ) ^ i / (2 : ℝ) ^ j -
          2 * ↑(fubini i)) / (↑n : ℝ) ^ i)
    =o[atTop] (fun n : ℕ => (2 : ℝ) ^ n / (↑n : ℝ) ^ (M + 1)) := by
  -- Strategy: show f =O (1/n) and 1/n =o (2^n/n^{M+1}).
  -- Part 1: f =O (1/n). The error |partial_i - tsum_i| is a tail of summable series,
  -- bounded by the tsum tail which decays exponentially. For a crude bound:
  -- |err_i(n)| ≤ tsum_{j≥n} j^i/2^j. After dividing by n^i and multiplying by 2^n/n,
  -- we get ≤ C/n for each i. Sum over i gives (M+1)C/n.
  have h_bigO : (fun n : ℕ => (2 : ℝ) ^ n / ↑n *
      ∑ i ∈ Finset.range (M + 1),
        (∑ j ∈ Finset.range n, (↑j : ℝ) ^ i / (2 : ℝ) ^ j -
          2 * ↑(fubini i)) / (↑n : ℝ) ^ i)
    =O[atTop] (fun n : ℕ => (1 : ℝ) / ↑n) := by
    -- Tail bound: |partial_i(n) - tsum_i| ≤ C * n^i / 2^n
    -- This cancels the 2^n in the numerator, leaving O(1/n).
    have h_tail := polylog_tail_bound
    apply Asymptotics.IsBigO.of_bound (4 * ∑ i ∈ Finset.range (M + 1), ↑(fubini i))
    rw [Filter.eventually_atTop]
    refine ⟨1, fun n hn => ?_⟩
    have hn1 : 0 < n := by omega
    have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn1
    have hnn : (↑n : ℝ) ≠ 0 := hn'.ne'
    have h2n : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) _
    -- Bound: |f(n)| ≤ (2^n/n) * ∑ 4*fubini(i)/2^n = 4*(∑ fubini(i))/n
    -- First bound the inner sum
    have h_inner : |∑ i ∈ Finset.range (M + 1),
        (∑ j ∈ Finset.range n, (↑j : ℝ) ^ i / (2 : ℝ) ^ j - 2 * ↑(fubini i)) / (↑n : ℝ) ^ i| ≤
        ∑ i ∈ Finset.range (M + 1), 4 * ↑(fubini i) / (2 : ℝ) ^ n := by
      calc |∑ i ∈ Finset.range (M + 1), _|
          ≤ ∑ i ∈ Finset.range (M + 1),
            |(_ : ℝ) / (↑n : ℝ) ^ i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range (M + 1),
            4 * ↑(fubini i) / (2 : ℝ) ^ n := by
            apply Finset.sum_le_sum; intro i _
            rw [abs_div, abs_of_nonneg (show 0 ≤ (↑n : ℝ) ^ i from pow_nonneg (Nat.cast_nonneg' n) i)]
            have htail := h_tail i n (by omega)
            have hni : (0:ℝ) < (↑n : ℝ) ^ i := pow_pos hn' i
            rw [div_le_div_iff₀ hni (pow_pos (by norm_num : (0:ℝ) < 2) n)]
            have h2nn : (0:ℝ) < (2:ℝ) ^ n := pow_pos (by norm_num) n
            have := mul_le_mul_of_nonneg_right htail h2nn.le
            rw [div_mul_cancel₀ _ h2nn.ne'] at this
            linarith
    -- |f(n)| ≤ (2^n/n) * (∑ 4*fubini(i)/2^n) = 4*(∑ fubini(i))/n
    have h_sum_bound : ∑ i ∈ Finset.range (M + 1), 4 * ↑(fubini i) / (2 : ℝ) ^ n =
        4 * (∑ i ∈ Finset.range (M + 1), ↑(fubini i)) / (2 : ℝ) ^ n := by
      rw [show ∀ s : Finset ℕ, ∀ f : ℕ → ℝ, ∀ c : ℝ,
          4 * (∑ i ∈ s, f i) / c = ∑ i ∈ s, 4 * f i / c from
          fun s f c => by rw [Finset.mul_sum, Finset.sum_div]]
    calc ‖(2 : ℝ) ^ n / ↑n * ∑ i ∈ Finset.range (M + 1),
          (∑ j ∈ Finset.range n, (↑j : ℝ) ^ i / (2 : ℝ) ^ j - 2 * ↑(fubini i)) / (↑n : ℝ) ^ i‖
        ≤ (2 : ℝ) ^ n / ↑n * |∑ i ∈ Finset.range (M + 1),
          (∑ j ∈ Finset.range n, (↑j : ℝ) ^ i / (2 : ℝ) ^ j - 2 * ↑(fubini i)) / (↑n : ℝ) ^ i| := by
          rw [norm_mul, Real.norm_of_nonneg
            (div_nonneg (pow_nonneg (by norm_num) _) (Nat.cast_nonneg' n)),
            Real.norm_eq_abs]
      _ ≤ (2 : ℝ) ^ n / ↑n * (4 * (∑ i ∈ Finset.range (M + 1), ↑(fubini i)) / (2 : ℝ) ^ n) := by
          gcongr; rw [← h_sum_bound]; exact h_inner
      _ = 4 * (∑ i ∈ Finset.range (M + 1), ↑(fubini i)) / ↑n := by field_simp
      _ = (4 * ∑ i ∈ Finset.range (M + 1), ↑(fubini i)) * ‖(1 : ℝ) / ↑n‖ := by
          rw [Real.norm_of_nonneg (by positivity)]; ring
  -- Part 2: 1/n =o (2^n/n^{M+1}) since n^M =o 2^n
  have h_littleO : (fun n : ℕ => (1 : ℝ) / ↑n)
      =o[atTop] (fun n : ℕ => (2 : ℝ) ^ n / (↑n : ℝ) ^ (M + 1)) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have h_poly := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) M
      (by norm_num : (1:ℝ) < 2)).bound hc
    rw [Filter.eventually_atTop] at h_poly ⊢
    obtain ⟨N, hN⟩ := h_poly
    refine ⟨max N 1, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := le_of_max_le_right hn
    have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    have hpoly := hN n (le_of_max_le_left hn)
    rw [Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg' n) _),
      Real.norm_of_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)] at hpoly
    rw [show (1:ℝ) / ↑n = (↑n : ℝ) ^ M / (↑n : ℝ) ^ (M + 1) from by
      rw [pow_succ]; field_simp]
    rw [show c * ((2 : ℝ) ^ n / (↑n : ℝ) ^ (M + 1)) =
      c * (2 : ℝ) ^ n / (↑n : ℝ) ^ (M + 1) from by ring]
    exact div_le_div_of_nonneg_right hpoly (pow_nonneg (Nat.cast_nonneg' n) _)
  exact h_bigO.trans_isLittleO h_littleO

-- Algebraic identity: S(n) decomposes via geometric expansion
private lemma S_decompose (n M : ℕ) (hn : 0 < n) :
    S n = (2 : ℝ) ^ n / ↑n *
      ∑ i ∈ Finset.range (M + 1),
        (∑ j ∈ Finset.range n, (↑j : ℝ) ^ i / (2 : ℝ) ^ j) / (↑n : ℝ) ^ i +
    (2 : ℝ) ^ n * ∑ j ∈ Finset.range n,
      ((↑j : ℝ) / ↑n) ^ (M + 1) / ((2 : ℝ) ^ j * (↑n - ↑j)) := by
  rw [S_reindex n hn]
  have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hnn : (↑n : ℝ) ≠ 0 := hn'.ne'
  -- Substitute geom_expand for 1/(n-j) in each term
  have h_expand : ∀ j ∈ Finset.range n,
      1 / ((2 : ℝ) ^ j * (↑n - ↑j)) =
      1 / ↑n * (∑ i ∈ Finset.range (M + 1), ((↑j : ℝ) / ↑n) ^ i) / (2 : ℝ) ^ j +
      ((↑j : ℝ) / ↑n) ^ (M + 1) / ((2 : ℝ) ^ j * (↑n - ↑j)) := by
    intro j hj
    have hj' : j < n := Finset.mem_range.mp hj
    have hjn : (↑j : ℝ) < ↑n := Nat.cast_lt.mpr hj'
    have hsub : (0 : ℝ) < ↑n - ↑j := by linarith
    have h2j : (0 : ℝ) < (2 : ℝ) ^ j := pow_pos (by norm_num) _
    have h_ge := geom_expand n j M hn hj'
    -- 1/(2^j(n-j)) = (1/(n-j)) / 2^j
    rw [show 1 / ((2 : ℝ) ^ j * (↑n - ↑j)) =
      1 / (↑n - ↑j) / (2 : ℝ) ^ j from by field_simp]
    rw [h_ge]
    field_simp
  -- Substitute into each term and split
  have h_sum_eq : ∑ j ∈ Finset.range n, 1 / ((2 : ℝ) ^ j * (↑n - ↑j)) =
      ∑ j ∈ Finset.range n,
        (1 / ↑n * (∑ i ∈ Finset.range (M + 1), ((↑j : ℝ) / ↑n) ^ i) / (2 : ℝ) ^ j +
        ((↑j : ℝ) / ↑n) ^ (M + 1) / ((2 : ℝ) ^ j * (↑n - ↑j))) :=
    Finset.sum_congr rfl h_expand
  rw [h_sum_eq, Finset.mul_sum]
  -- Distribute 2^n*(a+b) = 2^n*a + 2^n*b inside each term
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · -- LHS: ∑_j 2^n/n * (∑_i (j/n)^i / 2^j)
    -- Factor out 2^n/n, expand (j/n)^i, swap sums
    have : ∀ j ∈ Finset.range n,
        (2 : ℝ) ^ n * ((1 / ↑n * ∑ i ∈ Finset.range (M + 1), ((↑j : ℝ) / ↑n) ^ i) / (2 : ℝ) ^ j) =
        (2 : ℝ) ^ n / ↑n * ∑ i ∈ Finset.range (M + 1), (↑j : ℝ) ^ i / ((↑n : ℝ) ^ i * (2 : ℝ) ^ j) := by
      intro j hj
      have h2j : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
      rw [show (1 / ↑n * ∑ i ∈ Finset.range (M + 1), ((↑j : ℝ) / ↑n) ^ i) / (2 : ℝ) ^ j =
        1 / (↑n * (2 : ℝ) ^ j) * ∑ i ∈ Finset.range (M + 1), ((↑j : ℝ) / ↑n) ^ i from by
          field_simp]
      -- Both sides: sum over i of scalar terms. Match term by term.
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [div_pow]; field_simp
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
    congr 1
    -- ∑_j ∑_i j^i/(n^i*2^j) = ∑_i (∑_j j^i/2^j)/n^i
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro j _
    field_simp
  · -- Remainder: factor 2^n back out
    rw [← Finset.mul_sum]

theorem S_expansion (M : ℕ) :
    (fun n : ℕ => S n -
      (2 : ℝ) ^ (n + 1) / ↑n *
        ∑ i ∈ Finset.range (M + 1), ↑(fubini i) / (↑n : ℝ) ^ i)
    =o[atTop] (fun n : ℕ => (2 : ℝ) ^ n / (↑n : ℝ) ^ (M + 1)) := by
  -- S(n) = main_approx + geom_remainder + polylog_error
  -- where main_approx uses partial polylogs, and we replace them by fubini.
  have h_geom_rem := geom_remainder_isLittleO M
  have h_polylog_err := polylog_partial_error_isLittleO M
  -- The error splits into two o-terms
  have h_eq : ∀ᶠ n : ℕ in atTop,
      S n - (2 : ℝ) ^ (n + 1) / ↑n *
        ∑ i ∈ Finset.range (M + 1), ↑(fubini i) / (↑n : ℝ) ^ i =
      ((2 : ℝ) ^ n / ↑n *
        ∑ i ∈ Finset.range (M + 1),
          (∑ j ∈ Finset.range n, (↑j : ℝ) ^ i / (2 : ℝ) ^ j -
            2 * ↑(fubini i)) / (↑n : ℝ) ^ i) +
      (2 : ℝ) ^ n * ∑ j ∈ Finset.range n,
        ((↑j : ℝ) / ↑n) ^ (M + 1) / ((2 : ℝ) ^ j * (↑n - ↑j)) := by
    rw [Filter.eventually_atTop]
    refine ⟨1, fun n hn => ?_⟩
    have hn1 : 0 < n := by omega
    have hn' : (↑n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn1).ne'
    rw [S_decompose n M (by omega)]
    -- Cancel the identical geom remainder terms
    -- Cancel the identical geom remainder, then use sum linearity
    suffices h : ∀ c : ℝ,
        c * ∑ i ∈ Finset.range (M + 1),
          (∑ j ∈ Finset.range n, (↑j : ℝ) ^ i / (2 : ℝ) ^ j) / (↑n : ℝ) ^ i -
        c * 2 * ∑ i ∈ Finset.range (M + 1), ↑(fubini i) / (↑n : ℝ) ^ i =
        c * ∑ i ∈ Finset.range (M + 1),
          (∑ j ∈ Finset.range n, (↑j : ℝ) ^ i / (2 : ℝ) ^ j - 2 * ↑(fubini i)) / (↑n : ℝ) ^ i by
      have := h ((2 : ℝ) ^ n / ↑n)
      rw [show (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n from by rw [pow_succ]; ring,
        show 2 * (2 : ℝ) ^ n / ↑n = (2 : ℝ) ^ n / ↑n * 2 from by ring]
      linarith
    intro c
    rw [show c * 2 * _ = c * (2 * ∑ i ∈ Finset.range (M + 1), ↑(fubini i) / (↑n : ℝ) ^ i) from by ring]
    rw [← mul_sub]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _; ring
  have h_geom_scaled : (fun n : ℕ => (2 : ℝ) ^ n * ∑ j ∈ Finset.range n,
      ((↑j : ℝ) / ↑n) ^ (M + 1) / ((2 : ℝ) ^ j * (↑n - ↑j)))
    =o[atTop] (fun n : ℕ => (2 : ℝ) ^ n / (↑n : ℝ) ^ (M + 1)) :=
    ((Asymptotics.isBigO_refl (fun n : ℕ => (2 : ℝ) ^ n) atTop).mul_isLittleO
      h_geom_rem).congr (fun n => rfl) (fun n => by rw [one_div]; ring)
  -- Combine via h_eq
  have h_sum := h_polylog_err.add h_geom_scaled
  exact h_sum.congr' (h_eq.mono fun n hn => hn.symm) (Filter.EventuallyEq.refl _ _)

end DiscreteLaplace

/-! ## Main results -/
section Main

/-- **Cloitre's conjecture (2002).** For any truncation order `M`,
    `a(n) = (2^{n+1}/n) · ∑_{m=0}^M fubini(m)/n^m + o(2^n/n^{M+1})`. -/
theorem asymptotic_expansion (M : ℕ) :
    (fun n : ℕ => a n -
      (2 : ℝ) ^ (n + 1) / ↑n *
        ∑ i ∈ Finset.range (M + 1), ↑(fubini i) / (↑n : ℝ) ^ i)
    =o[atTop] (fun n : ℕ => (2 : ℝ) ^ n / (↑n : ℝ) ^ (M + 1)) := by
  have h1 := a_sub_S_isLittleO M
  have h2 := S_expansion M
  have h3 : (fun n : ℕ => (↑n : ℝ)) =o[atTop]
      (fun n : ℕ => (2 : ℝ) ^ n / (↑n : ℝ) ^ (M + 1)) := by
    have hkey : (fun n : ℕ => (↑n : ℝ) ^ (M + 1) * (↑n : ℝ)) =o[atTop]
        (fun n : ℕ => (2 : ℝ) ^ n) := by
      have := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) (M + 2)
        (by norm_num : (1:ℝ) < 2)
      refine this.congr_left (fun n => ?_)
      rw [show M + 2 = M + 1 + 1 from by omega, pow_succ]
    have hne : ∀ᶠ n : ℕ in atTop, (↑n : ℝ) ^ (M + 1) ≠ 0 :=
      Filter.eventually_atTop.mpr ⟨1, fun n hn =>
        pow_ne_zero _ (Nat.cast_ne_zero.mpr (by positivity))⟩
    rwa [isLittleO_mul_iff_isLittleO_div hne] at hkey
  have h1' : (fun n : ℕ => a n - (S n - ↑n)) =o[atTop]
      (fun n : ℕ => (2 : ℝ) ^ n / (↑n : ℝ) ^ (M + 1)) := by
    refine h1.trans_isBigO (Asymptotics.IsBigO.of_bound 1 ?_)
    rw [Filter.eventually_atTop]
    exact ⟨1, fun n hn => by
      rw [one_mul]
      rw [Real.norm_of_nonneg (div_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
        (pow_nonneg (Nat.cast_nonneg' n) _))]
      rw [Real.norm_of_nonneg (div_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
        (pow_nonneg (Nat.cast_nonneg' n) _))]
      have hn' : (1 : ℝ) ≤ ↑n := by exact_mod_cast hn
      apply div_le_div_of_nonneg_left (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
        (pow_pos (by linarith) _) ?_
      calc (↑n : ℝ) ^ (M + 1) ≤ (↑n : ℝ) ^ (M + 1) * ↑n :=
            le_mul_of_one_le_right (pow_nonneg (Nat.cast_nonneg' n) _) hn'
        _ = (↑n : ℝ) ^ (M + 2) := by ring_nf⟩
  have key : (fun n : ℕ => a n -
      (2 : ℝ) ^ (n + 1) / ↑n *
        ∑ i ∈ Finset.range (M + 1), ↑(fubini i) / (↑n : ℝ) ^ i) =
    (fun n => (a n - (S n - ↑n)) +
      ((S n - (2 : ℝ) ^ (n + 1) / ↑n *
        ∑ i ∈ Finset.range (M + 1), ↑(fubini i) / (↑n : ℝ) ^ i) - ↑n)) := by
    ext n; ring
  rw [key]
  exact h1'.add (h2.sub h3)

/-- Leading-term asymptotics: `a(n) ∼ 2^{n+1}/n`. -/
theorem leading_term :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ => a n)
      (fun n : ℕ => (2 : ℝ) ^ (n + 1) / (↑n : ℝ)) := by
  rw [Asymptotics.IsEquivalent]
  have h := asymptotic_expansion 0
  have hsimp : (fun n : ℕ => a n - (2 : ℝ) ^ (n + 1) / ↑n *
      ∑ i ∈ Finset.range (0 + 1), ↑(fubini i) / (↑n : ℝ) ^ i) =
    (fun n : ℕ => a n - (2 : ℝ) ^ (n + 1) / ↑n) := by
    ext n; simp [fubini_zero]
  rw [hsimp] at h
  refine (h.trans_isBigO ?_).congr_left (fun n => by simp [Pi.sub_apply])
  apply Asymptotics.IsBigO.of_bound 1
  rw [Filter.eventually_atTop]
  exact ⟨1, fun n hn => by
    rw [one_mul, show (0 : ℕ) + 1 = 1 from by omega, pow_one]
    rw [Real.norm_of_nonneg (div_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
      (Nat.cast_nonneg' n))]
    rw [Real.norm_of_nonneg (div_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
      (Nat.cast_nonneg' n))]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg' n)
    rw [pow_succ]
    exact le_mul_of_one_le_right (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) _) (by norm_num)⟩

end Main


end A051293
