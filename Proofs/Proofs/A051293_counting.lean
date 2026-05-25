import Mathlib
import Proofs.A051293_analytic
import Proofs.Zumkeller

/-!
# A051293: Combinatorial foundation

This file bridges the combinatorial definition of A051293 — nonempty
subsets of {1,…,n} with integer mean — to the divisor-sum formula
`a(n) = Σ_{k=1}^n (b(k) − 1)` used in `A051293.lean`.

## Structure

The proof of Cloitre's conjecture requires three layers:

1. **(B) DFT counting**: `b(k) = (1/k) Σ_{d|k, d odd} φ(d)·2^{k/d}`
   counts subsets of `{1,…,k}` with sum ≡ 0 mod k.
   (Stanley, Enumerative Combinatorics Vol 1, Exercise 1.105)

2. **(A) Per-k identity**: the number of nonempty subsets of `{1,…,k}`
   with sum ≡ 0 mod k equals the number of subsets of `{1,…,k}`
   containing k with integer mean.
   (Observed by Wiseman, OEIS A063776, 2019; no published proof)

3. **Summation**: summing (A) over `k = 1,…,n` and partitioning
   integer-mean subsets by their maximum element yields
   `a_comb(n) = Σ (b(k) − 1) = a(n)`.

Combined with the asymptotic expansion from `A051293.lean`, this
gives Cloitre's conjecture as originally stated.
-/

open Finset BigOperators

namespace A051293

section CombDefs

/-- The set of nonempty subsets of `Finset.range n` (representing
    {0,…,n-1}) whose elements, shifted by 1, have an integer average.
    A subset S has integer mean iff |S| divides Σ_{i ∈ S} (i+1). -/
def intMeanSubsets (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.range n).powerset.filter (fun S =>
    S.Nonempty ∧ S.card ∣ (S.sum (· + 1)))

/-- `a_comb(n) = #{nonempty S ⊆ {1,…,n} : mean(S) ∈ ℤ}`. -/
def a_comb (n : ℕ) : ℕ := (intMeanSubsets n).card

end CombDefs

section StepB

/-! ### Step (B): DFT counting formula (roots of unity filter)

`b_comb(k) = b(k)` where `b(k) = (1/k) ∑_{d|k, d odd} φ(d) · 2^{k/d}`.

Proof outline:
1. Character orthogonality: `∑_{r<k} ζ^{r·n} = k·[k|n]`
2. Factor: `∑_{S⊆range k} ζ^{r·sum_S} = ∏_{m=0}^{k-1}(1 + ζ^{r(m+1)})` (Finset.prod_add)
3. Evaluate: `∏_{m=0}^{n-1}(1+η^m) = 2` for odd n, `0` for even n
   (substitute x=-1 into `x^n-1 = ∏(x-η^m)`)
4. Collect by gcd: group r by gcd(r,k), count with φ, sum over odd divisors

Key Mathlib tools: IsPrimitiveRoot, Finset.prod_add, Nat.totient,
Polynomial.cyclotomic, Nat.sum_totient.

Key Lean idiom for ℕ→ℤ casts with (k-1):
  `rw [show (↑k : ℤ) - 1 = ↑(k-1) from (Int.ofNat_sub hk).symm]; exact_mod_cast h`
For omega-resistant `(k-1)*c` identities:
  `nlinarith [Nat.sub_add_cancel hk, Nat.mul_sub_one k c]`
-/

private lemma prod_one_add_nthRoots (n : ℕ) (hn : 0 < n) :
    ∏ ζ ∈ Polynomial.nthRootsFinset n (1 : ℂ), (1 + ζ) =
    if n % 2 = 1 then 2 else 0 := by
  have hprim := Complex.isPrimitiveRoot_exp n (by omega)
  have hfact := Polynomial.X_pow_sub_one_eq_prod hn hprim
  have heval := congr_arg (Polynomial.eval (-1)) hfact
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_C] at heval
  have hcard : (Polynomial.nthRootsFinset n (1 : ℂ)).card = n := hprim.card_nthRootsFinset
  have h_neg : ∏ ζ ∈ Polynomial.nthRootsFinset n (1 : ℂ), (-1 - ζ) =
      (-1) ^ n * ∏ ζ ∈ Polynomial.nthRootsFinset n (1 : ℂ), (1 + ζ) := by
    conv_rhs => rw [show (-1 : ℂ) ^ n = (-1) ^ (Polynomial.nthRootsFinset n (1 : ℂ)).card from by
      rw [hcard]]
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    congr 1; ext ζ; ring
  rw [h_neg] at heval
  have h_pow_ne : ((-1 : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h_solve : ∏ ζ ∈ Polynomial.nthRootsFinset n (1 : ℂ), (1 + ζ) =
      ((-1) ^ n - 1) / (-1) ^ n := by
    rw [eq_div_iff h_pow_ne, mul_comm]; exact heval.symm
  rw [h_solve]
  split_ifs with h
  · rw [Odd.neg_one_pow ⟨n / 2, by omega⟩]; norm_num
  · rw [Even.neg_one_pow ⟨n / 2, by omega⟩]; norm_num

private lemma char_orthogonality (k : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ k) (n : ℕ) :
    ∑ r ∈ Finset.range k, ζ ^ (r * n) = if k ∣ n then (k : ℂ) else 0 := by
  simp_rw [show ∀ r, ζ ^ (r * n) = (ζ ^ n) ^ r from fun r => by rw [← pow_mul, mul_comm]]
  split_ifs with h
  · have hone : ζ ^ n = 1 := by
      obtain ⟨m, hm⟩ := h; rw [hm, pow_mul, hζ.pow_eq_one, one_pow]
    simp [hone]
  · have hne : ζ ^ n ≠ 1 := fun h1 => h (hζ.dvd_of_pow_eq_one n h1)
    rw [geom_sum_eq hne k]
    have : (ζ ^ n) ^ k = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    simp [this]

private lemma b_comb_as_char_sum (k : ℕ) (_hk : 0 < k) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ k) :
    (b_comb k : ℂ) = (1 / k) * ∑ r ∈ Finset.range k,
      ∏ m ∈ Finset.range k, (1 + ζ ^ (r * (m + 1))) := by
  have h_expand : ∀ r, ∏ m ∈ Finset.range k, (1 + ζ ^ (r * (m + 1))) =
      ∑ S ∈ (Finset.range k).powerset, ζ ^ (r * S.sum (· + 1)) := by
    intro r
    simp_rw [show ∀ m, (1 : ℂ) + ζ ^ (r * (m + 1)) = ζ ^ (r * (m + 1)) + 1 from
      fun m => add_comm _ _]
    rw [Finset.prod_add]
    congr 1; ext S; simp only [Finset.prod_const_one, mul_one]
    rw [show r * S.sum (· + 1) = ∑ m ∈ S, (r * (m + 1)) from by rw [Finset.mul_sum]]
    rw [← Finset.prod_pow_eq_pow_sum]
  simp_rw [h_expand]
  rw [Finset.sum_comm]
  simp_rw [char_orthogonality k ζ hζ]
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hk_ne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [one_div, mul_comm, mul_inv_cancel_right₀ hk_ne]
  simp only [b_comb, modSubsets]

private lemma prod_range_periodic {α : Type*} [CommMonoid α] (f : ℕ → α) (d q : ℕ)
    (hf : ∀ m, f (m + q) = f m) :
    ∏ m ∈ Finset.range (d * q), f m = (∏ m ∈ Finset.range q, f m) ^ d := by
  induction d with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, Finset.prod_range_add, ih, pow_succ]
    congr 1
    apply Finset.prod_congr rfl
    intro m _
    have : ∀ p, f (m + p * q) = f m := by
      intro p; induction p with
      | zero => simp
      | succ p ihp =>
        have h1 : f (m + p * q + q) = f (m + p * q) := hf _
        rw [show m + (p + 1) * q = m + p * q + q from by ring, h1, ihp]
    rw [show n * q + m = m + n * q from by omega]; exact this n

private lemma isPrimitiveRoot_pow_gcd (k : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ k)
    (r : ℕ) (hr0 : r ≠ 0) : IsPrimitiveRoot (ζ ^ r) (k / Nat.gcd r k) := by
  have hord : orderOf ζ = k := hζ.eq_orderOf.symm
  exact IsPrimitiveRoot.iff_orderOf.mpr
    (by rw [orderOf_pow' ζ hr0, hord, Nat.gcd_comm])

private lemma sum_range_by_gcd (k : ℕ) (hk : 0 < k) (f : ℕ → ℂ) :
    ∑ r ∈ Finset.range k, f (Nat.gcd k r) =
    ∑ d ∈ k.divisors, ↑(k / d).totient * f d := by
  have hmaps : ∀ r ∈ Finset.range k, Nat.gcd k r ∈ k.divisors :=
    fun r _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left k r, by omega⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro d hd
  have hsimp : ∀ i ∈ (Finset.range k).filter (fun r => Nat.gcd k r = d), f (Nat.gcd k i) = f d :=
    fun i hi => by rw [(Finset.mem_filter.mp hi).2]
  rw [Finset.sum_congr rfl hsimp, Finset.sum_const, nsmul_eq_mul]
  congr 1
  exact_mod_cast (Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)).symm

private lemma char_sum_eq_divisor_sum (k : ℕ) (hk : 0 < k) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ k) :
    ∑ r ∈ Finset.range k, ∏ m ∈ Finset.range k, (1 + ζ ^ (r * (m + 1))) =
    ∑ d ∈ k.divisors.filter Odd, (2 : ℂ) ^ (k / d) * d.totient := by
  -- Step 1: each product depends only on gcd(k,r)
  -- For r=0: product = 2^k. For r≠0: use periodicity + primitive root evaluation
  have h_eval : ∀ r ∈ Finset.range k,
      ∏ m ∈ Finset.range k, (1 + ζ ^ (r * (m + 1))) =
      if (k / Nat.gcd k r) % 2 = 1 then (2 : ℂ) ^ (Nat.gcd k r) else 0 := by
    intro r hr
    by_cases hr0 : r = 0
    · subst hr0; simp [Nat.gcd_zero_right, Nat.div_self hk]; norm_num
    · set d := Nat.gcd k r
      set q := k / d
      have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left r hk
      have hq_pos : 0 < q := Nat.div_pos (Nat.le_of_dvd hk (Nat.gcd_dvd_left k r)) hd_pos
      have hkdq : k = d * q := by
        rw [mul_comm]; exact (Nat.div_mul_cancel (Nat.gcd_dvd_left k r)).symm
      have hprim : IsPrimitiveRoot (ζ ^ r) q := by
        rw [show q = k / Nat.gcd r k from by rw [Nat.gcd_comm]]
        exact isPrimitiveRoot_pow_gcd k ζ hζ r hr0
      have hperiod : ∀ m, (1 : ℂ) + ζ ^ (r * ((m + q) + 1)) = 1 + ζ ^ (r * (m + 1)) := by
        intro m; congr 1
        rw [show r * ((m + q) + 1) = r * (m + 1) + r * q from by ring,
          pow_add, show ζ ^ (r * q) = (ζ ^ r) ^ q from by rw [← pow_mul],
          hprim.pow_eq_one, mul_one]
      rw [hkdq, prod_range_periodic (fun m => 1 + ζ ^ (r * (m + 1))) d q hperiod]
      -- Goal: (∏_{m<q} (1 + ζ^{r*(m+1)}))^d = if q%2=1 then 2^d else 0
      -- The inner product = ∏_{ω ∈ nthRootsFinset q} (1+ω) via the bijection m ↦ ζ^{r*(m+1)}
      have h_inner : ∏ m ∈ Finset.range q, (1 + ζ ^ (r * (m + 1))) =
          ∏ ω ∈ Polynomial.nthRootsFinset q (1 : ℂ), (1 + ω) := by
        have h_inj : Set.InjOn (fun m => (ζ ^ r) ^ (m + 1)) ↑(Finset.range q) := by
          intro a ha b hb hab
          simp only [Finset.coe_range, Set.mem_Iio] at ha hb
          have hab' : (ζ ^ r) ^ (a + 1) = (ζ ^ r) ^ (b + 1) := hab
          have hne : (ζ ^ r) ≠ 0 := by
            intro h; have := hprim.pow_eq_one; rw [h, zero_pow (by omega)] at this
            exact one_ne_zero this.symm
          set η := Units.mk0 (ζ ^ r) hne
          have h_ord : orderOf η = q := by
            rw [show orderOf η = orderOf (ζ ^ r) from orderOf_injective
              (Units.coeHom ℂ) Units.val_injective η ▸ rfl]
            exact hprim.eq_orderOf.symm
          have hab_u : η ^ (a + 1) = η ^ (b + 1) := Units.val_injective (by exact hab')
          have h_mod := (pow_inj_mod (x := η)).mp hab_u
          rw [h_ord] at h_mod
          -- (a+1) % q = (b+1) % q with a,b < q implies a = b
          have h_modeq : a + 1 ≡ b + 1 [MOD q] := h_mod
          exact Nat.ModEq.add_right_cancel' 1 h_modeq |>.eq_of_lt_of_lt ha hb
        have h_image : (Finset.range q).image (fun m => (ζ ^ r) ^ (m + 1)) =
            Polynomial.nthRootsFinset q (1 : ℂ) := by
          apply Finset.eq_of_subset_of_card_le
          · intro ω hω
            obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hω
            rw [Polynomial.mem_nthRootsFinset hq_pos, ← pow_mul,
              show (m + 1) * q = q * (m + 1) from mul_comm _ _, pow_mul,
              hprim.pow_eq_one, one_pow]
          · rw [hprim.card_nthRootsFinset, Finset.card_image_of_injOn h_inj,
              Finset.card_range]
        rw [← h_image, Finset.prod_image (fun a ha b hb hab => h_inj ha hb hab)]
        congr 1; ext m; show 1 + ζ ^ (r * (m + 1)) = 1 + (ζ ^ r) ^ (m + 1)
        congr 1; rw [← pow_mul]
      rw [h_inner, prod_one_add_nthRoots q hq_pos]
      split_ifs <;> simp [show d ≠ 0 from by omega]
  -- Step 2: rewrite using h_eval, then apply sum_range_by_gcd
  rw [Finset.sum_congr rfl h_eval]
  rw [sum_range_by_gcd k hk (fun d => if (k / d) % 2 = 1 then (2 : ℂ) ^ d else 0)]
  -- Step 3: filter out even terms (they contribute 0)
  simp_rw [show ∀ d, ↑(k / d).totient * (if (k / d) % 2 = 1 then (2 : ℂ) ^ d else 0) =
    if (k / d) % 2 = 1 then ↑(k / d).totient * (2 : ℂ) ^ d else 0 from
    fun d => by split_ifs <;> simp]
  rw [← Finset.sum_filter]
  -- Step 4: reindex d ↦ k/d
  have hk_ne : k ≠ 0 := by omega
  apply Finset.sum_nbij (fun d => k / d)
  · intro d hd
    have hd_dvd := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
    have hd_cond := (Finset.mem_filter.mp hd).2
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hd_dvd, hk_ne⟩,
      Nat.odd_iff.mpr hd_cond⟩
  · intro a ha b hb hab
    have ha_dvd := (Nat.mem_divisors.mp (Finset.mem_filter.mp ha).1).1
    have hb_dvd := (Nat.mem_divisors.mp (Finset.mem_filter.mp hb).1).1
    have hab' : k / a = k / b := hab
    rw [← Nat.div_div_self ha_dvd hk_ne, hab', Nat.div_div_self hb_dvd hk_ne]
  · intro d hd
    have hd_dvd := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
    have hd_odd := (Finset.mem_filter.mp hd).2
    refine ⟨k / d, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨Nat.div_dvd_of_dvd hd_dvd, hk_ne⟩, ?_⟩, Nat.div_div_self hd_dvd hk_ne⟩
    rw [Nat.div_div_self hd_dvd hk_ne]; exact Nat.odd_iff.mp hd_odd
  · intro d hd
    have hd_dvd := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
    rw [Nat.div_div_self hd_dvd hk_ne, mul_comm]

theorem b_comb_eq_b (k : ℕ) (hk : 0 < k) :
    (b_comb k : ℝ) = A051293.b k := by
  have hζ := Complex.isPrimitiveRoot_exp k (by omega)
  have h_char := b_comb_as_char_sum k hk _ hζ
  have h_sum := char_sum_eq_divisor_sum k hk _ hζ
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk_ne_c : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- h_char: (b_comb k : ℂ) = (1/k) * ∑_r ∏_m (...)
  -- h_sum: ∑_r ∏_m (...) = ∑_{d|k,odd} 2^{k/d} * φ(d)
  -- So (b_comb k : ℂ) = (1/k) * ∑_{d|k,odd} 2^{k/d} * φ(d)
  -- And b k = (∑_{d|k,odd} 2^{k/d} * φ(d)) / k
  -- These are equal (both real), so cast to ℝ
  simp only [A051293.b]
  rw [eq_div_iff hk_ne]
  have h_eq_c : (b_comb k : ℂ) * k = ∑ d ∈ k.divisors.filter Odd, (2 : ℂ) ^ (k / d) * d.totient := by
    have : (b_comb k : ℂ) * k = ∑ r ∈ Finset.range k,
        ∏ m ∈ Finset.range k, (1 + Complex.exp (2 * ↑Real.pi * Complex.I / ↑k) ^ (r * (m + 1))) := by
      rw [h_char]; field_simp
    rw [this, h_sum]
  exact_mod_cast h_eq_c

end StepB

section Summation

/-! ### Step (summation): partitioning by maximum element

Every nonempty subset S ⊆ {1,…,n} with integer mean has a unique
maximum element k = max(S). Since S ⊆ {1,…,k} and k ∈ S, the subset
is counted by `maxKIntMeanSubsets k`. Summing over k gives the total. -/

private lemma maxK_subset_intMean {n k : ℕ} (hk : k ∈ Finset.range n)
    {S : Finset ℕ} (hS : S ∈ maxKIntMeanSubsets (k + 1)) :
    S ∈ intMeanSubsets n := by
  simp only [maxKIntMeanSubsets, Finset.mem_filter, Finset.mem_powerset] at hS
  simp only [intMeanSubsets, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨fun x hx => Finset.mem_range.mpr (Nat.lt_of_lt_of_le
    (Finset.mem_range.mp (hS.1 hx)) (Finset.mem_range.mp hk)), ⟨k, hS.2.1⟩, hS.2.2⟩

private lemma intMean_mem_maxK {n : ℕ} {S : Finset ℕ} (hS : S ∈ intMeanSubsets n) :
    ∃ k ∈ Finset.range n, S ∈ maxKIntMeanSubsets (k + 1) := by
  simp only [intMeanSubsets, Finset.mem_filter, Finset.mem_powerset] at hS
  obtain ⟨hS_sub, hS_ne, hS_div⟩ := hS
  refine ⟨S.max' hS_ne, Finset.mem_range.mpr (Finset.mem_range.mp (hS_sub (Finset.max'_mem S hS_ne))),
    ?_⟩
  simp only [maxKIntMeanSubsets, Finset.mem_filter, Finset.mem_powerset, Nat.add_sub_cancel]
  refine ⟨fun x hx => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' S x hx)),
    Finset.max'_mem S hS_ne, hS_div⟩

private lemma maxK_pairwise_disjoint :
    Set.PairwiseDisjoint (↑(Finset.range n) : Set ℕ) (fun k => maxKIntMeanSubsets (k + 1)) := by
  intro i _ j _ hij
  rw [Function.onFun, Finset.disjoint_left]
  intro S hSi hSj
  simp only [maxKIntMeanSubsets, Finset.mem_filter, Finset.mem_powerset, Nat.add_sub_cancel] at hSi hSj
  have := Finset.mem_range.mp (hSi.1 hSj.2.1)
  have := Finset.mem_range.mp (hSj.1 hSi.2.1)
  omega

theorem a_comb_eq_sum (n : ℕ) :
    a_comb n = ∑ k ∈ Finset.range n, (b_comb (k + 1) - 1) := by
  have h_eq : intMeanSubsets n = (Finset.range n).biUnion (fun k => maxKIntMeanSubsets (k + 1)) := by
    ext S
    simp only [Finset.mem_biUnion]
    exact ⟨intMean_mem_maxK, fun ⟨k, hk, hS⟩ => maxK_subset_intMean hk hS⟩
  simp only [a_comb, h_eq, Finset.card_biUnion maxK_pairwise_disjoint]
  congr 1; ext k
  by_cases hk : 0 < k + 1
  · exact (zumkeller_identity (k + 1) hk).symm
  · omega

end Summation

section Bridge

/-! ### Bridge: connecting combinatorial and analytic definitions -/

private lemma one_le_b_comb (k : ℕ) : 1 ≤ b_comb k := by
  have h : ∅ ∈ modSubsets k :=
    Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, dvd_zero k⟩
  exact Finset.one_le_card.mpr ⟨∅, h⟩

/-- The combinatorial count equals the analytic formula. -/
theorem a_comb_eq_a (n : ℕ) (_hn : 0 < n) :
    (a_comb n : ℝ) = A051293.a n := by
  simp only [a_comb_eq_sum, a]
  rw [Nat.cast_sum]
  congr 1; ext k
  have hk : 0 < k + 1 := Nat.succ_pos k
  rw [Nat.cast_sub (one_le_b_comb (k + 1)), b_comb_eq_b (k + 1) hk, Nat.cast_one]

/-- **Cloitre's conjecture (2002)**, as originally stated. -/
theorem cloitre_conjecture (M : ℕ) :
    (fun n : ℕ => (a_comb n : ℝ) -
      (2 : ℝ) ^ (n + 1) / ↑n *
        ∑ i ∈ Finset.range (M + 1), ↑(fubini i) / (↑n : ℝ) ^ i)
    =o[Filter.atTop] (fun n : ℕ => (2 : ℝ) ^ n / (↑n : ℝ) ^ (M + 1)) := by
  have h := asymptotic_expansion M
  suffices heq : ∀ᶠ n : ℕ in Filter.atTop,
      (a_comb n : ℝ) = A051293.a n by
    exact h.congr' (heq.mono fun n hn => by simp only [hn]) (Filter.EventuallyEq.refl _ _)
  rw [Filter.eventually_atTop]
  exact ⟨1, fun n hn => a_comb_eq_a n (by omega)⟩

end Bridge

end A051293
