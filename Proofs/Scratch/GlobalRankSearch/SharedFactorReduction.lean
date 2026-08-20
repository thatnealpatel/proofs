/-
  Scratch/GlobalRankSearch/SharedFactorReduction — exact shared-factor
  reduction certificates for finite triad families.
-/
import BilinearComplexity.RankCalculus
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

set_option autoImplicit false

namespace BilinearComplexity

/-- A dependent family of second factors sharing the same first factor
admits an explicit pivot elimination.  The dependence certificate has a
nonzero coefficient at `p`, and each surviving third factor is adjusted by
`w_s - (g_s / g_p) w_p`. -/
theorem exists_shared_first_factor_reduction_certificate
    {k : Type*} [Field k] {a b c n : ℕ}
    (u : Fin a → k) (v : Fin (n + 1) → Fin b → k)
    (w : Fin (n + 1) → Fin c → k)
    (hdep : ¬ LinearIndependent k v) :
    ∃ (p : Fin (n + 1)) (g : Fin (n + 1) → k),
      g p ≠ 0 ∧ (∑ s, g s • v s) = 0 ∧
        ∀ i j l,
          (∑ s, u i * v s j * w s l) =
            ∑ t : Fin n, u i * v (p.succAbove t) j *
              (w (p.succAbove t) l -
                (g (p.succAbove t) / g p) * w p l) := by
  rw [Fintype.linearIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨g, hg, p, hgp⟩ := hdep
  refine ⟨p, g, hgp, hg, ?_⟩
  intro i j l
  have hrel : (∑ s, g s * v s j) = 0 := by
    have hrel_fun := congrFun hg j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] using hrel_fun
  rw [Fin.sum_univ_succAbove (fun s => g s * v s j) p] at hrel
  have hpterm : g p * v p j = -(∑ t, g (p.succAbove t) * v (p.succAbove t) j) :=
    eq_neg_of_add_eq_zero_left hrel
  have hvp : v p j =
      ∑ t, -(g (p.succAbove t) / g p) * v (p.succAbove t) j := by
    calc
      v p j = (g p)⁻¹ * (g p * v p j) := by
        rw [← mul_assoc, inv_mul_cancel₀ hgp, one_mul]
      _ = (g p)⁻¹ * (-(∑ t, g (p.succAbove t) *
          v (p.succAbove t) j)) := by rw [hpterm]
      _ = ∑ t, -(g (p.succAbove t) / g p) *
          v (p.succAbove t) j := by
        rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro t _
        simp only [div_eq_mul_inv]
        ring
  rw [Fin.sum_univ_succAbove (fun s => u i * v s j * w s l) p]
  rw [hvp, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- A nonempty `Fin r` family with a common first factor and dependent
second factors has tensor rank at most `r - 1`.  The positive-size hypothesis
guards the natural-number subtraction. -/
theorem rankLE_sum_shared_first_factor_of_not_linearIndependent
    {k : Type*} [Field k] {a b c r : ℕ} (hr : 0 < r)
    (u : Fin a → k) (v : Fin r → Fin b → k)
    (w : Fin r → Fin c → k)
    (hdep : ¬ LinearIndependent k v) :
    RankLE (fun i j l => ∑ s, u i * v s j * w s l) (r - 1) := by
  cases r with
  | zero => simp at hr
  | succ n =>
      obtain ⟨p, g, _hgp, _hrel, hrewrite⟩ :=
        exists_shared_first_factor_reduction_certificate u v w hdep
      let w' : Fin n → Fin c → k := fun t l =>
        w (p.succAbove t) l - (g (p.succAbove t) / g p) * w p l
      have hrank : RankLE
          (fun i j l => ∑ s, u i * v s j * w s l) n := by
        refine ⟨fun _ => u, fun t => v (p.succAbove t), w', ?_⟩
        funext i j l
        exact hrewrite i j l
      simpa only [Nat.succ_sub_one] using hrank

/-- If every first factor is a scalar multiple of one vector, dependence
of the second factors still removes one triad: the scalars, including any zero
scalars, are absorbed into the adjusted third factors. -/
theorem rankLE_sum_scalar_shared_first_factor_of_not_linearIndependent
    {k : Type*} [Field k] {a b c r : ℕ} (hr : 0 < r)
    (u : Fin a → k) (q : Fin r → k)
    (v : Fin r → Fin b → k) (w : Fin r → Fin c → k)
    (hdep : ¬ LinearIndependent k v) :
    RankLE (fun i j l => ∑ s, (q s • u) i * v s j * w s l) (r - 1) := by
  let wscaled : Fin r → Fin c → k := fun s l => q s * w s l
  obtain ⟨u', v', w', hdecomp⟩ :=
    rankLE_sum_shared_first_factor_of_not_linearIndependent
      hr u v wscaled hdep
  refine ⟨u', v', w', ?_⟩
  calc
    (fun i j l => ∑ s, (q s • u) i * v s j * w s l) =
        (fun i j l => ∑ s, u i * v s j * wscaled s l) := by
          funext i j l
          apply Finset.sum_congr rfl
          intro s _
          simp only [Pi.smul_apply, smul_eq_mul, wscaled]
          ring
    _ = fun i j l => ∑ s, u' s i * v' s j * w' s l := hdecomp

/-- Symmetric shared-factor form: a common second factor and dependent first
factors also give rank at most `r - 1`, by swapping the first two tensor modes
and then swapping the resulting decomposition factors back. -/
theorem rankLE_sum_shared_second_factor_of_not_linearIndependent
    {k : Type*} [Field k] {a b c r : ℕ} (hr : 0 < r)
    (u : Fin r → Fin a → k) (v : Fin b → k)
    (w : Fin r → Fin c → k)
    (hdep : ¬ LinearIndependent k u) :
    RankLE (fun i j l => ∑ s, u s i * v j * w s l) (r - 1) := by
  obtain ⟨v', u', w', hdecomp⟩ :=
    rankLE_sum_shared_first_factor_of_not_linearIndependent
      hr v u w hdep
  refine ⟨u', v', w', ?_⟩
  funext i j l
  have hentry := congrFun (congrFun (congrFun hdecomp j) i) l
  calc
    (∑ s, u s i * v j * w s l) =
        ∑ s, v j * u s i * w s l := by
          apply Finset.sum_congr rfl
          intro s _
          ring
    _ = ∑ s, v' s j * u' s i * w' s l := hentry
    _ = ∑ s, u' s i * v' s j * w' s l := by
          apply Finset.sum_congr rfl
          intro s _
          ring

/-- Two nonzero scalar multiples of a shared nonzero first factor, with
nonzero duplicate second factors, jointly exercise dependence-driven elimination
from two nonzero triads to one. -/
example :
    let u : Fin 1 → ℚ := fun _ => 1
    let q : Fin 2 → ℚ := fun _ => 1
    let v : Fin 2 → Fin 1 → ℚ := fun _ _ => 1
    let w : Fin 2 → Fin 1 → ℚ := fun _ _ => 1
    (∀ s, (q s • u) 0 * v s 0 * w s 0 ≠ 0) ∧
      ¬ LinearIndependent ℚ v ∧
        RankLE (fun i j l => ∑ s, (q s • u) i * v s j * w s l) (2 - 1) := by
  dsimp only
  have hdep : ¬ LinearIndependent ℚ
      (fun _ : Fin 2 => fun _ : Fin 1 => (1 : ℚ)) := by
    intro hli
    rw [linearIndependent_fin2] at hli
    exact (hli.2 1) (by simp)
  refine ⟨?_, hdep, ?_⟩
  · intro s
    norm_num [Pi.smul_apply]
  · exact rankLE_sum_scalar_shared_first_factor_of_not_linearIndependent
      (by omega) (fun _ : Fin 1 => (1 : ℚ))
      (fun _ : Fin 2 => (1 : ℚ))
      (fun _ : Fin 2 => fun _ : Fin 1 => (1 : ℚ))
      (fun _ : Fin 2 => fun _ : Fin 1 => (1 : ℚ)) hdep

/-- Boundary check: the scalar-shared theorem permits a zero scalar multiple;
the other displayed triad remains nonzero. -/
example :
    let u : Fin 1 → ℚ := fun _ => 1
    let q : Fin 2 → ℚ := fun s => if s = 0 then 0 else 3
    let v : Fin 2 → Fin 1 → ℚ := fun _ _ => 1
    let w : Fin 2 → Fin 1 → ℚ := fun s _ => if s = 0 then 5 else 7
    ¬ LinearIndependent ℚ v ∧
      RankLE (fun i j l => ∑ s, (q s • u) i * v s j * w s l) (2 - 1) := by
  dsimp only
  have hdep : ¬ LinearIndependent ℚ
      (fun _ : Fin 2 => fun _ : Fin 1 => (1 : ℚ)) := by
    intro hli
    rw [linearIndependent_fin2] at hli
    exact (hli.2 1) (by simp)
  refine ⟨hdep, ?_⟩
  exact rankLE_sum_scalar_shared_first_factor_of_not_linearIndependent
    (by omega) (fun _ : Fin 1 => (1 : ℚ))
    (fun s : Fin 2 => if s = 0 then 0 else 3)
    (fun _ : Fin 2 => fun _ : Fin 1 => (1 : ℚ))
    (fun s : Fin 2 => fun _ : Fin 1 => if s = 0 then 5 else 7) hdep

#check @exists_shared_first_factor_reduction_certificate
#check @rankLE_sum_shared_first_factor_of_not_linearIndependent
#check @rankLE_sum_scalar_shared_first_factor_of_not_linearIndependent
#check @rankLE_sum_shared_second_factor_of_not_linearIndependent

#print axioms exists_shared_first_factor_reduction_certificate
#print axioms rankLE_sum_shared_first_factor_of_not_linearIndependent
#print axioms rankLE_sum_scalar_shared_first_factor_of_not_linearIndependent
#print axioms rankLE_sum_shared_second_factor_of_not_linearIndependent

end BilinearComplexity
