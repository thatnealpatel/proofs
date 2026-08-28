/-
  Scratch/GlobalRankSearch/SharedFactorReduction — compatibility checks for the
  public shared-factor reduction API.
-/
import BilinearComplexity.SharedFactorReduction

set_option autoImplicit false

namespace BilinearComplexity

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
