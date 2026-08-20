/-
  Scratch/GlobalRankSearch/M3ContractionProfiles — explicit contraction-incidence
  profiles for short exact decompositions of three-by-three matrix multiplication.

  Each profile records active-support lower bounds and subtraction-free inactive
  budgets for rank-one, rank-two, and rank-three matrix functionals in all three
  tensor modes.
-/
import Scratch.GlobalRankSearch.ContractionSupport

set_option autoImplicit false

namespace BilinearComplexity

open scoped Matrix

/-- The complete contraction-incidence profile of three fixed `3 × 3`
functionals of respective matrix ranks one, two, and three against all three
factor families of a length-`r` decomposition.  The fields are deliberately
numerical so a finite SAT or ILP encoding can use them without normalizing
matrix-rank products or natural-number subtraction. -/
structure M3ContractionProfile {k : Type*} [CommSemiring k] (r : ℕ)
    (u v w : Fin r → Fin 9 → k)
    (F₁ F₂ F₃ : Matrix (Fin 3) (Fin 3) k) : Prop where
  /-- The first functional has matrix rank one. -/
  rank_F₁ : F₁.rank = 1
  /-- The second functional has matrix rank two. -/
  rank_F₂ : F₂.rank = 2
  /-- The third functional has matrix rank three. -/
  rank_F₃ : F₃.rank = 3
  /-- A rank-one mode-one functional is active on at least three terms. -/
  modeOne_rankOne_active : 3 ≤ (functionalSupport F₁ u).card
  /-- The rank-one mode-one inactive budget is subtraction-free. -/
  modeOne_rankOne_budget : 3 + (functionalInactive F₁ u).card ≤ r
  /-- A rank-two mode-one functional is active on at least six terms. -/
  modeOne_rankTwo_active : 6 ≤ (functionalSupport F₂ u).card
  /-- The rank-two mode-one inactive budget is subtraction-free. -/
  modeOne_rankTwo_budget : 6 + (functionalInactive F₂ u).card ≤ r
  /-- A rank-three mode-one functional is active on at least nine terms. -/
  modeOne_rankThree_active : 9 ≤ (functionalSupport F₃ u).card
  /-- The rank-three mode-one inactive budget is subtraction-free. -/
  modeOne_rankThree_budget : 9 + (functionalInactive F₃ u).card ≤ r
  /-- A rank-one mode-two functional is active on at least three terms. -/
  modeTwo_rankOne_active : 3 ≤ (functionalSupport F₁ v).card
  /-- The rank-one mode-two inactive budget is subtraction-free. -/
  modeTwo_rankOne_budget : 3 + (functionalInactive F₁ v).card ≤ r
  /-- A rank-two mode-two functional is active on at least six terms. -/
  modeTwo_rankTwo_active : 6 ≤ (functionalSupport F₂ v).card
  /-- The rank-two mode-two inactive budget is subtraction-free. -/
  modeTwo_rankTwo_budget : 6 + (functionalInactive F₂ v).card ≤ r
  /-- A rank-three mode-two functional is active on at least nine terms. -/
  modeTwo_rankThree_active : 9 ≤ (functionalSupport F₃ v).card
  /-- The rank-three mode-two inactive budget is subtraction-free. -/
  modeTwo_rankThree_budget : 9 + (functionalInactive F₃ v).card ≤ r
  /-- A rank-one mode-three functional is active on at least three terms. -/
  modeThree_rankOne_active : 3 ≤ (functionalSupport F₁ w).card
  /-- The rank-one mode-three inactive budget is subtraction-free. -/
  modeThree_rankOne_budget : 3 + (functionalInactive F₁ w).card ≤ r
  /-- A rank-two mode-three functional is active on at least six terms. -/
  modeThree_rankTwo_active : 6 ≤ (functionalSupport F₂ w).card
  /-- The rank-two mode-three inactive budget is subtraction-free. -/
  modeThree_rankTwo_budget : 6 + (functionalInactive F₂ w).card ≤ r
  /-- A rank-three mode-three functional is active on at least nine terms. -/
  modeThree_rankThree_active : 9 ≤ (functionalSupport F₃ w).card
  /-- The rank-three mode-three inactive budget is subtraction-free. -/
  modeThree_rankThree_budget : 9 + (functionalInactive F₃ w).card ≤ r

/-- Every exact length-`r` decomposition of `3 × 3` matrix multiplication has
the full numerical contraction profile for arbitrary matrix functionals of
ranks one, two, and three. -/
theorem m3_contractionProfile_of_exact {k : Type*} [Field k] {r : ℕ}
    (u v w : Fin r → Fin 9 → k)
    (hdecomp : matMulTensor k 3 3 3 =
      fun x y z => ∑ t, u t x * v t y * w t z)
    (F₁ F₂ F₃ : Matrix (Fin 3) (Fin 3) k)
    (hF₁ : F₁.rank = 1) (hF₂ : F₂.rank = 2) (hF₃ : F₃.rank = 3) :
    M3ContractionProfile r u v w F₁ F₂ F₃ where
  rank_F₁ := hF₁
  rank_F₂ := hF₂
  rank_F₃ := hF₃
  modeOne_rankOne_active := by
    simpa [hF₁] using
      modeOne_mul_rank_le_card_functionalSupport u v w hdecomp F₁
  modeOne_rankOne_budget := by
    simpa [hF₁] using modeOne_heavy_hyperplane u v w hdecomp F₁
  modeOne_rankTwo_active := by
    simpa [hF₂] using
      modeOne_mul_rank_le_card_functionalSupport u v w hdecomp F₂
  modeOne_rankTwo_budget := by
    simpa [hF₂] using modeOne_heavy_hyperplane u v w hdecomp F₂
  modeOne_rankThree_active := by
    simpa [hF₃] using
      modeOne_mul_rank_le_card_functionalSupport u v w hdecomp F₃
  modeOne_rankThree_budget := by
    simpa [hF₃] using modeOne_heavy_hyperplane u v w hdecomp F₃
  modeTwo_rankOne_active := by
    simpa [hF₁] using
      modeTwo_mul_rank_le_card_functionalSupport u v w hdecomp F₁
  modeTwo_rankOne_budget := by
    simpa [hF₁] using modeTwo_heavy_hyperplane u v w hdecomp F₁
  modeTwo_rankTwo_active := by
    simpa [hF₂] using
      modeTwo_mul_rank_le_card_functionalSupport u v w hdecomp F₂
  modeTwo_rankTwo_budget := by
    simpa [hF₂] using modeTwo_heavy_hyperplane u v w hdecomp F₂
  modeTwo_rankThree_active := by
    simpa [hF₃] using
      modeTwo_mul_rank_le_card_functionalSupport u v w hdecomp F₃
  modeTwo_rankThree_budget := by
    simpa [hF₃] using modeTwo_heavy_hyperplane u v w hdecomp F₃
  modeThree_rankOne_active := by
    simpa [hF₁] using
      modeThree_mul_rank_le_card_functionalSupport u v w hdecomp F₁
  modeThree_rankOne_budget := by
    simpa [hF₁] using modeThree_heavy_hyperplane u v w hdecomp F₁
  modeThree_rankTwo_active := by
    simpa [hF₂] using
      modeThree_mul_rank_le_card_functionalSupport u v w hdecomp F₂
  modeThree_rankTwo_budget := by
    simpa [hF₂] using modeThree_heavy_hyperplane u v w hdecomp F₂
  modeThree_rankThree_active := by
    simpa [hF₃] using
      modeThree_mul_rank_le_card_functionalSupport u v w hdecomp F₃
  modeThree_rankThree_budget := by
    simpa [hF₃] using modeThree_heavy_hyperplane u v w hdecomp F₃

/-- The twenty-seven-term schoolbook decomposition over `ℚ`, together with
explicit diagonal matrices of ranks one, two, and three, jointly satisfies the
generic profile theorem's hypotheses and conclusion. -/
example :
    let F₁ : Matrix (Fin 3) (Fin 3) ℚ := Matrix.diagonal ![1, 0, 0]
    let F₂ : Matrix (Fin 3) (Fin 3) ℚ := Matrix.diagonal ![1, 1, 0]
    let F₃ : Matrix (Fin 3) (Fin 3) ℚ := Matrix.diagonal ![1, 1, 1]
    ∃ u v w : Fin 27 → Fin 9 → ℚ,
      matMulTensor ℚ 3 3 3 =
          (fun x y z => ∑ t, u t x * v t y * w t z) ∧
        F₁.rank = 1 ∧ F₂.rank = 2 ∧ F₃.rank = 3 ∧
        M3ContractionProfile 27 u v w F₁ F₂ F₃ := by
  dsimp only
  let F₁ : Matrix (Fin 3) (Fin 3) ℚ := Matrix.diagonal ![1, 0, 0]
  let F₂ : Matrix (Fin 3) (Fin 3) ℚ := Matrix.diagonal ![1, 1, 0]
  let F₃ : Matrix (Fin 3) (Fin 3) ℚ := Matrix.diagonal ![1, 1, 1]
  have hF₁ : F₁.rank = 1 := by
    rw [show F₁ = Matrix.diagonal ![(1 : ℚ), 0, 0] from rfl,
      Matrix.rank_diagonal]
    decide
  have hF₂ : F₂.rank = 2 := by
    rw [show F₂ = Matrix.diagonal ![(1 : ℚ), 1, 0] from rfl,
      Matrix.rank_diagonal]
    decide
  have hF₃ : F₃.rank = 3 := by
    rw [show F₃ = Matrix.diagonal ![(1 : ℚ), 1, 1] from rfl,
      Matrix.rank_diagonal]
    decide
  obtain ⟨u, v, w, hdecomp⟩ := rankLE_matMulTensor ℚ 3 3 3
  have hprofile :=
    m3_contractionProfile_of_exact u v w hdecomp F₁ F₂ F₃ hF₁ hF₂ hF₃
  exact ⟨u, v, w, hdecomp, hF₁, hF₂, hF₃, hprofile⟩

#check @M3ContractionProfile
#check @M3ContractionProfile.rank_F₁
#check @M3ContractionProfile.rank_F₂
#check @M3ContractionProfile.rank_F₃
#check @M3ContractionProfile.modeOne_rankOne_active
#check @M3ContractionProfile.modeTwo_rankTwo_budget
#check @M3ContractionProfile.modeThree_rankThree_active
#check @m3_contractionProfile_of_exact

#print axioms m3_contractionProfile_of_exact

end BilinearComplexity
