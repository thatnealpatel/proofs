/-
  Scratch.GlobalRankSearch.ResidualRankPruning — exact residual-rank pruning
  for partial list decompositions.

  A completed list decomposition splits at any prefix: the unpeeled suffix
  decomposes the residual exactly.  Passing that residual through a linear
  matrix-valued flattening therefore bounds its matrix rank by the number of
  remaining terms times the uniform simple-image rank bound.  Violating this
  bound rules out the branch.
-/
import BilinearComplexity.PeelingMoves
import BilinearComplexity.LinearFlattening

set_option autoImplicit false

namespace BilinearComplexity

section ListDecomposition

variable {k : Type*} [CommSemiring k] {a b c : ℕ}

/-- A list decomposition of length `L.length` witnesses the corresponding
`RankLE` bound with exactly that many indexed triads. -/
theorem rankLE_length_of_isDecomp
    {T : Tensor k a b c} {L : Decomp k a b c} (hdecomp : IsDecomp T L) :
    RankLE T L.length := by
  induction L generalizing T with
  | nil =>
      exact rankLE_zero_iff.mpr hdecomp.symm
  | cons t ts ih =>
      change RankLE T (Nat.succ ts.length)
      obtain ⟨u, v, w, htail⟩ := ih (T := decompSum ts) rfl
      refine ⟨Fin.cases t.1 u, Fin.cases t.2.1 v, Fin.cases t.2.2 w, ?_⟩
      rw [← hdecomp]
      funext i j l
      simp only [decompSum]
      rw [Fin.sum_univ_succ]
      simp only [Fin.cases_zero, Fin.cases_succ]
      rw [congr_fun (congr_fun (congr_fun htail i) j) l]

#check @rankLE_length_of_isDecomp

end ListDecomposition

section ResidualDecomposition

variable {k : Type*} [CommRing k] {a b c : ℕ}

/-- If `pre ++ suffix` decomposes `T`, then `suffix` decomposes the tensor
left after peeling `pre` from `T`. -/
theorem isDecomp_residual_of_isDecomp_append
    {T : Tensor k a b c} {pre suffix : Decomp k a b c}
    (hdecomp : IsDecomp T (pre ++ suffix)) :
    IsDecomp (residual T pre) suffix := by
  simp only [IsDecomp] at hdecomp ⊢
  rw [residual_eq_sub]
  rw [decompSum_append] at hdecomp
  funext i j l
  have hentry := congr_fun (congr_fun (congr_fun hdecomp i) j) l
  rw [← hentry]
  abel

/-- A completed branch supplies an exact `suffix.length`-term rank witness for
its prefix residual. -/
theorem rankLE_residual_of_isDecomp_append
    {T : Tensor k a b c} {pre suffix : Decomp k a b c}
    (hdecomp : IsDecomp T (pre ++ suffix)) :
    RankLE (residual T pre) suffix.length :=
  rankLE_length_of_isDecomp (isDecomp_residual_of_isDecomp_append hdecomp)

#check @isDecomp_residual_of_isDecomp_append
#check @rankLE_residual_of_isDecomp_append

end ResidualDecomposition

section ResidualFlattening

variable {k : Type*} [Field k] {a b c q remaining : ℕ}
variable {rows cols : Type*} [Fintype rows] [Fintype cols]

/-- Positive residual-rank bound: if a suffix completes a prefix to a list
decomposition, every linear flattening with simple-image rank at most `q`
sends the prefix residual to a matrix of rank at most `suffix.length * q`. -/
theorem rank_linearMap_residual_le_of_isDecomp_append
    (F : Tensor k a b c →ₗ[k] Matrix rows cols k)
    (hsimple : ∀ (u : Fin a → k) (v : Fin b → k) (w : Fin c → k),
      (F (fun i j l => u i * v j * w l)).rank ≤ q)
    {T : Tensor k a b c} {pre suffix : Decomp k a b c}
    (hdecomp : IsDecomp T (pre ++ suffix)) :
    (F (residual T pre)).rank ≤ suffix.length * q :=
  rank_linearMap_le_mul_of_rankLE F hsimple
    (rankLE_residual_of_isDecomp_append hdecomp)

/-- Contrapositive residual-rank certificate for a fixed suffix: if the
flattened residual rank is strictly larger than `suffix.length * q`, that
suffix cannot complete the prefix to a decomposition of `T`. -/
theorem not_isDecomp_append_of_mul_lt_rank_linearMap_residual
    (F : Tensor k a b c →ₗ[k] Matrix rows cols k)
    (hsimple : ∀ (u : Fin a → k) (v : Fin b → k) (w : Fin c → k),
      (F (fun i j l => u i * v j * w l)).rank ≤ q)
    {T : Tensor k a b c} {pre suffix : Decomp k a b c}
    (hviolation : suffix.length * q < (F (residual T pre)).rank) :
    ¬ IsDecomp T (pre ++ suffix) := by
  intro hdecomp
  exact Nat.not_le_of_lt hviolation
    (rank_linearMap_residual_le_of_isDecomp_append F hsimple hdecomp)

/-- Branch-pruning form: if `remaining * q` is strictly below the flattened
residual rank, then no suffix of at most `remaining` triads can complete the
current prefix. -/
theorem no_isDecomp_completion_of_mul_lt_rank_linearMap_residual
    (F : Tensor k a b c →ₗ[k] Matrix rows cols k)
    (hsimple : ∀ (u : Fin a → k) (v : Fin b → k) (w : Fin c → k),
      (F (fun i j l => u i * v j * w l)).rank ≤ q)
    {T : Tensor k a b c} {pre : Decomp k a b c}
    (hviolation : remaining * q < (F (residual T pre)).rank) :
    ¬ ∃ suffix : Decomp k a b c,
      suffix.length ≤ remaining ∧ IsDecomp T (pre ++ suffix) := by
  rintro ⟨suffix, hlength, hdecomp⟩
  have hrank : (F (residual T pre)).rank ≤ suffix.length * q :=
    rank_linearMap_residual_le_of_isDecomp_append F hsimple hdecomp
  have hproduct : suffix.length * q ≤ remaining * q :=
    Nat.mul_le_mul_right q hlength
  exact Nat.not_le_of_lt hviolation (hrank.trans hproduct)

#check @rank_linearMap_residual_le_of_isDecomp_append
#check @not_isDecomp_append_of_mul_lt_rank_linearMap_residual
#check @no_isDecomp_completion_of_mul_lt_rank_linearMap_residual

end ResidualFlattening

section JointSatisfiability

/-- The positive hypotheses are jointly inhabited, including the zero-term
edge case: the empty list decomposes the zero tensor and the zero flattening
has rank zero. -/
example :
    let F : Tensor ℚ 1 1 1 →ₗ[ℚ] Matrix (Fin 1) (Fin 1) ℚ := 0
    let T : Tensor ℚ 1 1 1 := 0
    let pre : Decomp ℚ 1 1 1 := []
    let suffix : Decomp ℚ 1 1 1 := []
    (∀ (u v w : Fin 1 → ℚ),
      (F (fun i j l => u i * v j * w l)).rank ≤ 0) ∧
    IsDecomp T (pre ++ suffix) ∧
    (F (residual T pre)).rank ≤ suffix.length * 0 := by
  simp

/-- The strict-violation hypotheses are also jointly inhabited: evaluation
of the unique entry maps a nonzero `1 × 1 × 1` tensor to a nonzero `1 × 1`
matrix, so no zero-term suffix can complete the empty prefix. -/
example :
    let F : Tensor ℚ 1 1 1 →ₗ[ℚ] Matrix (Fin 1) (Fin 1) ℚ :=
      { toFun := fun T _ _ => T 0 0 0
        map_add' := by
          intro T U
          rfl
        map_smul' := by
          intro m T
          rfl }
    let T : Tensor ℚ 1 1 1 := fun _ _ _ => 1
    (∀ (u v w : Fin 1 → ℚ),
      (F (fun i j l => u i * v j * w l)).rank ≤ 1) ∧
    0 * 1 < (F (residual T [])).rank ∧
    ¬ ∃ suffix : Decomp ℚ 1 1 1,
      suffix.length ≤ 0 ∧ IsDecomp T ([] ++ suffix) := by
  dsimp only
  let F : Tensor ℚ 1 1 1 →ₗ[ℚ] Matrix (Fin 1) (Fin 1) ℚ :=
    { toFun := fun T _ _ => T 0 0 0
      map_add' := by
        intro T U
        rfl
      map_smul' := by
        intro m T
        rfl }
  let T : Tensor ℚ 1 1 1 := fun _ _ _ => 1
  have hsimple : ∀ (u v w : Fin 1 → ℚ),
      (F (fun i j l => u i * v j * w l)).rank ≤ 1 := by
    intro u v w
    exact (Matrix.rank_le_card_height _).trans_eq (Fintype.card_fin 1)
  have hdet :
      ((F T).submatrix (fun i : Fin 1 => i) (fun i : Fin 1 => i)).det ≠ 0 := by
    rw [Matrix.det_fin_one]
    change (1 : ℚ) ≠ 0
    norm_num
  have hrank : 1 ≤ (F T).rank :=
    le_rank_of_submatrix_det_ne_zero (F T) (fun i => i) (fun i => i) hdet
  have hviolation : 0 * 1 < (F (residual T [])).rank := by
    simpa only [residual, zero_mul] using
      (Nat.lt_of_lt_of_le Nat.zero_lt_one hrank)
  refine ⟨hsimple, hviolation, ?_⟩
  exact no_isDecomp_completion_of_mul_lt_rank_linearMap_residual
    (remaining := 0) F hsimple hviolation

end JointSatisfiability

#print axioms isDecomp_residual_of_isDecomp_append
#print axioms rankLE_length_of_isDecomp
#print axioms rankLE_residual_of_isDecomp_append
#print axioms rank_linearMap_residual_le_of_isDecomp_append
#print axioms not_isDecomp_append_of_mul_lt_rank_linearMap_residual
#print axioms no_isDecomp_completion_of_mul_lt_rank_linearMap_residual

end BilinearComplexity
