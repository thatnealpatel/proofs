import BilinearComplexity.NormalizedBinaryCarrier
import BilinearComplexity.Winograd

set_option autoImplicit false

/-!
# Binary `2 × 2` matrix-multiplication rank certificate

This module realizes Strassen's seven binary products as a normalized
finite-set state of profile `(4,4,4)`. It checks that the state evaluates to
`matMulTensor F2 2 2 2`, constructs both state-indexed and directly indexed
`RankLE` certificates, and combines the explicit upper bound with the existing
independent Winograd lower bound over `ZMod 2`.

This is an instance-level certificate for the known exact rank of binary
`2 × 2` matrix multiplication. It is not a search-discovery result.

AI disclosure: produced with AI assistance (see `Proofs/README`).
-/

namespace BilinearComplexity.BinaryMatMulRankCertificate

open BilinearComplexity
open NormalizedBinaryCarrier

/-- The normalized factor profile for the three four-coordinate modes of
`2 × 2` matrix multiplication. -/
def profile444 : Profile := ⟨4, 4, 4⟩

example : profile444 = ⟨4, 4, 4⟩ := rfl

private theorem strassenU_ne_zero (s : Fin 7) : strassenU F2 s ≠ 0 := by
  fin_cases s
  · intro h
    exact (one_ne_zero : (1 : F2) ≠ 0)
      (by simpa [strassenU] using congrFun h (0 : Fin 4))
  · intro h
    exact (one_ne_zero : (1 : F2) ≠ 0)
      (by simpa [strassenU] using congrFun h (2 : Fin 4))
  · intro h
    exact (one_ne_zero : (1 : F2) ≠ 0)
      (by simpa [strassenU] using congrFun h (0 : Fin 4))
  · intro h
    exact (one_ne_zero : (1 : F2) ≠ 0)
      (by simpa [strassenU] using congrFun h (3 : Fin 4))
  · intro h
    exact (one_ne_zero : (1 : F2) ≠ 0)
      (by simpa [strassenU] using congrFun h (0 : Fin 4))
  · intro h
    exact (one_ne_zero : (1 : F2) ≠ 0)
      (by simpa [strassenU] using congrFun h (0 : Fin 4))
  · intro h
    exact (one_ne_zero : (1 : F2) ≠ 0)
      (by simpa [strassenU] using congrFun h (1 : Fin 4))

private theorem strassenV_ne_zero (s : Fin 7) : strassenV F2 s ≠ 0 := by
  fin_cases s
  · intro h
    exact (one_ne_zero : (1 : F2) ≠ 0)
      (by simpa [strassenV] using congrFun h (0 : Fin 4))
  · intro h
    exact (one_ne_zero : (1 : F2) ≠ 0)
      (by simpa [strassenV] using congrFun h (0 : Fin 4))
  · intro h
    exact (one_ne_zero : (1 : F2) ≠ 0)
      (by simpa [strassenV] using congrFun h (1 : Fin 4))
  · intro h
    exact (one_ne_zero : (1 : F2) ≠ 0)
      (by simpa [strassenV] using congrFun h (0 : Fin 4))
  · intro h
    exact (one_ne_zero : (1 : F2) ≠ 0)
      (by simpa [strassenV] using congrFun h (3 : Fin 4))
  · intro h
    exact (one_ne_zero : (1 : F2) ≠ 0)
      (by simpa [strassenV] using congrFun h (0 : Fin 4))
  · intro h
    exact (one_ne_zero : (1 : F2) ≠ 0)
      (by simpa [strassenV] using congrFun h (2 : Fin 4))

private theorem strassenW_ne_zero (s : Fin 7) : strassenW F2 s ≠ 0 := by
  fin_cases s
  · intro h
    exact (one_ne_zero : (1 : F2) ≠ 0)
      (by simpa [strassenW] using congrFun h (0 : Fin 4))
  · intro h
    exact (one_ne_zero : (1 : F2) ≠ 0)
      (by simpa [strassenW] using congrFun h (1 : Fin 4))
  · intro h
    exact (one_ne_zero : (1 : F2) ≠ 0)
      (by simpa [strassenW] using congrFun h (2 : Fin 4))
  · intro h
    exact (one_ne_zero : (1 : F2) ≠ 0)
      (by simpa [strassenW] using congrFun h (0 : Fin 4))
  · intro h
    exact (one_ne_zero : (1 : F2) ≠ 0)
      (by simpa [strassenW] using congrFun h (0 : Fin 4))
  · intro h
    exact (one_ne_zero : (1 : F2) ≠ 0)
      (by simpa [strassenW] using congrFun h (3 : Fin 4))
  · intro h
    exact (one_ne_zero : (1 : F2) ≠ 0)
      (by simpa [strassenW] using congrFun h (0 : Fin 4))

/-- The `s`-th normalized binary factor triple in Strassen's seven-product
scheme. The third factor uses the transposed output packing
`[C11,C21,C12,C22]` required by `matMulTensor`. -/
def strassenTerm (s : Fin 7) : Carrier profile444 :=
  (⟨strassenU F2 s, strassenU_ne_zero s⟩,
    ⟨strassenV F2 s, strassenV_ne_zero s⟩,
    ⟨strassenW F2 s, strassenW_ne_zero s⟩)

example : (strassenTerm 0).1.1 = ![1, 0, 0, 1] := rfl
example : (strassenTerm 0).2.2.1 = ![1, 0, 0, 1] := rfl

/-- Every indexed Strassen product is a nonzero rank-one tensor. -/
theorem strassenTerm_tensor_ne_zero (s : Fin 7) :
    tensorEvaluation (strassenTerm s) ≠ 0 :=
  tensorEvaluation_ne_zero (strassenTerm s)

/-- Strassen's seven normalized binary products as a finite-set state. -/
def strassenState : State profile444 :=
  Finset.univ.image strassenTerm

example : strassenState.card = 7 := by decide

/-- Any normalized binary finite-set state gives an ordered rank certificate
with as many slots as the state has terms. -/
theorem rankLE_stateEvaluation {p : Profile} (D : State p) :
    RankLE (stateEvaluation D) D.card := by
  refine ⟨fun s i => (D.equivFin.symm s).val.1.1 i,
    fun s j => (D.equivFin.symm s).val.2.1.1 j,
    fun s l => (D.equivFin.symm s).val.2.2.1 l, ?_⟩
  funext i j l
  rw [stateEvaluation_eq_sum]
  simp only [Finset.sum_apply, tensorEvaluation_apply]
  rw [← Finset.sum_coe_sort D
    (fun t => t.1.1 i * t.2.1.1 j * t.2.2.1 l)]
  exact (Equiv.sum_comp D.equivFin.symm
    (fun t => t.val.1.1 i * t.val.2.1.1 j * t.val.2.2.1 l)).symm

/-- The seven indexed Strassen products are pairwise distinct over `F₂`. -/
theorem strassenTerm_injective : Function.Injective strassenTerm := by
  decide

/-- The normalized Strassen state has exactly seven products. -/
theorem strassenState_card : strassenState.card = 7 := by
  rw [strassenState,
    Finset.card_image_of_injective Finset.univ strassenTerm_injective,
    Finset.card_univ, Fintype.card_fin]

set_option maxHeartbeats 800000 in
/-- The normalized Strassen state evaluates exactly to the binary `2 × 2`
matrix-multiplication tensor, with the third mode in transposed packing. -/
theorem strassenState_evaluation :
    stateEvaluation strassenState = matMulTensor F2 2 2 2 := by
  funext i j l
  fin_cases i <;> fin_cases j <;> fin_cases l <;> decide

/-- The generic state-enumeration bridge turns the normalized Strassen state
into a `RankLE` certificate whose slot count is definitionally its cardinality. -/
theorem strassenState_rankLE :
    RankLE (matMulTensor F2 2 2 2) strassenState.card := by
  rw [← strassenState_evaluation]
  exact rankLE_stateEvaluation strassenState

set_option maxHeartbeats 800000 in
/-- The explicit Strassen vectors over `F₂` directly construct a seven-slot
`RankLE` certificate for binary `2 × 2` matrix multiplication. -/
theorem strassen_rankLE_F2 : RankLE (matMulTensor F2 2 2 2) 7 :=
  ⟨strassenU F2, strassenV F2, strassenW F2, by decide⟩

/-- The independent Winograd lower bound and the explicit binary Strassen
certificate establish exact rank seven. -/
theorem rank_matMulTensor_F2_eq_seven :
    rank (matMulTensor F2 2 2 2) = 7 := by
  apply le_antisymm
  · exact rank_le_of_rankLE strassen_rankLE_F2
  · exact BilinearComplexity.seven_le_rank_matMulTensor_zmod

example : ∃ D : State profile444,
    stateEvaluation D = matMulTensor F2 2 2 2 :=
  ⟨strassenState, strassenState_evaluation⟩

/-- Every normalized finite-set state representing binary `2 × 2` matrix
multiplication contains at least seven distinct products. -/
theorem seven_le_card_of_stateEvaluation_eq_matMulTensor
    (D : State profile444)
    (hD : stateEvaluation D = matMulTensor F2 2 2 2) :
    7 ≤ D.card := by
  have hRank : rank (matMulTensor F2 2 2 2) ≤ D.card := by
    apply rank_le_of_rankLE
    rw [← hD]
    exact rankLE_stateEvaluation D
  exact BilinearComplexity.seven_le_rank_matMulTensor_zmod.trans hRank

/-- Executable entrywise equality check for the normalized Strassen state and
the binary matrix-multiplication tensor. -/
def strassenStateEvaluationMatches : Bool :=
  (List.ofFn fun i : Fin 4 => i).all fun i =>
    (List.ofFn fun j : Fin 4 => j).all fun j =>
      (List.ofFn fun l : Fin 4 => l).all fun l =>
        stateEvaluation strassenState i j l == matMulTensor F2 2 2 2 i j l

example : strassenStateEvaluationMatches = true := by decide

#eval strassenState.card
#eval strassenStateEvaluationMatches

#check @BilinearComplexity.seven_le_rank_matMulTensor_zmod
#check @rankLE_stateEvaluation
#check @strassenTerm_tensor_ne_zero
#check @strassenTerm_injective
#check @strassenState_card
#check @strassenState_evaluation
#check @strassenState_rankLE
#check @strassen_rankLE_F2
#check @rank_matMulTensor_F2_eq_seven
#check @seven_le_card_of_stateEvaluation_eq_matMulTensor

#print axioms BilinearComplexity.seven_le_rank_matMulTensor_zmod
#print axioms rankLE_stateEvaluation
#print axioms strassenTerm_tensor_ne_zero
#print axioms strassenTerm_injective
#print axioms strassenState_card
#print axioms strassenState_evaluation
#print axioms strassenState_rankLE
#print axioms strassen_rankLE_F2
#print axioms rank_matMulTensor_F2_eq_seven
#print axioms seven_le_card_of_stateEvaluation_eq_matMulTensor

end BilinearComplexity.BinaryMatMulRankCertificate
