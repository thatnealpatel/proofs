import BilinearComplexity.FieldFiveToFourContext

set_option autoImplicit false
namespace BilinearComplexity.FieldFiveToFourContext.CertifiedFiveToFour

open FieldRankOne FieldContextual FieldNativeMoves FieldNativePath
open FieldNativePairBridge FieldFiveToFour

abbrev F3 := FieldFiveToFour.F3
variable {a b c : ℕ}

/-- Scratch proof of the absent source/source retained-context identity. -/
theorem scratch_residualContext_eq_of_sourceSource_q_not_mem
    {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I)
    (C : State F3 a b c) (hp : B.normalized.placement = .sourceSource)
    (hq : B.q ∉ C)
    (hC : Disjoint C (stateUnion I.sourceState I.targetState)) :
    residualContext B C = C := by
  have hs : schedule B C = .beforeResidual := by
    simp [schedule, hp, hq]
  have hCS : Disjoint C I.sourceState := by
    rw [Finset.disjoint_left] at hC ⊢
    intro x hxC hxSource
    exact hC hxC (by
      classical
      simp only [stateUnion, Finset.mem_union]
      exact Or.inl hxSource)
  rw [residualContext, hs, outerSource_eq_sourceState_of_sourceSource B hp,
    outerTarget_eq_singletonState_of_sourceSource B hp]
  classical
  ext x
  simp only [stateUnion, stateDifference, singletonState, Finset.mem_union,
    Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · rintro (hxOld | hxImpossible)
    · exact hxOld.1
    · exact False.elim (hxImpossible.2 hxImpossible.1)
  · intro hxC
    exact Or.inl ⟨hxC, fun hxSource =>
      Finset.disjoint_left.mp hCS hxC hxSource⟩

example {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I)
    (C : State F3 a b c) (hp : B.normalized.placement = .sourceSource)
    (hq : B.q ∉ C)
    (hC : Disjoint C (stateUnion I.sourceState I.targetState)) :
    requestStart B C = stateUnion (residualContext B C) B.signedResidualSource := by
  have hs : schedule B C = .beforeResidual := by
    simp [schedule, hp, hq]
  have hCS : Disjoint C I.sourceState := by
    rw [Finset.disjoint_left] at hC ⊢
    intro x hxC hxSource
    exact hC hxC (by
      classical
      simp only [stateUnion, Finset.mem_union]
      exact Or.inl hxSource)
  have hcancel :
      stateDifference (stateUnion C I.sourceState) I.sourceState = C := by
    classical
    ext x
    simp only [stateDifference, stateUnion, Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hxC | hxSource, hxNotSource⟩
      · exact hxC
      · exact False.elim (hxNotSource hxSource)
    · intro hxC
      exact ⟨Or.inl hxC, fun hxSource =>
        Finset.disjoint_left.mp hCS hxC hxSource⟩
  rw [requestStart, hs, outerSource_eq_sourceState_of_sourceSource B hp,
    outerTarget_eq_singletonState_of_sourceSource B hp, hcancel,
    scratch_residualContext_eq_of_sourceSource_q_not_mem B C hp hq hC,
    signedResidualSource_eq_singletonState_of_sourceSource B hp]

example {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I)
    (C : State F3 a b c) (hp : B.normalized.placement = .sourceSource)
    (hq : B.q ∉ C)
    (hC : Disjoint C (stateUnion I.sourceState I.targetState)) :
    requestFinish B C = stateUnion (residualContext B C) B.signedResidualTarget := by
  have hs : schedule B C = .beforeResidual := by
    simp [schedule, hp, hq]
  rw [requestFinish, hs,
    scratch_residualContext_eq_of_sourceSource_q_not_mem B C hp hq hC,
    signedResidualTarget_eq_targetState_of_sourceSource B hp]

example {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I)
    (C : State F3 a b c) (hp : B.normalized.placement = .sourceSource)
    (hq : B.q ∉ C)
    (hC : Disjoint C (stateUnion I.sourceState I.targetState)) :
    Disjoint (residualContext B C)
      (stateUnion B.signedResidualSource B.signedResidualTarget) := by
  rw [scratch_residualContext_eq_of_sourceSource_q_not_mem B C hp hq hC,
    signedResidualSource_eq_singletonState_of_sourceSource B hp,
    signedResidualTarget_eq_targetState_of_sourceSource B hp]
  classical
  rw [Finset.disjoint_left]
  intro x hxC hxEndpoints
  simp only [stateUnion, singletonState, Finset.mem_union,
    Finset.mem_singleton] at hxEndpoints
  rcases hxEndpoints with hxq | hxTarget
  · subst x
    exact hq hxC
  · exact Finset.disjoint_left.mp hC hxC (by
      simp only [stateUnion, Finset.mem_union]
      exact Or.inr hxTarget)

end BilinearComplexity.FieldFiveToFourContext.CertifiedFiveToFour
