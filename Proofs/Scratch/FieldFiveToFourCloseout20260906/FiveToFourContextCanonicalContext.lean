import BilinearComplexity.FieldFiveToFourContext

set_option autoImplicit false
namespace BilinearComplexity.FieldFiveToFourContext.CertifiedFiveToFour
open FieldRankOne FieldContextual FieldNativeMoves FieldNativePath
open FieldNativePairBridge FieldFiveToFour
abbrev F3 := FieldFiveToFour.F3
variable {a b c : ℕ}

/-- With the contraction atom present in source/source placement, the retained residual context
is the old context without that atom together with the original source. -/
theorem residualContext_eq_of_sourceSource_q_mem
    {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I)
    (C : State F3 a b c) (hp : B.normalized.placement = .sourceSource)
    (hq : B.q ∈ C) :
    residualContext B C = stateUnion (stateDifference C (singletonState B.q)) I.sourceState := by
  rw [residualContext]
  have hs : schedule B C = .afterResidual := by
    simp [schedule, hp, hq]
  rw [hs, outerTarget_eq_singletonState_of_sourceSource B hp,
    outerSource_eq_sourceState_of_sourceSource B hp]
  classical
  ext x
  simp only [stateUnion, stateDifference, singletonState, Finset.mem_union,
    Finset.mem_sdiff, Finset.mem_singleton]
  have hqS : B.q ∉ I.sourceState := q_not_mem_sourceState B
  aesop

/-- In the occupied source/source schedule, the requested residual start is retained context
union intrinsic residual source. -/
theorem requestStart_eq_residualContext_union_residualSource_of_sourceSource_q_mem
    {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I)
    (C : State F3 a b c) (hp : B.normalized.placement = .sourceSource)
    (hq : B.q ∈ C) :
    requestStart B C = stateUnion (residualContext B C) (residualSource B) := by
  have hs : schedule B C = .afterResidual := by simp [schedule, hp, hq]
  rw [requestStart, hs, residualContext_eq_of_sourceSource_q_mem B C hp hq,
    residualSource_eq_signedResidualSource_of_sourceSource B hp,
    signedResidualSource_eq_singletonState_of_sourceSource B hp]
  classical
  ext x
  simp only [stateUnion, stateDifference, singletonState, Finset.mem_union,
    Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · intro hx
    rcases hx with hxC | hxS
    · by_cases hxq : x = B.q
      · exact Or.inr hxq
      · exact Or.inl (Or.inl ⟨hxC, hxq⟩)
    · exact Or.inl (Or.inr hxS)
  · rintro (⟨⟨hxC, _⟩ | hxS⟩ | rfl)
    · exact Or.inl hxC
    · exact Or.inr hxS
    · exact Or.inl hq

/-- In the occupied source/source schedule, the requested residual finish is retained context
union intrinsic residual target. -/
theorem requestFinish_eq_residualContext_union_residualTarget_of_sourceSource_q_mem
    {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I)
    (C : State F3 a b c) (hp : B.normalized.placement = .sourceSource)
    (hq : B.q ∈ C) :
    requestFinish B C = stateUnion (residualContext B C) (residualTarget B) := by
  have hs : schedule B C = .afterResidual := by simp [schedule, hp, hq]
  rw [requestFinish, hs, outerTarget_eq_singletonState_of_sourceSource B hp,
    outerSource_eq_sourceState_of_sourceSource B hp,
    residualContext_eq_of_sourceSource_q_mem B C hp hq,
    residualTarget_eq_targetState_of_sourceSource B hp]
  classical
  ext x
  simp only [stateUnion, stateDifference, singletonState, Finset.mem_union,
    Finset.mem_sdiff, Finset.mem_singleton]
  have hqS : B.q ∉ I.sourceState := q_not_mem_sourceState B
  have hqT : B.q ∉ I.targetState := q_not_mem_targetState B
  aesop

end BilinearComplexity.FieldFiveToFourContext.CertifiedFiveToFour
