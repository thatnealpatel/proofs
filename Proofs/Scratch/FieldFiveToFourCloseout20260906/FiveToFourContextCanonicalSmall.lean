import BilinearComplexity.FieldFiveToFourContext
set_option autoImplicit false
namespace BilinearComplexity.FieldFiveToFourContext.CertifiedFiveToFour
open FieldRankOne FieldContextual FieldNativeMoves FieldNativePath
open FieldNativePairBridge FieldFiveToFour
abbrev F3 := FieldFiveToFour.F3
variable {a b c : ℕ}

/-- In source/source placement, the outer source is the original source pair. -/
theorem outerSource_eq_sourceState_of_sourceSource {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I)
    (hp : B.normalized.placement = .sourceSource) :
    outerSource B = I.sourceState := by
  classical
  cases P : B.normalized with
  | sourceSource u v huv hfirst hsecond pair =>
      fin_cases u <;> fin_cases v <;>
        first
        | omega
        | (simp_all [P, outerSource, EffectiveDisplayedF3PairTriple.placement,
            EffectiveDisplayedF3PairTriple.leftIndex,
            EffectiveDisplayedF3PairTriple.rightIndex,
            DisplayedF3PairTriple.sourceState, pairState, Finset.ext_iff,
            I.atomAt_injective.eq_iff] <;> aesop)
  | targetTarget u v huv hfirst hsecond pair => simp [P, EffectiveDisplayedF3PairTriple.placement] at hp
  | oppositeForward u v hfirst hsecond pair => simp [P, EffectiveDisplayedF3PairTriple.placement] at hp
  | oppositeReverse u v hfirst hsecond pair => simp [P, EffectiveDisplayedF3PairTriple.placement] at hp

/-- In source/source placement, the canonical residual source is the contraction singleton. -/
theorem signedResidualSource_eq_singletonState_of_sourceSource {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (hp : B.normalized.placement = .sourceSource) :
    B.signedResidualSource = singletonState B.q := by
  classical
  cases P : B.normalized with
  | sourceSource u v huv hfirst hsecond pair =>
      simp [P, FieldFiveToFour.CertifiedFiveToFour.signedResidualSource,
        EffectiveDisplayedF3PairTriple.signedResidualSource,
        EffectiveDisplayedF3PairTriple.residualShape,
        EffectiveDisplayedF3PairTriple.placement,
        FieldFiveToFour.CertifiedFiveToFour.signedResidualAtom,
        EffectiveDisplayedF3PairTriple.signedResidualAtom,
        EffectiveDisplayedF3PairTriple.residualReindex,
        EffectiveDisplayedF3PairTriple.residualAtomFamily,
        FieldFiveToFour.CertifiedFiveToFour.q]
  | targetTarget u v huv hfirst hsecond pair => simp [P, EffectiveDisplayedF3PairTriple.placement] at hp
  | oppositeForward u v hfirst hsecond pair => simp [P, EffectiveDisplayedF3PairTriple.placement] at hp
  | oppositeReverse u v hfirst hsecond pair => simp [P, EffectiveDisplayedF3PairTriple.placement] at hp

/-- In source/source placement, the outer target is the contraction singleton. -/
theorem outerTarget_eq_singletonState_of_sourceSource
    {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I)
    (hp : B.normalized.placement = .sourceSource) :
    outerTarget B = singletonState B.q := by
  classical
  cases P : B.normalized with
  | sourceSource u v huv hfirst hsecond pair =>
      simp [P, outerTarget, EffectiveDisplayedF3PairTriple.placement,
        FieldFiveToFour.CertifiedFiveToFour.q]
  | targetTarget u v huv hfirst hsecond pair =>
      simp [P, EffectiveDisplayedF3PairTriple.placement] at hp
  | oppositeForward u v hfirst hsecond pair =>
      simp [P, EffectiveDisplayedF3PairTriple.placement] at hp
  | oppositeReverse u v hfirst hsecond pair =>
      simp [P, EffectiveDisplayedF3PairTriple.placement] at hp

/-- In source/source placement, the intrinsic residual source is the canonical signed source. -/
theorem residualSource_eq_signedResidualSource_of_sourceSource
    {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I)
    (hp : B.normalized.placement = .sourceSource) :
    residualSource B = B.signedResidualSource := by
  rw [residualSource, outerSource_eq_sourceState_of_sourceSource B hp,
    outerTarget_eq_singletonState_of_sourceSource B hp,
    signedResidualSource_eq_singletonState_of_sourceSource B hp]
  classical
  ext x
  simp only [stateUnion, stateDifference, singletonState,
    Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
  have hqT : B.q ∉ I.targetState := q_not_mem_targetState B
  aesop

/-- In source/source placement, the intrinsic residual target is the original target triple. -/
theorem residualTarget_eq_targetState_of_sourceSource
    {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I)
    (hp : B.normalized.placement = .sourceSource) :
    residualTarget B = I.targetState := by
  rw [residualTarget, outerSource_eq_sourceState_of_sourceSource B hp,
    outerTarget_eq_singletonState_of_sourceSource B hp]
  classical
  ext x
  simp only [stateUnion, stateDifference, singletonState,
    Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
  have hqT : B.q ∉ I.targetState := q_not_mem_targetState B
  aesop

/-- In source/source placement, the canonical residual target is the original target triple. -/
theorem signedResidualTarget_eq_targetState_of_sourceSource
    {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I)
    (hp : B.normalized.placement = .sourceSource) :
    B.signedResidualTarget = I.targetState := by
  classical
  cases P : B.normalized with
  | sourceSource u v huv hfirst hsecond pair =>
      have hL : B.normalized.leftIndex = I.slots (.inl u) := by
        simpa [P, EffectiveDisplayedF3PairTriple.leftIndex] using hfirst
      have hR : B.normalized.rightIndex = I.slots (.inl v) := by
        simpa [P, EffectiveDisplayedF3PairTriple.rightIndex] using hsecond
      have h0 : B.normalized.normalizedSplit (.inl 0) = I.slots (.inl u) :=
        B.normalized.normalizedSplit_left_zero.trans hL
      have h1 : B.normalized.normalizedSplit (.inl 1) = I.slots (.inl v) :=
        B.normalized.normalizedSplit_left_one.trans hR
      have hcover (i : Fin 2) : i = u ∨ i = v := by
        fin_cases u <;> fin_cases v <;> fin_cases i <;> simp_all
      have hleft :
          Set.range (fun i : Fin 2 => B.normalized.normalizedSplit (.inl i)) =
            Set.range (fun i : Fin 2 => I.slots (.inl i)) := by
        ext k
        constructor
        · rintro ⟨i, rfl⟩
          fin_cases i
          · exact ⟨u, h0.symm⟩
          · exact ⟨v, h1.symm⟩
        · rintro ⟨i, rfl⟩
          rcases hcover i with rfl | rfl
          · exact ⟨0, h0⟩
          · exact ⟨1, h1⟩
      have hright := range_comp_inr_eq_of_range_inl_eq
        B.normalized.normalizedSplit I.slots I.atomAt hleft
      have hfin :
          Finset.univ.image (fun j : Fin 3 =>
              I.atomAt (B.normalized.normalizedSplit (.inr j))) =
            Finset.univ.image (fun j : Fin 3 => I.atomAt (I.slots (.inr j))) := by
        ext x
        simpa only [Finset.mem_image, Finset.mem_univ, true_and,
          Set.ext_iff, Set.mem_range] using Set.ext_iff.mp hright x
      rw [DisplayedF3PairTriple.targetState, ← hfin]
      ext x
      simp [P, FieldFiveToFour.CertifiedFiveToFour.signedResidualTarget,
        EffectiveDisplayedF3PairTriple.signedResidualTarget,
        EffectiveDisplayedF3PairTriple.residualShape,
        EffectiveDisplayedF3PairTriple.placement,
        FieldFiveToFour.CertifiedFiveToFour.signedResidualAtom,
        EffectiveDisplayedF3PairTriple.signedResidualAtom,
        EffectiveDisplayedF3PairTriple.residualReindex,
        EffectiveDisplayedF3PairTriple.residualAtomFamily, tripleState]
  | targetTarget u v huv hfirst hsecond pair =>
      simp [P, EffectiveDisplayedF3PairTriple.placement] at hp
  | oppositeForward u v hfirst hsecond pair =>
      simp [P, EffectiveDisplayedF3PairTriple.placement] at hp
  | oppositeReverse u v hfirst hsecond pair =>
      simp [P, EffectiveDisplayedF3PairTriple.placement] at hp

/-- In source/source placement, the intrinsic residual target is the canonical signed target. -/
theorem residualTarget_eq_signedResidualTarget_of_sourceSource
    {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I)
    (hp : B.normalized.placement = .sourceSource) :
    residualTarget B = B.signedResidualTarget := by
  rw [residualTarget_eq_targetState_of_sourceSource B hp,
    signedResidualTarget_eq_targetState_of_sourceSource B hp]

end BilinearComplexity.FieldFiveToFourContext.CertifiedFiveToFour
