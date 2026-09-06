import BilinearComplexity.FieldFiveToFourContext

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace BilinearComplexity.FieldFiveToFourContext.CertifiedFiveToFour
open FieldRankOne FieldContextual FieldNativeMoves FieldNativePath
open FieldNativePairBridge FieldFiveToFour
abbrev F3 := FieldFiveToFour.F3
variable {a b c : ℕ}

example {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I) :
    residualSource B = B.signedResidualSource := by
  classical
  have hq (i : Fin 5) : B.q ≠ I.atomAt i := q_ne_atomAt B i
  have hq' (i : Fin 5) : I.atomAt i ≠ B.q := (hq i).symm
  have hatom (i j : Fin 2 ⊕ Fin 3) :
      I.atomAt (I.slots i) = I.atomAt (I.slots j) ↔ i = j := by
    constructor
    · intro hij
      exact I.slots.injective (I.atomAt_injective hij)
    · intro hij
      subst j
      rfl
  have hslot (i j : Fin 2 ⊕ Fin 3) : I.slots i = I.slots j ↔ i = j :=
    I.slots.injective.eq_iff
  cases P : B.normalized with
  | sourceSource u v huv hfirst hsecond pair =>
      fin_cases u <;> fin_cases v <;>
        simp_all [residualSource, outerSource, outerTarget,
          FieldFiveToFour.CertifiedFiveToFour.signedResidualSource,
          EffectiveDisplayedF3PairTriple.signedResidualSource,
          EffectiveDisplayedF3PairTriple.residualShape,
          EffectiveDisplayedF3PairTriple.placement,
          FieldFiveToFour.CertifiedFiveToFour.signedResidualAtom,
          EffectiveDisplayedF3PairTriple.signedResidualAtom,
          EffectiveDisplayedF3PairTriple.residualAtomFamily,
          EffectiveDisplayedF3PairTriple.residualReindex,
          DisplayedF3PairTriple.sourceState, DisplayedF3PairTriple.targetState,
          pairState, singletonState, stateUnion, stateDifference, Finset.ext_iff,
          FieldFiveToFour.CertifiedFiveToFour.q,
          EffectiveDisplayedF3PairTriple.leftIndex,
          EffectiveDisplayedF3PairTriple.rightIndex, hatom, hslot,
          hq, hq'] <;> aesop
  | targetTarget u v huv hfirst hsecond pair =>
      fin_cases u <;> fin_cases v <;>
        simp_all [residualSource, outerSource, outerTarget,
          FieldFiveToFour.CertifiedFiveToFour.signedResidualSource,
          EffectiveDisplayedF3PairTriple.signedResidualSource,
          EffectiveDisplayedF3PairTriple.residualShape,
          EffectiveDisplayedF3PairTriple.placement,
          FieldFiveToFour.CertifiedFiveToFour.signedResidualAtom,
          EffectiveDisplayedF3PairTriple.signedResidualAtom,
          EffectiveDisplayedF3PairTriple.residualAtomFamily,
          EffectiveDisplayedF3PairTriple.residualReindex,
          EffectiveDisplayedF3PairTriple.normalizedSplit,
          DisplayedF3PairTriple.logicalSlots, pairFrontSplit, pairFrontPerm,
          Equiv.trans_apply, Equiv.swap_apply_def,
          targetTargetResidualReindex, pairFrontPerm4,
          DisplayedF3PairTriple.sourceState, DisplayedF3PairTriple.targetState,
          pairState, singletonState, stateUnion, stateDifference, Finset.ext_iff,
          FieldFiveToFour.CertifiedFiveToFour.q,
          EffectiveDisplayedF3PairTriple.leftIndex,
          EffectiveDisplayedF3PairTriple.rightIndex, hatom, hslot,
          hq, hq'] <;> aesop
  | oppositeForward u v hfirst hsecond pair =>
      fin_cases u <;> fin_cases v <;>
        simp_all [residualSource, outerSource, outerTarget,
          FieldFiveToFour.CertifiedFiveToFour.signedResidualSource,
          EffectiveDisplayedF3PairTriple.signedResidualSource,
          EffectiveDisplayedF3PairTriple.residualShape,
          EffectiveDisplayedF3PairTriple.placement,
          FieldFiveToFour.CertifiedFiveToFour.signedResidualAtom,
          EffectiveDisplayedF3PairTriple.signedResidualAtom,
          EffectiveDisplayedF3PairTriple.residualAtomFamily,
          EffectiveDisplayedF3PairTriple.residualReindex,
          DisplayedF3PairTriple.sourceState, DisplayedF3PairTriple.targetState,
          pairState, singletonState, stateUnion, stateDifference, Finset.ext_iff,
          FieldFiveToFour.CertifiedFiveToFour.q,
          EffectiveDisplayedF3PairTriple.leftIndex,
          EffectiveDisplayedF3PairTriple.rightIndex, hatom, hslot,
          hq, hq'] <;> aesop
  | oppositeReverse u v hfirst hsecond pair =>
      fin_cases u <;> fin_cases v <;>
        simp_all [residualSource, outerSource, outerTarget,
          FieldFiveToFour.CertifiedFiveToFour.signedResidualSource,
          EffectiveDisplayedF3PairTriple.signedResidualSource,
          EffectiveDisplayedF3PairTriple.residualShape,
          EffectiveDisplayedF3PairTriple.placement,
          FieldFiveToFour.CertifiedFiveToFour.signedResidualAtom,
          EffectiveDisplayedF3PairTriple.signedResidualAtom,
          EffectiveDisplayedF3PairTriple.residualAtomFamily,
          EffectiveDisplayedF3PairTriple.residualReindex,
          DisplayedF3PairTriple.sourceState, DisplayedF3PairTriple.targetState,
          pairState, singletonState, stateUnion, stateDifference, Finset.ext_iff,
          FieldFiveToFour.CertifiedFiveToFour.q,
          EffectiveDisplayedF3PairTriple.leftIndex,
          EffectiveDisplayedF3PairTriple.rightIndex, hatom, hslot,
          hq, hq'] <;> aesop

end BilinearComplexity.FieldFiveToFourContext.CertifiedFiveToFour
