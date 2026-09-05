import BilinearComplexity.BinaryAmbientMoves

set_option autoImplicit false

/-!
# Structural support of intrinsic binary ambient moves

This file identifies the exact finite symmetric-difference support of every
intrinsic move. It also records native inverse witnesses and the factor-line
geometry of three-term supports.
-/

namespace BilinearComplexity.BinaryAmbientMoveSupport

open scoped symmDiff TensorProduct BigOperators
open BinaryCircuit
open BinaryAmbientCarrier
open BinaryAmbientMoves
open NormalizedBinaryCarrier (F2 CoordinateVector)

universe u v w

variable {U : Type u} {V : Type v} {W : Type w}
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [Module F2 U] [Module F2 V] [Module F2 W]
variable [DecidableEq U] [DecidableEq V] [DecidableEq W]

omit [Module F2 U] [Module F2 V] [Module F2 W] in
private theorem split_outputLeft_ne_source
    {source outputLeft outputRight : Carrier U V W}
    {D E : State U V W}
    (h : GeneratedFirstSplit source outputLeft outputRight D E) :
    outputLeft ≠ source := by
  intro heq
  have hfirst := h.2.2.2.2.1
  rw [heq] at hfirst
  have hzero : outputRight.1.1 = 0 :=
    add_left_cancel (hfirst.symm.trans (add_zero _).symm)
  exact outputRight.1.2 hzero

omit [Module F2 U] [Module F2 V] [Module F2 W] in
private theorem split_outputRight_ne_source
    {source outputLeft outputRight : Carrier U V W}
    {D E : State U V W}
    (h : GeneratedFirstSplit source outputLeft outputRight D E) :
    outputRight ≠ source := by
  intro heq
  have hfirst := h.2.2.2.2.1
  rw [heq] at hfirst
  have hzero : outputLeft.1.1 = 0 :=
    add_right_cancel (hfirst.symm.trans (zero_add _).symm)
  exact outputLeft.1.2 hzero

omit [Module F2 U] [Module F2 V] [Module F2 W] in
/-- A Split changes exactly its source and its two fresh outputs. -/
theorem GeneratedFirstSplit.symmDiff_eq
    {source outputLeft outputRight : Carrier U V W}
    {D E : State U V W}
    (h : GeneratedFirstSplit source outputLeft outputRight D E) :
    D ∆ E = {source, outputLeft, outputRight} := by
  rcases h with ⟨hsource, hlr, hl, hr, hfirst, hls, hrs, hlt, hrt, rfl⟩
  have hlns : outputLeft ≠ source := split_outputLeft_ne_source
    ⟨hsource, hlr, hl, hr, hfirst, hls, hrs, hlt, hrt, rfl⟩
  have hrns : outputRight ≠ source := split_outputRight_ne_source
    ⟨hsource, hlr, hl, hr, hfirst, hls, hrs, hlt, hrt, rfl⟩
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_erase,
    Finset.mem_singleton]
  aesop

omit [Module F2 U] [Module F2 V] [Module F2 W] in
private theorem reduction_target_ne_sourceLeft
    {sourceLeft sourceRight target : Carrier U V W}
    {D E : State U V W}
    (h : DirectedNarrowPairReduction sourceLeft sourceRight target D E) :
    target ≠ sourceLeft := by
  intro heq
  have hfirst := h.2.2.2.2.2.2.1
  have heqFirst := congrArg (fun t : Carrier U V W => t.1.1) heq
  have hzero : sourceRight.1.1 = 0 := add_left_cancel
    (hfirst.symm.trans (heqFirst.trans (add_zero _).symm))
  exact sourceRight.1.2 hzero

omit [Module F2 U] [Module F2 V] [Module F2 W] in
private theorem reduction_target_ne_sourceRight
    {sourceLeft sourceRight target : Carrier U V W}
    {D E : State U V W}
    (h : DirectedNarrowPairReduction sourceLeft sourceRight target D E) :
    target ≠ sourceRight := by
  intro heq
  have hfirst := h.2.2.2.2.2.2.1
  have heqFirst := congrArg (fun t : Carrier U V W => t.1.1) heq
  have hzero : sourceLeft.1.1 = 0 := add_right_cancel
    (hfirst.symm.trans (heqFirst.trans (zero_add _).symm))
  exact sourceLeft.1.2 hzero

omit [Module F2 U] [Module F2 V] [Module F2 W] in
/-- A directed Reduction changes exactly its two sources and its fresh target. -/
theorem DirectedNarrowPairReduction.symmDiff_eq
    {sourceLeft sourceRight target : Carrier U V W}
    {D E : State U V W}
    (h : DirectedNarrowPairReduction sourceLeft sourceRight target D E) :
    D ∆ E = {sourceLeft, sourceRight, target} := by
  rcases h with ⟨hleft, hright, hlr, hfresh, hsecond, hthird, hfirst,
    htargetSecond, htargetThird, rfl⟩
  have htleft : target ≠ sourceLeft := reduction_target_ne_sourceLeft
    ⟨hleft, hright, hlr, hfresh, hsecond, hthird, hfirst,
      htargetSecond, htargetThird, rfl⟩
  have htright : target ≠ sourceRight := reduction_target_ne_sourceRight
    ⟨hleft, hright, hlr, hfresh, hsecond, hthird, hfirst,
      htargetSecond, htargetThird, rfl⟩
  have htD : target ∉ D := by
    intro ht
    apply hfresh
    exact Finset.mem_erase.mpr ⟨htright,
      Finset.mem_erase.mpr ⟨htleft, ht⟩⟩
  ext x
  simp only [Finset.mem_symmDiff]
  by_cases hxLeft : x = sourceLeft
  · subst x
    simp [hleft, hlr, htleft.symm]
  by_cases hxRight : x = sourceRight
  · subst x
    simp [hright, htright.symm]
  by_cases hxTarget : x = target
  · subst x
    simp [htD]
  simp [hxLeft, hxRight, hxTarget]

omit [Module F2 U] [Module F2 V] [Module F2 W] in
private theorem flip_targetLeft_ne_sourceLeft
    {sourceLeft sourceRight targetLeft targetRight : Carrier U V W}
    {D E : State U V W}
    (h : SourceThirdFlip sourceLeft sourceRight targetLeft targetRight D E) :
    targetLeft ≠ sourceLeft := by
  intro heq
  have hfirst := h.2.2.2.2.2.2.2.1
  have heqFirst := congrArg (fun t : Carrier U V W => t.1.1) heq
  have hzero : sourceRight.1.1 = 0 := add_left_cancel
    (hfirst.symm.trans (heqFirst.trans (add_zero _).symm))
  exact sourceRight.1.2 hzero

omit [Module F2 U] [Module F2 V] [Module F2 W] in
private theorem flip_targetLeft_ne_sourceRight
    {sourceLeft sourceRight targetLeft targetRight : Carrier U V W}
    {D E : State U V W}
    (h : SourceThirdFlip sourceLeft sourceRight targetLeft targetRight D E) :
    targetLeft ≠ sourceRight := by
  intro heq
  have hfirst := h.2.2.2.2.2.2.2.1
  have heqFirst := congrArg (fun t : Carrier U V W => t.1.1) heq
  have hzero : sourceLeft.1.1 = 0 := add_right_cancel
    (hfirst.symm.trans (heqFirst.trans (zero_add _).symm))
  exact sourceLeft.1.2 hzero

omit [Module F2 U] [Module F2 W] in
private theorem flip_targetRight_ne_sourceRight
    {sourceLeft sourceRight targetLeft targetRight : Carrier U V W}
    {D E : State U V W}
    (h : SourceThirdFlip sourceLeft sourceRight targetLeft targetRight D E) :
    targetRight ≠ sourceRight := by
  intro heq
  have hsecond := h.2.2.2.2.2.2.2.2.2.2.2.1
  have heqSecond := congrArg (fun t : Carrier U V W => t.2.1.1) heq
  have hadd : sourceRight.2.1.1 + sourceLeft.2.1.1 =
      sourceRight.2.1.1 + 0 := by
    rw [← ZModModule.sub_eq_add]
    exact hsecond.symm.trans (heqSecond.trans (add_zero _).symm)
  exact sourceLeft.2.1.2 (add_left_cancel hadd)

omit [Module F2 U] [Module F2 W] in
private theorem flip_targetRight_ne_sourceLeft
    {sourceLeft sourceRight targetLeft targetRight : Carrier U V W}
    {D E : State U V W}
    (h : SourceThirdFlip sourceLeft sourceRight targetLeft targetRight D E) :
    targetRight ≠ sourceLeft := by
  intro heq
  have hsecond := h.2.2.2.2.2.2.2.2.2.2.2.1
  have heqSecond := congrArg (fun t : Carrier U V W => t.2.1.1) heq
  have hadd : sourceRight.2.1.1 + sourceLeft.2.1.1 =
      0 + sourceLeft.2.1.1 := by
    rw [← ZModModule.sub_eq_add]
    exact hsecond.symm.trans (heqSecond.trans (zero_add _).symm)
  exact sourceRight.2.1.2 (add_right_cancel hadd)

omit [Module F2 U] [Module F2 W] in
/-- A Flip changes exactly its two sources and two fresh targets. -/
theorem SourceThirdFlip.symmDiff_eq
    {sourceLeft sourceRight targetLeft targetRight : Carrier U V W}
    {D E : State U V W}
    (h : SourceThirdFlip sourceLeft sourceRight targetLeft targetRight D E) :
    D ∆ E = {sourceLeft, sourceRight, targetLeft, targetRight} := by
  rcases h with ⟨hleft, hright, hsources, hfreshLeft, hfreshRight, htargets,
    hthird, htlf, htls, htlt, htrf, htrs, htrt, rfl⟩
  let h₀ : SourceThirdFlip sourceLeft sourceRight targetLeft targetRight D
      (insert targetLeft (insert targetRight
        ((D.erase sourceLeft).erase sourceRight))) :=
    ⟨hleft, hright, hsources, hfreshLeft, hfreshRight, htargets,
      hthird, htlf, htls, htlt, htrf, htrs, htrt, rfl⟩
  have htlasl := flip_targetLeft_ne_sourceLeft h₀
  have htlasr := flip_targetLeft_ne_sourceRight h₀
  have htrasl := flip_targetRight_ne_sourceLeft h₀
  have htrasr := flip_targetRight_ne_sourceRight h₀
  have htlD : targetLeft ∉ D := by
    intro ht
    apply hfreshLeft
    exact Finset.mem_erase.mpr ⟨htlasr,
      Finset.mem_erase.mpr ⟨htlasl, ht⟩⟩
  have htrD : targetRight ∉ D := by
    intro ht
    apply hfreshRight
    exact Finset.mem_erase.mpr ⟨htrasr,
      Finset.mem_erase.mpr ⟨htrasl, ht⟩⟩
  ext x
  simp only [Finset.mem_symmDiff]
  by_cases hxSL : x = sourceLeft
  · subst x
    simp [hleft, hsources, htlasl.symm, htrasl.symm]
  by_cases hxSR : x = sourceRight
  · subst x
    simp [hright, htlasr.symm, htrasr.symm]
  by_cases hxTL : x = targetLeft
  · subst x
    simp [htlD, htargets]
  by_cases hxTR : x = targetRight
  · subst x
    simp [htrD]
  simp [hxSL, hxSR, hxTL, hxTR]

omit [Module F2 U] [Module F2 V] [Module F2 W] in
/-- Reversing a Split is a directed Reduction from its two outputs back
to its source. -/
theorem GeneratedFirstSplit.reverse_reduction
    {source outputLeft outputRight : Carrier U V W} {D E : State U V W}
    (h : GeneratedFirstSplit source outputLeft outputRight D E) :
    DirectedNarrowPairReduction outputLeft outputRight source E D := by
  rcases h with ⟨hsource, hlr, hl, hr, hfirst, hls, hrs, hlt, hrt, rfl⟩
  let h₀ : GeneratedFirstSplit source outputLeft outputRight D
      (insert outputLeft (insert outputRight (D.erase source))) :=
    ⟨hsource, hlr, hl, hr, hfirst, hls, hrs, hlt, hrt, rfl⟩
  have hlns := split_outputLeft_ne_source h₀
  have hrns := split_outputRight_ne_source h₀
  refine ⟨by simp, by simp, hlr, ?_, hrs.trans hls.symm,
    hrt.trans hlt.symm, hfirst, hls.symm, hlt.symm, ?_⟩
  · simp only [Finset.mem_erase, Finset.mem_insert, not_and, not_or]
    aesop
  · ext x
    simp [hlr, hl, hr, hsource]

omit [Module F2 U] [Module F2 V] [Module F2 W] in
/-- Reversing a directed Reduction is a Split from its singleton target back
to its ordered source pair. -/
theorem DirectedNarrowPairReduction.reverse_split
    {sourceLeft sourceRight target : Carrier U V W} {D E : State U V W}
    (h : DirectedNarrowPairReduction sourceLeft sourceRight target D E) :
    GeneratedFirstSplit target sourceLeft sourceRight E D := by
  rcases h with ⟨hleft, hright, hlr, hfresh, hsecond, hthird, hfirst,
    htargetSecond, htargetThird, rfl⟩
  have hrightErase : sourceRight ∈ D.erase sourceLeft :=
    Finset.mem_erase.mpr ⟨hlr.symm, hright⟩
  refine ⟨by simp, hlr, ?_, ?_, hfirst, htargetSecond.symm,
    hsecond.trans htargetSecond.symm, htargetThird.symm,
    hthird.trans htargetThird.symm, ?_⟩
  · simp [Finset.erase_insert hfresh]
  · simp [Finset.erase_insert hfresh]
  · rw [Finset.erase_insert hfresh, Finset.insert_erase hrightErase,
      Finset.insert_erase hleft]

omit [Module F2 W] in
/-- Reversing a Flip is the same ordered shear applied to its target pair. -/
theorem SourceThirdFlip.reverse_flip
    {sourceLeft sourceRight targetLeft targetRight : Carrier U V W}
    {D E : State U V W}
    (h : SourceThirdFlip sourceLeft sourceRight targetLeft targetRight D E) :
    SourceThirdFlip targetLeft targetRight sourceLeft sourceRight E D := by
  rcases h with ⟨hleft, hright, hsources, hfreshLeft, hfreshRight, htargets,
    hthird, htlf, htls, htlt, htrf, htrs, htrt, rfl⟩
  let h₀ : SourceThirdFlip sourceLeft sourceRight targetLeft targetRight D
      (insert targetLeft (insert targetRight
        ((D.erase sourceLeft).erase sourceRight))) :=
    ⟨hleft, hright, hsources, hfreshLeft, hfreshRight, htargets,
      hthird, htlf, htls, htlt, htrf, htrs, htrt, rfl⟩
  have htlasl := flip_targetLeft_ne_sourceLeft h₀
  have htlasr := flip_targetLeft_ne_sourceRight h₀
  have htrasl := flip_targetRight_ne_sourceLeft h₀
  have htrasr := flip_targetRight_ne_sourceRight h₀
  refine ⟨by simp, by simp, htargets, ?_, ?_, hsources, ?_, ?_,
    htls.symm, ?_, htrf.symm, ?_, ?_, ?_⟩
  · simp [hsources, htargets, hfreshLeft, hfreshRight]
  · simp [htargets, hfreshLeft, hfreshRight]
  · exact htrt.trans htlt.symm
  · calc
      sourceLeft.1.1 =
          (sourceLeft.1.1 + sourceRight.1.1) + sourceRight.1.1 := by
        rw [add_assoc, ZModModule.add_self, add_zero]
      _ = targetLeft.1.1 + targetRight.1.1 := by rw [htlf, htrf]
  · exact htlt.symm
  · rw [htrs, htls, ZModModule.sub_eq_add, ZModModule.sub_eq_add,
      add_assoc, ZModModule.add_self, add_zero]
  · exact hthird.trans htlt.symm
  · have hc : targetLeft ∉ insert targetRight
        ((D.erase sourceLeft).erase sourceRight) := by
      simpa only [Finset.mem_insert, not_or] using ⟨htargets, hfreshLeft⟩
    have hrightErase : sourceRight ∈ D.erase sourceLeft :=
      Finset.mem_erase.mpr ⟨hsources.symm, hright⟩
    rw [Finset.erase_insert hc, Finset.erase_insert hfreshRight,
      Finset.insert_erase hrightErase, Finset.insert_erase hleft]

omit [Module F2 W] in
/-- Every ordered intrinsic move has an intrinsic reverse move. -/
theorem Move.reverse {D E : State U V W} (h : Move D E) : Move E D := by
  cases h with
  | generatedFirstSplit hsplit =>
      exact Move.directedNarrowPairReduction
        (BilinearComplexity.BinaryAmbientMoveSupport.GeneratedFirstSplit.reverse_reduction hsplit)
  | sourceThirdFlip hflip =>
      exact Move.sourceThirdFlip
        (BilinearComplexity.BinaryAmbientMoveSupport.SourceThirdFlip.reverse_flip hflip)
  | directedNarrowPairReduction hreduction =>
      exact Move.generatedFirstSplit
        (BilinearComplexity.BinaryAmbientMoveSupport.DirectedNarrowPairReduction.reverse_split hreduction)

/-- Every intrinsic move in any mode ordering has a reverse in the same mode
ordering. -/
theorem AllModeMove.reverse {D E : State U V W} (h : AllModeMove D E) :
    AllModeMove E D := by
  cases h with
  | abc hmove =>
      exact AllModeMove.abc
        (BilinearComplexity.BinaryAmbientMoveSupport.Move.reverse hmove)
  | bca hmove hD hE =>
      exact AllModeMove.bca
        (BilinearComplexity.BinaryAmbientMoveSupport.Move.reverse hmove) hE hD
  | cab hmove hD hE =>
      exact AllModeMove.cab
        (BilinearComplexity.BinaryAmbientMoveSupport.Move.reverse hmove) hE hD
  | acb hmove hD hE =>
      exact AllModeMove.acb
        (BilinearComplexity.BinaryAmbientMoveSupport.Move.reverse hmove) hE hD
  | cba hmove hD hE =>
      exact AllModeMove.cba
        (BilinearComplexity.BinaryAmbientMoveSupport.Move.reverse hmove) hE hD
  | bac hmove hD hE =>
      exact AllModeMove.bac
        (BilinearComplexity.BinaryAmbientMoveSupport.Move.reverse hmove) hE hD

omit [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq U] [DecidableEq V] [DecidableEq W] in
/-- Cyclic reordering from `(W,U,V)` to `(U,V,W)` is injective. -/
theorem permuteBCATerm_injective :
    Function.Injective (permuteBCATerm (U := U) (V := V) (W := W)) := by
  intro s t hst
  rcases s with ⟨s₁, s₂, s₃⟩
  rcases t with ⟨t₁, t₂, t₃⟩
  injection hst with h₁ h₂₃
  injection h₂₃ with h₂ h₃
  subst_vars
  rfl

omit [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq U] [DecidableEq V] [DecidableEq W] in
/-- Cyclic reordering from `(V,W,U)` to `(U,V,W)` is injective. -/
theorem permuteCABTerm_injective :
    Function.Injective (permuteCABTerm (U := U) (V := V) (W := W)) := by
  intro s t hst
  rcases s with ⟨s₁, s₂, s₃⟩
  rcases t with ⟨t₁, t₂, t₃⟩
  injection hst with h₁ h₂₃
  injection h₂₃ with h₂ h₃
  subst_vars
  rfl

omit [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq U] [DecidableEq V] [DecidableEq W] in
/-- Swapping the last two modes is injective. -/
theorem permuteACBTerm_injective :
    Function.Injective (permuteACBTerm (U := U) (V := V) (W := W)) := by
  intro s t hst
  rcases s with ⟨s₁, s₂, s₃⟩
  rcases t with ⟨t₁, t₂, t₃⟩
  injection hst with h₁ h₂₃
  injection h₂₃ with h₂ h₃
  subst_vars
  rfl

omit [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq U] [DecidableEq V] [DecidableEq W] in
/-- Reversing all three modes is injective. -/
theorem permuteCBATerm_injective :
    Function.Injective (permuteCBATerm (U := U) (V := V) (W := W)) := by
  intro s t hst
  rcases s with ⟨s₁, s₂, s₃⟩
  rcases t with ⟨t₁, t₂, t₃⟩
  injection hst with h₁ h₂₃
  injection h₂₃ with h₂ h₃
  subst_vars
  rfl

omit [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq U] [DecidableEq V] [DecidableEq W] in
/-- Swapping the first two modes is injective. -/
theorem permuteBACTerm_injective :
    Function.Injective (permuteBACTerm (U := U) (V := V) (W := W)) := by
  intro s t hst
  rcases s with ⟨s₁, s₂, s₃⟩
  rcases t with ⟨t₁, t₂, t₃⟩
  injection hst with h₁ h₂₃
  injection h₂₃ with h₂ h₃
  subst_vars
  rfl

/-- The three-point support of a Split has zero tensor evaluation. -/
theorem GeneratedFirstSplit.support_evaluation
    {source outputLeft outputRight : Carrier U V W} {D E : State U V W}
    (h : GeneratedFirstSplit source outputLeft outputRight D E) :
    stateEvaluation (D ∆ E) = 0 := by
  rw [BilinearComplexity.BinaryAmbientMoveSupport.GeneratedFirstSplit.symmDiff_eq h]
  have hlns := split_outputLeft_ne_source h
  have hrns := split_outputRight_ne_source h
  rcases h with ⟨_, hlr, _, _, hfirst, hls, hrs, hlt, hrt, _⟩
  simp only [stateEvaluation]
  simp [tensorEvaluation, hlns.symm, hrns.symm, hlr]
  rw [hfirst, hls, hrs, hlt, hrt, TensorProduct.add_tmul]
  exact BinaryCircuit.add_self_eq_zero
    (V := U ⊗[F2] (V ⊗[F2] W)) _

/-- The three-point support of a directed Reduction has zero tensor
evaluation. -/
theorem DirectedNarrowPairReduction.support_evaluation
    {sourceLeft sourceRight target : Carrier U V W} {D E : State U V W}
    (h : DirectedNarrowPairReduction sourceLeft sourceRight target D E) :
    stateEvaluation (D ∆ E) = 0 := by
  rw [BilinearComplexity.BinaryAmbientMoveSupport.DirectedNarrowPairReduction.symmDiff_eq h]
  have htleft := reduction_target_ne_sourceLeft h
  have htright := reduction_target_ne_sourceRight h
  rcases h with ⟨_, _, hlr, _, hsecond, hthird, hfirst,
    htargetSecond, htargetThird, _⟩
  simp only [stateEvaluation]
  simp [tensorEvaluation, hlr, htleft.symm, htright.symm]
  rw [hsecond, hthird, hfirst, htargetSecond, htargetThird,
    TensorProduct.add_tmul]
  let x := sourceLeft.1.1 ⊗ₜ[F2]
    (sourceLeft.2.1.1 ⊗ₜ[F2] sourceLeft.2.2.1)
  let y := sourceRight.1.1 ⊗ₜ[F2]
    (sourceLeft.2.1.1 ⊗ₜ[F2] sourceLeft.2.2.1)
  calc
    x + (y + (x + y)) = (x + x) + (y + y) := by abel
    _ = 0 := by
      rw [BinaryCircuit.add_self_eq_zero, BinaryCircuit.add_self_eq_zero,
        zero_add]

/-- The four-point support of a Flip has zero tensor evaluation. -/
theorem SourceThirdFlip.support_evaluation
    {sourceLeft sourceRight targetLeft targetRight : Carrier U V W}
    {D E : State U V W}
    (h : SourceThirdFlip sourceLeft sourceRight targetLeft targetRight D E) :
    stateEvaluation (D ∆ E) = 0 := by
  rw [BilinearComplexity.BinaryAmbientMoveSupport.SourceThirdFlip.symmDiff_eq h]
  have htlasl := flip_targetLeft_ne_sourceLeft h
  have htlasr := flip_targetLeft_ne_sourceRight h
  have htrasl := flip_targetRight_ne_sourceLeft h
  have htrasr := flip_targetRight_ne_sourceRight h
  rcases h with ⟨_, _, hsources, _, _, htargets, hthird, htlf, htls,
    htlt, htrf, htrs, htrt, _⟩
  simp only [stateEvaluation]
  simp [tensorEvaluation, hsources, htargets,
    htlasl.symm, htlasr.symm, htrasl.symm, htrasr.symm]
  rw [hthird, htlf, htls, htlt, htrf, htrs, htrt,
    ZModModule.sub_eq_add, TensorProduct.add_tmul,
    TensorProduct.add_tmul, TensorProduct.tmul_add]
  let x := sourceLeft.1.1 ⊗ₜ[F2]
    (sourceLeft.2.1.1 ⊗ₜ[F2] sourceLeft.2.2.1)
  let y := sourceRight.1.1 ⊗ₜ[F2]
    (sourceRight.2.1.1 ⊗ₜ[F2] sourceLeft.2.2.1)
  let z := sourceRight.1.1 ⊗ₜ[F2]
    (sourceLeft.2.1.1 ⊗ₜ[F2] sourceLeft.2.2.1)
  calc
    x + (y + ((x + z) + (y + z))) =
        (x + x) + (y + y) + (z + z) := by abel
    _ = 0 := by
      simp only [BinaryCircuit.add_self_eq_zero]

/-- Every ordered intrinsic move has zero tensor evaluation on its support. -/
theorem Move.support_evaluation {D E : State U V W} (h : Move D E) :
    stateEvaluation (D ∆ E) = 0 := by
  cases h with
  | generatedFirstSplit hsplit =>
      exact GeneratedFirstSplit.support_evaluation hsplit
  | sourceThirdFlip hflip =>
      exact SourceThirdFlip.support_evaluation hflip
  | directedNarrowPairReduction hreduction =>
      exact DirectedNarrowPairReduction.support_evaluation hreduction

private theorem stateEvaluation_image_eq_map
    {A B C X Y Z : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module F2 A] [Module F2 B] [Module F2 C]
    [Module F2 X] [Module F2 Y] [Module F2 Z]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (p : Carrier A B C → Carrier X Y Z) (hp : Function.Injective p)
    (f : A ⊗[F2] (B ⊗[F2] C) →ₗ[F2] X ⊗[F2] (Y ⊗[F2] Z))
    (hf : ∀ t, tensorEvaluation (p t) = f (tensorEvaluation t))
    (S : State A B C) :
    stateEvaluation (S.image p) = f (stateEvaluation S) := by
  rw [stateEvaluation, Finset.sum_image hp.injOn, stateEvaluation, map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  exact hf t

private def swapFirstTwo
    {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module F2 A] [Module F2 B] [Module F2 C] :
    A ⊗[F2] (B ⊗[F2] C) →ₗ[F2] B ⊗[F2] (A ⊗[F2] C) :=
  (TensorProduct.assoc F2 B A C).toLinearMap.comp
    ((TensorProduct.map (TensorProduct.comm F2 A B).toLinearMap LinearMap.id).comp
      (TensorProduct.assoc F2 A B C).symm.toLinearMap)

private def swapLastTwo
    {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module F2 A] [Module F2 B] [Module F2 C] :
    A ⊗[F2] (B ⊗[F2] C) →ₗ[F2] A ⊗[F2] (C ⊗[F2] B) :=
  TensorProduct.map LinearMap.id (TensorProduct.comm F2 B C).toLinearMap

private def bcaTensorMap :
    W ⊗[F2] (U ⊗[F2] V) →ₗ[F2] U ⊗[F2] (V ⊗[F2] W) :=
  (swapLastTwo (A := U) (B := W) (C := V)).comp
    (swapFirstTwo (A := W) (B := U) (C := V))

private def cabTensorMap :
    V ⊗[F2] (W ⊗[F2] U) →ₗ[F2] U ⊗[F2] (V ⊗[F2] W) :=
  (swapFirstTwo (A := V) (B := U) (C := W)).comp
    (swapLastTwo (A := V) (B := W) (C := U))

private def acbTensorMap :
    U ⊗[F2] (W ⊗[F2] V) →ₗ[F2] U ⊗[F2] (V ⊗[F2] W) :=
  swapLastTwo

private def cbaTensorMap :
    W ⊗[F2] (V ⊗[F2] U) →ₗ[F2] U ⊗[F2] (V ⊗[F2] W) :=
  (swapLastTwo (A := U) (B := W) (C := V)).comp
    ((swapFirstTwo (A := W) (B := U) (C := V)).comp
      (swapLastTwo (A := W) (B := V) (C := U)))

private def bacTensorMap :
    V ⊗[F2] (U ⊗[F2] W) →ₗ[F2] U ⊗[F2] (V ⊗[F2] W) :=
  swapFirstTwo

private theorem stateEvaluation_permuteBCA (S : State W U V) :
    stateEvaluation (permuteBCAState S) = bcaTensorMap (stateEvaluation S) := by
  apply stateEvaluation_image_eq_map permuteBCATerm
    permuteBCATerm_injective bcaTensorMap
  intro t
  rfl

private theorem stateEvaluation_permuteCAB (S : State V W U) :
    stateEvaluation (permuteCABState S) = cabTensorMap (stateEvaluation S) := by
  apply stateEvaluation_image_eq_map permuteCABTerm
    permuteCABTerm_injective cabTensorMap
  intro t
  rfl

private theorem stateEvaluation_permuteACB (S : State U W V) :
    stateEvaluation (permuteACBState S) = acbTensorMap (stateEvaluation S) := by
  apply stateEvaluation_image_eq_map permuteACBTerm
    permuteACBTerm_injective acbTensorMap
  intro t
  rfl

private theorem stateEvaluation_permuteCBA (S : State W V U) :
    stateEvaluation (permuteCBAState S) = cbaTensorMap (stateEvaluation S) := by
  apply stateEvaluation_image_eq_map permuteCBATerm
    permuteCBATerm_injective cbaTensorMap
  intro t
  rfl

private theorem stateEvaluation_permuteBAC (S : State V U W) :
    stateEvaluation (permuteBACState S) = bacTensorMap (stateEvaluation S) := by
  apply stateEvaluation_image_eq_map permuteBACTerm
    permuteBACTerm_injective bacTensorMap
  intro t
  rfl

private theorem stateEvaluation_symmDiff
    {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module F2 A] [Module F2 B] [Module F2 C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (D E : State A B C) :
    stateEvaluation (D ∆ E) = stateEvaluation D + stateEvaluation E := by
  simpa only [stateEvaluation, BinaryCircuit.evaluation,
    BinaryCircuit.toggle] using
    (BinaryCircuit.evaluation_symmDiff
      (value := tensorEvaluation (U := A) (V := B) (W := C)) D E)

private theorem stateEvaluation_eq_of_move_support_evaluation
    {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module F2 A] [Module F2 B] [Module F2 C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    {D E : State A B C} (hz : stateEvaluation (D ∆ E) = 0) :
    stateEvaluation D = stateEvaluation E := by
  rw [stateEvaluation_symmDiff] at hz
  calc
    stateEvaluation D = stateEvaluation D + 0 := (add_zero _).symm
    _ = stateEvaluation D + (stateEvaluation D + stateEvaluation E) := by rw [hz]
    _ = (stateEvaluation D + stateEvaluation D) + stateEvaluation E :=
      (add_assoc _ _ _).symm
    _ = stateEvaluation E := by
      rw [BinaryCircuit.add_self_eq_zero, zero_add]

/-- Every intrinsic move in any mode ordering has zero tensor evaluation on
its symmetric-difference support. -/
theorem AllModeMove.support_evaluation {D E : State U V W}
    (h : AllModeMove D E) : stateEvaluation (D ∆ E) = 0 := by
  rw [stateEvaluation_symmDiff]
  cases h with
  | abc hmove =>
      have hz := Move.support_evaluation hmove
      rw [stateEvaluation_symmDiff] at hz
      exact hz
  | bca hmove hD hE =>
      rw [hD, hE, stateEvaluation_permuteBCA, stateEvaluation_permuteBCA]
      have heq := stateEvaluation_eq_of_move_support_evaluation
        (Move.support_evaluation hmove)
      rw [heq, BinaryCircuit.add_self_eq_zero]
  | cab hmove hD hE =>
      rw [hD, hE, stateEvaluation_permuteCAB, stateEvaluation_permuteCAB]
      have heq := stateEvaluation_eq_of_move_support_evaluation
        (Move.support_evaluation hmove)
      rw [heq, BinaryCircuit.add_self_eq_zero]
  | acb hmove hD hE =>
      rw [hD, hE, stateEvaluation_permuteACB, stateEvaluation_permuteACB]
      have heq := stateEvaluation_eq_of_move_support_evaluation
        (Move.support_evaluation hmove)
      rw [heq, BinaryCircuit.add_self_eq_zero]
  | cba hmove hD hE =>
      rw [hD, hE, stateEvaluation_permuteCBA, stateEvaluation_permuteCBA]
      have heq := stateEvaluation_eq_of_move_support_evaluation
        (Move.support_evaluation hmove)
      rw [heq, BinaryCircuit.add_self_eq_zero]
  | bac hmove hD hE =>
      rw [hD, hE, stateEvaluation_permuteBAC, stateEvaluation_permuteBAC]
      have heq := stateEvaluation_eq_of_move_support_evaluation
        (Move.support_evaluation hmove)
      rw [heq, BinaryCircuit.add_self_eq_zero]

omit [Module F2 U] [Module F2 W] in
/-- Every ordered intrinsic move has symmetric-difference support of size
exactly three for Split/Reduction or exactly four for Flip. -/
theorem Move.support_card {D E : State U V W} (h : Move D E) :
    (D ∆ E).card = 3 ∨ (D ∆ E).card = 4 := by
  cases h with
  | generatedFirstSplit hsplit =>
      left
      rw [BilinearComplexity.BinaryAmbientMoveSupport.GeneratedFirstSplit.symmDiff_eq hsplit]
      have hleft := split_outputLeft_ne_source hsplit
      have hright := split_outputRight_ne_source hsplit
      apply Finset.card_eq_three.mpr
      exact ⟨_, _, _, hleft.symm, hright.symm, hsplit.2.1, rfl⟩
  | sourceThirdFlip hflip =>
      right
      rw [BilinearComplexity.BinaryAmbientMoveSupport.SourceThirdFlip.symmDiff_eq hflip]
      have htlasl := flip_targetLeft_ne_sourceLeft hflip
      have htlasr := flip_targetLeft_ne_sourceRight hflip
      have htrasl := flip_targetRight_ne_sourceLeft hflip
      have htrasr := flip_targetRight_ne_sourceRight hflip
      apply Finset.card_eq_four.mpr
      exact ⟨_, _, _, _, hflip.2.2.1, htlasl.symm, htrasl.symm,
        htlasr.symm, htrasr.symm, hflip.2.2.2.2.2.1, rfl⟩
  | directedNarrowPairReduction hreduction =>
      left
      rw [BilinearComplexity.BinaryAmbientMoveSupport.DirectedNarrowPairReduction.symmDiff_eq hreduction]
      have htleft := reduction_target_ne_sourceLeft hreduction
      have htright := reduction_target_ne_sourceRight hreduction
      apply Finset.card_eq_three.mpr
      exact ⟨_, _, _, hreduction.2.2.1, htleft.symm, htright.symm, rfl⟩

private theorem image_symmDiff_card
    {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (hf : Function.Injective f) (D E : Finset X) :
    (D.image f ∆ E.image f).card = (D ∆ E).card := by
  rw [← Finset.image_symmDiff D E hf,
    Finset.card_image_of_injective (D ∆ E) hf]

/-- Every intrinsic move in any of the six mode orientations has genuine
symmetric-difference support of size exactly three or exactly four. -/
theorem AllModeMove.support_card {D E : State U V W} (h : AllModeMove D E) :
    (D ∆ E).card = 3 ∨ (D ∆ E).card = 4 := by
  cases h with
  | abc hmove => exact BilinearComplexity.BinaryAmbientMoveSupport.Move.support_card hmove
  | bca hmove hD hE =>
      rw [hD, hE]
      simp only [permuteBCAState]
      rw [image_symmDiff_card permuteBCATerm permuteBCATerm_injective]
      exact BilinearComplexity.BinaryAmbientMoveSupport.Move.support_card hmove
  | cab hmove hD hE =>
      rw [hD, hE]
      simp only [permuteCABState]
      rw [image_symmDiff_card permuteCABTerm permuteCABTerm_injective]
      exact BilinearComplexity.BinaryAmbientMoveSupport.Move.support_card hmove
  | acb hmove hD hE =>
      rw [hD, hE]
      simp only [permuteACBState]
      rw [image_symmDiff_card permuteACBTerm permuteACBTerm_injective]
      exact BilinearComplexity.BinaryAmbientMoveSupport.Move.support_card hmove
  | cba hmove hD hE =>
      rw [hD, hE]
      simp only [permuteCBAState]
      rw [image_symmDiff_card permuteCBATerm permuteCBATerm_injective]
      exact BilinearComplexity.BinaryAmbientMoveSupport.Move.support_card hmove
  | bac hmove hD hE =>
      rw [hD, hE]
      simp only [permuteBACState]
      rw [image_symmDiff_card permuteBACTerm permuteBACTerm_injective]
      exact BilinearComplexity.BinaryAmbientMoveSupport.Move.support_card hmove

omit [Module F2 U] [Module F2 W] in
/-- An ordered move with three support points is precisely a Split or a
directed Reduction, with the displayed exact support. -/
theorem Move.support_three_factor_line {D E : State U V W} (h : Move D E)
    (hcard : (D ∆ E).card = 3) :
    (∃ source outputLeft outputRight,
        GeneratedFirstSplit source outputLeft outputRight D E ∧
          D ∆ E = {source, outputLeft, outputRight}) ∨
      ∃ sourceLeft sourceRight target,
        DirectedNarrowPairReduction sourceLeft sourceRight target D E ∧
          D ∆ E = {sourceLeft, sourceRight, target} := by
  cases h with
  | generatedFirstSplit hsplit =>
      left
      exact ⟨_, _, _, hsplit,
        GeneratedFirstSplit.symmDiff_eq hsplit⟩
  | sourceThirdFlip hflip =>
      have hsupport := SourceThirdFlip.symmDiff_eq hflip
      have hfour : (D ∆ E).card = 4 := by
        rw [hsupport]
        apply Finset.card_eq_four.mpr
        have htlasl := flip_targetLeft_ne_sourceLeft hflip
        have htlasr := flip_targetLeft_ne_sourceRight hflip
        have htrasl := flip_targetRight_ne_sourceLeft hflip
        have htrasr := flip_targetRight_ne_sourceRight hflip
        exact ⟨_, _, _, _, hflip.2.2.1, htlasl.symm, htrasl.symm,
          htlasr.symm, htrasr.symm, hflip.2.2.2.2.2.1, rfl⟩
      omega
  | directedNarrowPairReduction hreduction =>
      right
      exact ⟨_, _, _, hreduction,
        DirectedNarrowPairReduction.symmDiff_eq hreduction⟩

private theorem factor_mem_span_erase_of_three
    {α : Type*} {M : Type*} [DecidableEq α]
    [AddCommGroup M] [Module F2 M]
    (f : α → M) {S : Finset α} {a b c t : α}
    (hS : S = {a, b, c}) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ht : t ∈ S)
    (hgeometry : f a = f b + f c ∨ (f a = f b ∧ f a = f c)) :
    f t ∈ Submodule.span F2 (f '' (S.erase t : Set α)) := by
  have ha : a ∈ S := by simp [hS]
  have hb : b ∈ S := by simp [hS]
  have hc : c ∈ S := by simp [hS]
  have hcases : t = a ∨ t = b ∨ t = c := by simpa [hS] using ht
  rcases hcases with htA | htB | htC
  · subst t
    rcases hgeometry with hline | hcommon
    · rw [hline]
      apply Submodule.add_mem
      · exact Submodule.subset_span ⟨b,
          Finset.mem_erase.mpr ⟨hab.symm, hb⟩, rfl⟩
      · exact Submodule.subset_span ⟨c,
          Finset.mem_erase.mpr ⟨hac.symm, hc⟩, rfl⟩
    · rw [hcommon.1]
      exact Submodule.subset_span ⟨b,
        Finset.mem_erase.mpr ⟨hab.symm, hb⟩, rfl⟩
  · subst t
    rcases hgeometry with hline | hcommon
    · have hline' : f b = f a + f c := by
        calc
          f b = (f b + f c) + f c := by
            rw [add_assoc, BinaryCircuit.add_self_eq_zero, add_zero]
          _ = f a + f c := by rw [← hline]
      rw [hline']
      apply Submodule.add_mem
      · exact Submodule.subset_span ⟨a,
          Finset.mem_erase.mpr ⟨hab, ha⟩, rfl⟩
      · exact Submodule.subset_span ⟨c,
          Finset.mem_erase.mpr ⟨hbc.symm, hc⟩, rfl⟩
    · rw [← hcommon.1]
      exact Submodule.subset_span ⟨a,
        Finset.mem_erase.mpr ⟨hab, ha⟩, rfl⟩
  · subst t
    rcases hgeometry with hline | hcommon
    · have hline' : f c = f a + f b := by
        calc
          f c = (f b + f b) + f c := by
            rw [BinaryCircuit.add_self_eq_zero, zero_add]
          _ = (f b + f c) + f b := by abel
          _ = f a + f b := by rw [← hline]
      rw [hline']
      apply Submodule.add_mem
      · exact Submodule.subset_span ⟨a,
          Finset.mem_erase.mpr ⟨hac, ha⟩, rfl⟩
      · exact Submodule.subset_span ⟨b,
          Finset.mem_erase.mpr ⟨hbc, hb⟩, rfl⟩
    · rw [← hcommon.2]
      exact Submodule.subset_span ⟨a,
        Finset.mem_erase.mpr ⟨hac, ha⟩, rfl⟩

private theorem factors_mem_spans_erase_of_three
    {S : State U V W} {a b c t : Carrier U V W}
    (hS : S = {a, b, c}) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ht : t ∈ S)
    (hfirst : a.1.1 = b.1.1 + c.1.1 ∨
      (a.1.1 = b.1.1 ∧ a.1.1 = c.1.1))
    (hsecond : a.2.1.1 = b.2.1.1 + c.2.1.1 ∨
      (a.2.1.1 = b.2.1.1 ∧ a.2.1.1 = c.2.1.1))
    (hthird : a.2.2.1 = b.2.2.1 + c.2.2.1 ∨
      (a.2.2.1 = b.2.2.1 ∧ a.2.2.1 = c.2.2.1)) :
    t.1.1 ∈ firstSpan (S.erase t) ∧
      t.2.1.1 ∈ secondSpan (S.erase t) ∧
      t.2.2.1 ∈ thirdSpan (S.erase t) := by
  refine ⟨?_, ?_, ?_⟩
  · exact factor_mem_span_erase_of_three (fun q : Carrier U V W => q.1.1)
      hS hab hac hbc ht hfirst
  · exact factor_mem_span_erase_of_three (fun q : Carrier U V W => q.2.1.1)
      hS hab hac hbc ht hsecond
  · exact factor_mem_span_erase_of_three (fun q : Carrier U V W => q.2.2.1)
      hS hab hac hbc ht hthird

private theorem GeneratedFirstSplit.support_three_factors_mem_spans
    {source outputLeft outputRight : Carrier U V W} {D E : State U V W}
    (h : GeneratedFirstSplit source outputLeft outputRight D E)
    {t : Carrier U V W} (ht : t ∈ D ∆ E) :
    t.1.1 ∈ firstSpan ((D ∆ E).erase t) ∧
      t.2.1.1 ∈ secondSpan ((D ∆ E).erase t) ∧
      t.2.2.1 ∈ thirdSpan ((D ∆ E).erase t) := by
  have hsupport := GeneratedFirstSplit.symmDiff_eq h
  have hlns := (split_outputLeft_ne_source h).symm
  have hrns := (split_outputRight_ne_source h).symm
  rcases h with ⟨_, hlr, _, _, hfirst, hls, hrs, hlt, hrt, _⟩
  apply factors_mem_spans_erase_of_three hsupport hlns hrns hlr ht
  · exact Or.inl hfirst
  · exact Or.inr ⟨hls.symm, hrs.symm⟩
  · exact Or.inr ⟨hlt.symm, hrt.symm⟩

private theorem DirectedNarrowPairReduction.support_three_factors_mem_spans
    {sourceLeft sourceRight target : Carrier U V W} {D E : State U V W}
    (h : DirectedNarrowPairReduction sourceLeft sourceRight target D E)
    {t : Carrier U V W} (ht : t ∈ D ∆ E) :
    t.1.1 ∈ firstSpan ((D ∆ E).erase t) ∧
      t.2.1.1 ∈ secondSpan ((D ∆ E).erase t) ∧
      t.2.2.1 ∈ thirdSpan ((D ∆ E).erase t) := by
  have hsupport₀ := DirectedNarrowPairReduction.symmDiff_eq h
  have hsupport : D ∆ E = {target, sourceLeft, sourceRight} := by
    rw [hsupport₀]
    ext q
    simp only [Finset.mem_insert, Finset.mem_singleton]
    aesop
  have htleft := reduction_target_ne_sourceLeft h
  have htright := reduction_target_ne_sourceRight h
  rcases h with ⟨_, _, hlr, _, hsecond, hthird, hfirst,
    htargetSecond, htargetThird, _⟩
  apply factors_mem_spans_erase_of_three hsupport htleft htright hlr ht
  · exact Or.inl hfirst
  · exact Or.inr ⟨htargetSecond, htargetSecond.trans hsecond.symm⟩
  · exact Or.inr ⟨htargetThird, htargetThird.trans hthird.symm⟩

/-- For every term of a three-point ordered support, each factor lies in the
corresponding factor span generated by the other two support terms. -/
theorem Move.support_three_factors_mem_spans {D E : State U V W}
    (h : Move D E) (hcard : (D ∆ E).card = 3)
    {t : Carrier U V W} (ht : t ∈ D ∆ E) :
    t.1.1 ∈ firstSpan ((D ∆ E).erase t) ∧
      t.2.1.1 ∈ secondSpan ((D ∆ E).erase t) ∧
      t.2.2.1 ∈ thirdSpan ((D ∆ E).erase t) := by
  rcases Move.support_three_factor_line h hcard with
    ⟨_, _, _, hsplit, _⟩ | ⟨_, _, _, hreduction, _⟩
  · exact GeneratedFirstSplit.support_three_factors_mem_spans hsplit ht
  · exact DirectedNarrowPairReduction.support_three_factors_mem_spans
      hreduction ht

omit [Module F2 U] [Module F2 W] in
/-- A four-point ordered move is precisely a Flip, with the displayed exact
support. -/
theorem Move.support_four_factor_flip {D E : State U V W} (h : Move D E)
    (hcard : (D ∆ E).card = 4) :
    ∃ sourceLeft sourceRight targetLeft targetRight,
      SourceThirdFlip sourceLeft sourceRight targetLeft targetRight D E ∧
        D ∆ E = {sourceLeft, sourceRight, targetLeft, targetRight} := by
  cases h with
  | generatedFirstSplit hsplit =>
      have hsupport := GeneratedFirstSplit.symmDiff_eq hsplit
      have hthree : (D ∆ E).card = 3 := by
        rw [hsupport]
        apply Finset.card_eq_three.mpr
        have hleft := split_outputLeft_ne_source hsplit
        have hright := split_outputRight_ne_source hsplit
        exact ⟨_, _, _, hleft.symm, hright.symm, hsplit.2.1, rfl⟩
      omega
  | sourceThirdFlip hflip =>
      exact ⟨_, _, _, _, hflip, SourceThirdFlip.symmDiff_eq hflip⟩
  | directedNarrowPairReduction hreduction =>
      have hsupport := DirectedNarrowPairReduction.symmDiff_eq hreduction
      have hthree : (D ∆ E).card = 3 := by
        rw [hsupport]
        apply Finset.card_eq_three.mpr
        have htleft := reduction_target_ne_sourceLeft hreduction
        have htright := reduction_target_ne_sourceRight hreduction
        exact ⟨_, _, _, hreduction.2.2.1, htleft.symm, htright.symm, rfl⟩
      omega

private theorem image_symmDiff_eq
    {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (hf : Function.Injective f) (D E : Finset X) :
    D.image f ∆ E.image f = (D ∆ E).image f :=
  (Finset.image_symmDiff D E hf).symm

/-- A three-point all-mode support is, in one of the six represented
orientations, the injective image of an intrinsic Split or directed Reduction.
The retained primitive witness exposes the varying factor and the two common
factor lines. -/
theorem AllModeMove.support_three_factor_line {D E : State U V W}
    (h : AllModeMove D E) (hcard : (D ∆ E).card = 3) :
    ((∃ s l r, GeneratedFirstSplit s l r D E ∧ D ∆ E = {s, l, r}) ∨
      ∃ l r t, DirectedNarrowPairReduction l r t D E ∧ D ∆ E = {l, r, t}) ∨
    (∃ D₀ E₀ : State W U V,
      ((∃ s l r, GeneratedFirstSplit s l r D₀ E₀ ∧ D₀ ∆ E₀ = {s, l, r}) ∨
        ∃ l r t, DirectedNarrowPairReduction l r t D₀ E₀ ∧ D₀ ∆ E₀ = {l, r, t}) ∧
      D ∆ E = Finset.image permuteBCATerm (D₀ ∆ E₀)) ∨
    (∃ D₀ E₀ : State V W U,
      ((∃ s l r, GeneratedFirstSplit s l r D₀ E₀ ∧ D₀ ∆ E₀ = {s, l, r}) ∨
        ∃ l r t, DirectedNarrowPairReduction l r t D₀ E₀ ∧ D₀ ∆ E₀ = {l, r, t}) ∧
      D ∆ E = Finset.image permuteCABTerm (D₀ ∆ E₀)) ∨
    (∃ D₀ E₀ : State U W V,
      ((∃ s l r, GeneratedFirstSplit s l r D₀ E₀ ∧ D₀ ∆ E₀ = {s, l, r}) ∨
        ∃ l r t, DirectedNarrowPairReduction l r t D₀ E₀ ∧ D₀ ∆ E₀ = {l, r, t}) ∧
      D ∆ E = Finset.image permuteACBTerm (D₀ ∆ E₀)) ∨
    (∃ D₀ E₀ : State W V U,
      ((∃ s l r, GeneratedFirstSplit s l r D₀ E₀ ∧ D₀ ∆ E₀ = {s, l, r}) ∨
        ∃ l r t, DirectedNarrowPairReduction l r t D₀ E₀ ∧ D₀ ∆ E₀ = {l, r, t}) ∧
      D ∆ E = Finset.image permuteCBATerm (D₀ ∆ E₀)) ∨
      ∃ D₀ E₀ : State V U W,
      ((∃ s l r, GeneratedFirstSplit s l r D₀ E₀ ∧ D₀ ∆ E₀ = {s, l, r}) ∨
        ∃ l r t, DirectedNarrowPairReduction l r t D₀ E₀ ∧ D₀ ∆ E₀ = {l, r, t}) ∧
      D ∆ E = Finset.image permuteBACTerm (D₀ ∆ E₀) := by
  cases h with
  | abc hmove =>
      left
      exact Move.support_three_factor_line hmove hcard
  | bca hmove hD hE =>
      right; left
      rw [hD, hE] at hcard ⊢
      simp only [permuteBCAState] at hcard ⊢
      rw [image_symmDiff_card permuteBCATerm permuteBCATerm_injective] at hcard
      exact ⟨_, _, Move.support_three_factor_line hmove hcard,
        image_symmDiff_eq permuteBCATerm permuteBCATerm_injective _ _⟩
  | cab hmove hD hE =>
      right; right; left
      rw [hD, hE] at hcard ⊢
      simp only [permuteCABState] at hcard ⊢
      rw [image_symmDiff_card permuteCABTerm permuteCABTerm_injective] at hcard
      exact ⟨_, _, Move.support_three_factor_line hmove hcard,
        image_symmDiff_eq permuteCABTerm permuteCABTerm_injective _ _⟩
  | acb hmove hD hE =>
      right; right; right; left
      rw [hD, hE] at hcard ⊢
      simp only [permuteACBState] at hcard ⊢
      rw [image_symmDiff_card permuteACBTerm permuteACBTerm_injective] at hcard
      exact ⟨_, _, Move.support_three_factor_line hmove hcard,
        image_symmDiff_eq permuteACBTerm permuteACBTerm_injective _ _⟩
  | cba hmove hD hE =>
      right; right; right; right; left
      rw [hD, hE] at hcard ⊢
      simp only [permuteCBAState] at hcard ⊢
      rw [image_symmDiff_card permuteCBATerm permuteCBATerm_injective] at hcard
      exact ⟨_, _, Move.support_three_factor_line hmove hcard,
        image_symmDiff_eq permuteCBATerm permuteCBATerm_injective _ _⟩
  | bac hmove hD hE =>
      right; right; right; right; right
      rw [hD, hE] at hcard ⊢
      simp only [permuteBACState] at hcard ⊢
      rw [image_symmDiff_card permuteBACTerm permuteBACTerm_injective] at hcard
      exact ⟨_, _, Move.support_three_factor_line hmove hcard,
        image_symmDiff_eq permuteBACTerm permuteBACTerm_injective _ _⟩

omit [Module F2 U] [Module F2 W] in
private theorem Move.support_three_geometry {D E : State U V W}
    (h : Move D E) (hcard : (D ∆ E).card = 3) :
    ∃ a b c : Carrier U V W,
      D ∆ E = {a, b, c} ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      (a.1.1 = b.1.1 + c.1.1 ∨
        (a.1.1 = b.1.1 ∧ a.1.1 = c.1.1)) ∧
      (a.2.1.1 = b.2.1.1 + c.2.1.1 ∨
        (a.2.1.1 = b.2.1.1 ∧ a.2.1.1 = c.2.1.1)) ∧
      (a.2.2.1 = b.2.2.1 + c.2.2.1 ∨
        (a.2.2.1 = b.2.2.1 ∧ a.2.2.1 = c.2.2.1)) := by
  rcases Move.support_three_factor_line h hcard with
    ⟨s, l, r, hs, hsupport⟩ | ⟨l, r, t, hr, hsupport₀⟩
  · refine ⟨s, l, r, hsupport, (split_outputLeft_ne_source hs).symm,
      (split_outputRight_ne_source hs).symm, hs.2.1, Or.inl hs.2.2.2.2.1,
      Or.inr ⟨hs.2.2.2.2.2.1.symm, hs.2.2.2.2.2.2.1.symm⟩,
      Or.inr ⟨hs.2.2.2.2.2.2.2.1.symm,
        hs.2.2.2.2.2.2.2.2.1.symm⟩⟩
  · have hsupport : D ∆ E = {t, l, r} := by
      rw [hsupport₀]
      ext q
      simp only [Finset.mem_insert, Finset.mem_singleton]
      aesop
    refine ⟨t, l, r, hsupport, reduction_target_ne_sourceLeft hr,
      reduction_target_ne_sourceRight hr, hr.2.2.1,
      Or.inl hr.2.2.2.2.2.2.1, ?_, ?_⟩
    · exact Or.inr ⟨hr.2.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.1.trans hr.2.2.2.2.1.symm⟩
    · exact Or.inr ⟨hr.2.2.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.2.1.trans hr.2.2.2.2.2.1.symm⟩

private theorem AllModeMove.support_three_geometry {D E : State U V W}
    (h : AllModeMove D E) (hcard : (D ∆ E).card = 3) :
    ∃ a b c : Carrier U V W,
      D ∆ E = {a, b, c} ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      (a.1.1 = b.1.1 + c.1.1 ∨
        (a.1.1 = b.1.1 ∧ a.1.1 = c.1.1)) ∧
      (a.2.1.1 = b.2.1.1 + c.2.1.1 ∨
        (a.2.1.1 = b.2.1.1 ∧ a.2.1.1 = c.2.1.1)) ∧
      (a.2.2.1 = b.2.2.1 + c.2.2.1 ∨
        (a.2.2.1 = b.2.2.1 ∧ a.2.2.1 = c.2.2.1)) := by
  cases h
  case abc hmove => exact Move.support_three_geometry hmove hcard
  case bca D₀ E₀ hmove hD hE =>
      have hc : (D₀ ∆ E₀).card = 3 := by
        rw [hD, hE] at hcard
        simp only [permuteBCAState] at hcard
        rwa [image_symmDiff_card permuteBCATerm permuteBCATerm_injective] at hcard
      rcases Move.support_three_geometry hmove hc with
        ⟨a, b, c, hS₀, hab, hac, hbc, hfirst, hsecond, hthird⟩
      have hS : D ∆ E = (D₀ ∆ E₀).image permuteBCATerm := by
        rw [hD, hE]
        exact image_symmDiff_eq permuteBCATerm permuteBCATerm_injective _ _
      refine ⟨permuteBCATerm a, permuteBCATerm b, permuteBCATerm c,
        ?_, permuteBCATerm_injective.ne hab, permuteBCATerm_injective.ne hac,
        permuteBCATerm_injective.ne hbc, ?_, ?_, ?_⟩
      · rw [hS, hS₀]; simp
      · simpa [permuteBCATerm] using hsecond
      · simpa [permuteBCATerm] using hthird
      · simpa [permuteBCATerm] using hfirst
  case cab D₀ E₀ hmove hD hE =>
      have hc : (D₀ ∆ E₀).card = 3 := by
        rw [hD, hE] at hcard
        simp only [permuteCABState] at hcard
        rwa [image_symmDiff_card permuteCABTerm permuteCABTerm_injective] at hcard
      rcases Move.support_three_geometry hmove hc with
        ⟨a, b, c, hS₀, hab, hac, hbc, hfirst, hsecond, hthird⟩
      have hS : D ∆ E = (D₀ ∆ E₀).image permuteCABTerm := by
        rw [hD, hE]
        exact image_symmDiff_eq permuteCABTerm permuteCABTerm_injective _ _
      refine ⟨permuteCABTerm a, permuteCABTerm b, permuteCABTerm c,
        ?_, permuteCABTerm_injective.ne hab, permuteCABTerm_injective.ne hac,
        permuteCABTerm_injective.ne hbc, ?_, ?_, ?_⟩
      · rw [hS, hS₀]; simp
      · simpa [permuteCABTerm] using hthird
      · simpa [permuteCABTerm] using hfirst
      · simpa [permuteCABTerm] using hsecond
  case acb D₀ E₀ hmove hD hE =>
      have hc : (D₀ ∆ E₀).card = 3 := by
        rw [hD, hE] at hcard
        simp only [permuteACBState] at hcard
        rwa [image_symmDiff_card permuteACBTerm permuteACBTerm_injective] at hcard
      rcases Move.support_three_geometry hmove hc with
        ⟨a, b, c, hS₀, hab, hac, hbc, hfirst, hsecond, hthird⟩
      have hS : D ∆ E = (D₀ ∆ E₀).image permuteACBTerm := by
        rw [hD, hE]
        exact image_symmDiff_eq permuteACBTerm permuteACBTerm_injective _ _
      refine ⟨permuteACBTerm a, permuteACBTerm b, permuteACBTerm c,
        ?_, permuteACBTerm_injective.ne hab, permuteACBTerm_injective.ne hac,
        permuteACBTerm_injective.ne hbc, ?_, ?_, ?_⟩
      · rw [hS, hS₀]; simp
      · simpa [permuteACBTerm] using hfirst
      · simpa [permuteACBTerm] using hthird
      · simpa [permuteACBTerm] using hsecond
  case cba D₀ E₀ hmove hD hE =>
      have hc : (D₀ ∆ E₀).card = 3 := by
        rw [hD, hE] at hcard
        simp only [permuteCBAState] at hcard
        rwa [image_symmDiff_card permuteCBATerm permuteCBATerm_injective] at hcard
      rcases Move.support_three_geometry hmove hc with
        ⟨a, b, c, hS₀, hab, hac, hbc, hfirst, hsecond, hthird⟩
      have hS : D ∆ E = (D₀ ∆ E₀).image permuteCBATerm := by
        rw [hD, hE]
        exact image_symmDiff_eq permuteCBATerm permuteCBATerm_injective _ _
      refine ⟨permuteCBATerm a, permuteCBATerm b, permuteCBATerm c,
        ?_, permuteCBATerm_injective.ne hab, permuteCBATerm_injective.ne hac,
        permuteCBATerm_injective.ne hbc, ?_, ?_, ?_⟩
      · rw [hS, hS₀]; simp
      · simpa [permuteCBATerm] using hthird
      · simpa [permuteCBATerm] using hsecond
      · simpa [permuteCBATerm] using hfirst
  case bac D₀ E₀ hmove hD hE =>
      have hc : (D₀ ∆ E₀).card = 3 := by
        rw [hD, hE] at hcard
        simp only [permuteBACState] at hcard
        rwa [image_symmDiff_card permuteBACTerm permuteBACTerm_injective] at hcard
      rcases Move.support_three_geometry hmove hc with
        ⟨a, b, c, hS₀, hab, hac, hbc, hfirst, hsecond, hthird⟩
      have hS : D ∆ E = (D₀ ∆ E₀).image permuteBACTerm := by
        rw [hD, hE]
        exact image_symmDiff_eq permuteBACTerm permuteBACTerm_injective _ _
      refine ⟨permuteBACTerm a, permuteBACTerm b, permuteBACTerm c,
        ?_, permuteBACTerm_injective.ne hab, permuteBACTerm_injective.ne hac,
        permuteBACTerm_injective.ne hbc, ?_, ?_, ?_⟩
      · rw [hS, hS₀]; simp
      · simpa [permuteBACTerm] using hsecond
      · simpa [permuteBACTerm] using hfirst
      · simpa [permuteBACTerm] using hthird

/-- For every term of a three-point all-mode support, each factor lies in the
corresponding factor span generated by the other two support terms. -/
theorem AllModeMove.support_three_factors_mem_spans {D E : State U V W}
    (h : AllModeMove D E) (hcard : (D ∆ E).card = 3)
    {t : Carrier U V W} (ht : t ∈ D ∆ E) :
    t.1.1 ∈ firstSpan ((D ∆ E).erase t) ∧
      t.2.1.1 ∈ secondSpan ((D ∆ E).erase t) ∧
      t.2.2.1 ∈ thirdSpan ((D ∆ E).erase t) := by
  rcases AllModeMove.support_three_geometry h hcard with
    ⟨a, b, c, hsupport, hab, hac, hbc, hfirst, hsecond, hthird⟩
  exact factors_mem_spans_erase_of_three hsupport hab hac hbc ht
    hfirst hsecond hthird

/-- A four-point all-mode support is, in one of the six represented
orientations, the injective image of the four witnesses of an intrinsic Flip.
The retained Flip witness exposes all factor equations. -/
theorem AllModeMove.support_four_factor_flip {D E : State U V W}
    (h : AllModeMove D E) (hcard : (D ∆ E).card = 4) :
    (∃ sl sr tl tr, SourceThirdFlip sl sr tl tr D E ∧
        D ∆ E = {sl, sr, tl, tr}) ∨
    (∃ (D₀ E₀ : State W U V) (sl sr tl tr : Carrier W U V),
        SourceThirdFlip sl sr tl tr D₀ E₀ ∧
          D ∆ E = Finset.image permuteBCATerm {sl, sr, tl, tr}) ∨
    (∃ (D₀ E₀ : State V W U) (sl sr tl tr : Carrier V W U),
        SourceThirdFlip sl sr tl tr D₀ E₀ ∧
          D ∆ E = Finset.image permuteCABTerm {sl, sr, tl, tr}) ∨
    (∃ (D₀ E₀ : State U W V) (sl sr tl tr : Carrier U W V),
        SourceThirdFlip sl sr tl tr D₀ E₀ ∧
          D ∆ E = Finset.image permuteACBTerm {sl, sr, tl, tr}) ∨
    (∃ (D₀ E₀ : State W V U) (sl sr tl tr : Carrier W V U),
        SourceThirdFlip sl sr tl tr D₀ E₀ ∧
          D ∆ E = Finset.image permuteCBATerm {sl, sr, tl, tr}) ∨
      ∃ (D₀ E₀ : State V U W) (sl sr tl tr : Carrier V U W),
        SourceThirdFlip sl sr tl tr D₀ E₀ ∧
          D ∆ E = Finset.image permuteBACTerm {sl, sr, tl, tr} := by
  cases h with
  | abc hmove =>
      left
      exact Move.support_four_factor_flip hmove hcard
  | bca hmove hD hE =>
      right; left
      rw [hD, hE] at hcard ⊢
      simp only [permuteBCAState] at hcard ⊢
      rw [image_symmDiff_card permuteBCATerm permuteBCATerm_injective] at hcard
      rcases Move.support_four_factor_flip hmove hcard with ⟨sl, sr, tl, tr, hflip, hs⟩
      exact ⟨_, _, sl, sr, tl, tr, hflip,
        (image_symmDiff_eq permuteBCATerm permuteBCATerm_injective _ _).trans
          (congrArg (Finset.image permuteBCATerm) hs)⟩
  | cab hmove hD hE =>
      right; right; left
      rw [hD, hE] at hcard ⊢
      simp only [permuteCABState] at hcard ⊢
      rw [image_symmDiff_card permuteCABTerm permuteCABTerm_injective] at hcard
      rcases Move.support_four_factor_flip hmove hcard with ⟨sl, sr, tl, tr, hflip, hs⟩
      exact ⟨_, _, sl, sr, tl, tr, hflip,
        (image_symmDiff_eq permuteCABTerm permuteCABTerm_injective _ _).trans
          (congrArg (Finset.image permuteCABTerm) hs)⟩
  | acb hmove hD hE =>
      right; right; right; left
      rw [hD, hE] at hcard ⊢
      simp only [permuteACBState] at hcard ⊢
      rw [image_symmDiff_card permuteACBTerm permuteACBTerm_injective] at hcard
      rcases Move.support_four_factor_flip hmove hcard with ⟨sl, sr, tl, tr, hflip, hs⟩
      exact ⟨_, _, sl, sr, tl, tr, hflip,
        (image_symmDiff_eq permuteACBTerm permuteACBTerm_injective _ _).trans
          (congrArg (Finset.image permuteACBTerm) hs)⟩
  | cba hmove hD hE =>
      right; right; right; right; left
      rw [hD, hE] at hcard ⊢
      simp only [permuteCBAState] at hcard ⊢
      rw [image_symmDiff_card permuteCBATerm permuteCBATerm_injective] at hcard
      rcases Move.support_four_factor_flip hmove hcard with ⟨sl, sr, tl, tr, hflip, hs⟩
      exact ⟨_, _, sl, sr, tl, tr, hflip,
        (image_symmDiff_eq permuteCBATerm permuteCBATerm_injective _ _).trans
          (congrArg (Finset.image permuteCBATerm) hs)⟩
  | bac hmove hD hE =>
      right; right; right; right; right
      rw [hD, hE] at hcard ⊢
      simp only [permuteBACState] at hcard ⊢
      rw [image_symmDiff_card permuteBACTerm permuteBACTerm_injective] at hcard
      rcases Move.support_four_factor_flip hmove hcard with ⟨sl, sr, tl, tr, hflip, hs⟩
      exact ⟨_, _, sl, sr, tl, tr, hflip,
        (image_symmDiff_eq permuteBACTerm permuteBACTerm_injective _ _).trans
          (congrArg (Finset.image permuteBACTerm) hs)⟩

omit [Module F2 U] [Module F2 V] [Module F2 W] in
/-- Outside the symmetric difference of two finite states, their occupancy is
identical. -/
theorem AllModeMove.mem_iff_mem_of_not_mem_support {D E : State U V W}
    {t : Carrier U V W} (ht : t ∉ D ∆ E) :
    (t ∈ D ↔ t ∈ E) := by
  rw [Finset.mem_symmDiff, not_or, not_and_or, not_and_or] at ht
  tauto

omit [Module F2 U] [Module F2 V] [Module F2 W] in
/-- Toggling one finite state by its symmetric difference with another gives
the other state. -/
theorem AllModeMove.target_eq_toggle_support {D E : State U V W} :
    E = D ∆ (D ∆ E) := by
  ext t
  simp only [Finset.mem_symmDiff]
  tauto

/-! Ground checks for support size and nonvacuity. -/

open NormalizedBinaryCarrier
open NormalizedBinaryReplay221

example : BinaryAmbientMoves.AllModeMove
    (U := CoordinateVector 2) (V := CoordinateVector 2)
    (W := CoordinateVector 1) S0 S1 :=
  .abc (.generatedFirstSplit
    (BinaryAmbientMoves.Coordinate.generatedFirstSplit_iff.mpr forwardSplit))

example : (S0 ∆ S1).card = 3 := by decide

#check @GeneratedFirstSplit.symmDiff_eq
#check @SourceThirdFlip.symmDiff_eq
#check @DirectedNarrowPairReduction.symmDiff_eq
#check @Move.support_card
#check @AllModeMove.support_card
#check @AllModeMove.mem_iff_mem_of_not_mem_support
#check @AllModeMove.target_eq_toggle_support

end BilinearComplexity.BinaryAmbientMoveSupport
