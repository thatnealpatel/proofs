import BilinearComplexity.FieldFiveToFourContext

set_option autoImplicit false
namespace BilinearComplexity.FieldFiveToFourContext.CertifiedFiveToFour
open FieldRankOne FieldContextual FieldNativeMoves FieldNativePath
open FieldNativePairBridge FieldFiveToFour FieldCircuitContraction
abbrev F3 := FieldFiveToFour.F3
variable {a b c : ℕ}

private theorem atomAt_mem_sourceState_iff_coefficient_one
    (I : DisplayedF3PairTriple a b c) (k : Fin 5) :
    I.atomAt k ∈ I.sourceState ↔ I.coefficient k = 1 := by
  let z := I.slots.symm k
  have hk : I.slots z = k := I.slots.apply_symm_apply k
  rw [← hk]
  cases z with
  | inl u =>
      simp [DisplayedF3PairTriple.sourceState,
        DisplayedF3PairTriple.coefficient, I.atomAt_injective.eq_iff]
  | inr v =>
      simp [DisplayedF3PairTriple.sourceState,
        DisplayedF3PairTriple.coefficient, I.atomAt_injective.eq_iff]
      exact by decide

private theorem signedResidualAtom_mem_sourceState_of_coefficient_one
    {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I)
    (hp : B.normalized.placement = .targetTarget) (i : Fin 4)
    (hi : signedFourCoefficients (k := F3) B.normalized.residualShape i = 1) :
    B.signedResidualAtom i ∈ I.sourceState := by
  let P := B.normalized
  have hcoef := P.residual_coefficients_reindex i
  change signedFourCoefficients (k := F3) P.residualShape i = 1 at hi
  rw [hi] at hcoef
  change P.residualAtomFamily (P.residualReindex i) ∈ I.sourceState
  let r := P.residualReindex i
  change P.residualAtomFamily r ∈ I.sourceState
  change P.contraction.residualCoefficients r = 1 at hcoef
  revert hcoef
  refine Fin.cases ?_ (fun j hcoef => ?_) r
  · intro hcoef
    rw [EffectiveDisplayedF3PairTriple.contraction_residualCoefficients_zero] at hcoef
    change P.placement = .targetTarget at hp
    cases Q : P with
    | sourceSource => simp [Q, EffectiveDisplayedF3PairTriple.placement] at hp
    | targetTarget u v huv hfirst hsecond pair =>
        simp [Q, EffectiveDisplayedF3PairTriple.leftIndex,
          DisplayedF3PairTriple.coefficient, hfirst] at hcoef
        exact False.elim ((by decide : (-1 : F3) ≠ 1) hcoef)
    | oppositeForward => simp [Q, EffectiveDisplayedF3PairTriple.placement] at hp
    | oppositeReverse => simp [Q, EffectiveDisplayedF3PairTriple.placement] at hp
  · change I.atomAt (P.normalizedSplit (.inr j)) ∈ I.sourceState
    rw [atomAt_mem_sourceState_iff_coefficient_one]
    simpa only [EffectiveDisplayedF3PairTriple.contraction_residualCoefficients_succ] using hcoef


private theorem signedResidualAtom_injective
    {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I) :
    Function.Injective B.signedResidualAtom := by
  intro i j hij
  apply B.signedResidual.everyDeletionIndependent.injective B.signedResidual.term
  simpa only [← FieldFiveToFour.CertifiedFiveToFour.signedResidualAtom_val] using
    congrArg Atom.val hij

private theorem normalizedSplit_right_ne_left
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) (j : Fin 3) :
    P.normalizedSplit (.inr j) ≠ P.leftIndex := by
  intro h
  have heq : P.normalizedSplit (.inr j) = P.normalizedSplit (.inl 0) :=
    h.trans P.normalizedSplit_left_zero.symm
  exact Sum.inr_ne_inl (P.normalizedSplit.injective heq)

private theorem normalizedSplit_right_ne_right
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) (j : Fin 3) :
    P.normalizedSplit (.inr j) ≠ P.rightIndex := by
  intro h
  have heq : P.normalizedSplit (.inr j) = P.normalizedSplit (.inl 1) :=
    h.trans P.normalizedSplit_left_one.symm
  exact Sum.inr_ne_inl (P.normalizedSplit.injective heq)

private theorem signedResidualAtom_mem_residualSource_of_coefficient_one
    {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I) (i : Fin 4)
    (hi : signedFourCoefficients (k := F3) B.normalized.residualShape i = 1) :
    B.signedResidualAtom i ∈ residualSource B := by
  let P := B.normalized
  have hcoef := P.residual_coefficients_reindex i
  change signedFourCoefficients (k := F3) P.residualShape i = 1 at hi
  rw [hi] at hcoef
  change P.residualAtomFamily (P.residualReindex i) ∈ residualSource B
  let r := P.residualReindex i
  change P.residualAtomFamily r ∈ residualSource B
  change P.contraction.residualCoefficients r = 1 at hcoef
  revert hcoef
  refine Fin.cases ?_ (fun j hcoef => ?_) r
  · intro hcoef
    rw [EffectiveDisplayedF3PairTriple.contraction_residualCoefficients_zero] at hcoef
    have hp : P.placement ≠ .targetTarget := by
      intro hp
      cases Q : P with
      | sourceSource => simp [Q, EffectiveDisplayedF3PairTriple.placement] at hp
      | targetTarget u v huv hfirst hsecond pair =>
          simp [Q, EffectiveDisplayedF3PairTriple.leftIndex,
            DisplayedF3PairTriple.coefficient, hfirst] at hcoef
          exact (by decide : (-1 : F3) ≠ 1) hcoef
      | oppositeForward => simp [Q, EffectiveDisplayedF3PairTriple.placement] at hp
      | oppositeReverse => simp [Q, EffectiveDisplayedF3PairTriple.placement] at hp
    rw [residualSource]
    simp only [stateUnion, stateDifference, Finset.mem_union, Finset.mem_sdiff]
    exact Or.inr ⟨(q_mem_outerTarget_iff B).mpr hp, q_not_mem_targetState B⟩
  · let k := P.normalizedSplit (.inr j)
    have hsource : I.atomAt k ∈ I.sourceState := by
      rw [atomAt_mem_sourceState_iff_coefficient_one]
      simpa only [EffectiveDisplayedF3PairTriple.contraction_residualCoefficients_succ] using hcoef
    have hkL : I.atomAt k ≠ I.atomAt P.leftIndex := by
      intro h
      exact normalizedSplit_right_ne_left P j (I.atomAt_injective h)
    have hkR : I.atomAt k ≠ I.atomAt P.rightIndex := by
      intro h
      exact normalizedSplit_right_ne_right P j (I.atomAt_injective h)
    have hkq : I.atomAt k ≠ B.q := (q_ne_atomAt B k).symm
    change I.atomAt k ≠ I.atomAt B.normalized.leftIndex at hkL
    change I.atomAt k ≠ I.atomAt B.normalized.rightIndex at hkR
    have houter : I.atomAt k ∉ outerSource B := by
      unfold outerSource
      split <;> simp_all [pairState, singletonState]
    rw [residualSource]
    simp only [stateUnion, stateDifference, Finset.mem_union, Finset.mem_sdiff]
    exact Or.inl ⟨hsource, houter⟩

private theorem sourceState_eq_pairState (I : DisplayedF3PairTriple a b c) :
    I.sourceState = pairState (I.atomAt (I.slots (.inl 0)))
      (I.atomAt (I.slots (.inl 1))) := by
  ext x
  simp only [DisplayedF3PairTriple.sourceState, pairState,
    Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨u, rfl⟩
    fin_cases u <;> simp
  · intro hx
    rcases hx with h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩

private theorem targetState_eq_tripleState (I : DisplayedF3PairTriple a b c) :
    I.targetState =
      {I.atomAt (I.slots (.inr 0)), I.atomAt (I.slots (.inr 1)),
        I.atomAt (I.slots (.inr 2))} := by
  ext x
  simp only [DisplayedF3PairTriple.targetState, Finset.mem_image,
    Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨u, rfl⟩
    fin_cases u <;> simp
  · intro hx
    rcases hx with h | h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩

private theorem atomAt_slots_eq_iff (I : DisplayedF3PairTriple a b c)
    (i j : Fin 2 ⊕ Fin 3) :
    I.atomAt (I.slots i) = I.atomAt (I.slots j) ↔ i = j :=
  I.atomAt_injective.eq_iff.trans I.slots.injective.eq_iff

private theorem atomAt_slot_ne_q {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (i : Fin 2 ⊕ Fin 3) :
    I.atomAt (I.slots i) ≠ B.q :=
  (q_ne_atomAt B (I.slots i)).symm

private theorem q_eq_atomAt_iff_false {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (i : Fin 5) :
    B.q = I.atomAt i ↔ False :=
  iff_false_intro (q_ne_atomAt B i)

private theorem atomAt_eq_q_iff_false {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (i : Fin 5) :
    I.atomAt i = B.q ↔ False :=
  iff_false_intro (q_ne_atomAt B i).symm

private theorem residualSource_eq_singleton_of_sourceSource
    {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I)
    (hp : B.normalized.placement = .sourceSource) :
    residualSource B = singletonState B.q := by
  ext x
  cases Q : B.normalized with
  | sourceSource u v huv hfirst hsecond pair =>
      fin_cases u <;> fin_cases v <;>
        simp_all [residualSource, outerSource, outerTarget, Q,
          EffectiveDisplayedF3PairTriple.placement,
          EffectiveDisplayedF3PairTriple.leftIndex,
          EffectiveDisplayedF3PairTriple.rightIndex,
          sourceState_eq_pairState I, targetState_eq_tripleState I,
          pairState, singletonState, stateUnion, stateDifference,
          atomAt_slots_eq_iff I, atomAt_slot_ne_q B, q_ne_atomAt B,
          Fin.ext_iff] <;> aesop
  | targetTarget => simp [Q, EffectiveDisplayedF3PairTriple.placement] at hp
  | oppositeForward => simp [Q, EffectiveDisplayedF3PairTriple.placement] at hp
  | oppositeReverse => simp [Q, EffectiveDisplayedF3PairTriple.placement] at hp

private theorem residualSource_eq_sourceState_of_targetTarget
    {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I)
    (hp : B.normalized.placement = .targetTarget) :
    residualSource B = I.sourceState := by
  ext x
  cases Q : B.normalized with
  | sourceSource => simp [Q, EffectiveDisplayedF3PairTriple.placement] at hp
  | targetTarget u v huv hfirst hsecond pair =>
      fin_cases u <;> fin_cases v <;>
        simp_all [residualSource, outerSource, outerTarget, Q,
          EffectiveDisplayedF3PairTriple.placement,
          EffectiveDisplayedF3PairTriple.leftIndex,
          EffectiveDisplayedF3PairTriple.rightIndex,
          sourceState_eq_pairState I, targetState_eq_tripleState I,
          pairState, singletonState, stateUnion, stateDifference,
          atomAt_slots_eq_iff I, atomAt_slot_ne_q B, q_ne_atomAt B,
          Fin.ext_iff] <;> aesop
  | oppositeForward => simp [Q, EffectiveDisplayedF3PairTriple.placement] at hp
  | oppositeReverse => simp [Q, EffectiveDisplayedF3PairTriple.placement] at hp

private theorem residualSource_eq_pair_of_opposite_left_zero
    {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I)
    (hp : B.normalized.placement = .opposite)
    (hleft : B.normalized.leftIndex = I.slots (.inl 0)) :
    residualSource B = pairState (I.atomAt (I.slots (.inl 1))) B.q := by
  ext x
  cases Q : B.normalized with
  | sourceSource => simp [Q, EffectiveDisplayedF3PairTriple.placement] at hp
  | targetTarget => simp [Q, EffectiveDisplayedF3PairTriple.placement] at hp
  | oppositeForward u v hfirst hsecond pair =>
      fin_cases u <;> fin_cases v <;>
        simp_all [residualSource, outerSource, outerTarget, Q,
          EffectiveDisplayedF3PairTriple.placement,
          EffectiveDisplayedF3PairTriple.leftIndex,
          EffectiveDisplayedF3PairTriple.rightIndex,
          sourceState_eq_pairState I, targetState_eq_tripleState I,
          pairState, singletonState, stateUnion, stateDifference,
          atomAt_slots_eq_iff I, atomAt_slot_ne_q B, q_ne_atomAt B,
          Fin.ext_iff] <;> aesop
  | oppositeReverse u v hfirst hsecond pair =>
      fin_cases u <;> fin_cases v <;>
        simp_all [residualSource, outerSource, outerTarget, Q,
          EffectiveDisplayedF3PairTriple.placement,
          EffectiveDisplayedF3PairTriple.leftIndex,
          EffectiveDisplayedF3PairTriple.rightIndex,
          sourceState_eq_pairState I, targetState_eq_tripleState I,
          pairState, singletonState, stateUnion, stateDifference,
          atomAt_slots_eq_iff I, atomAt_slot_ne_q B, q_ne_atomAt B,
          Fin.ext_iff] <;> aesop

private theorem residualSource_eq_pair_of_opposite_left_one
    {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I)
    (hp : B.normalized.placement = .opposite)
    (hleft : B.normalized.leftIndex = I.slots (.inl 1)) :
    residualSource B = pairState (I.atomAt (I.slots (.inl 0))) B.q := by
  ext x
  cases Q : B.normalized with
  | sourceSource => simp [Q, EffectiveDisplayedF3PairTriple.placement] at hp
  | targetTarget => simp [Q, EffectiveDisplayedF3PairTriple.placement] at hp
  | oppositeForward u v hfirst hsecond pair =>
      fin_cases u <;> fin_cases v <;>
        simp_all [residualSource, outerSource, outerTarget, Q,
          EffectiveDisplayedF3PairTriple.placement,
          EffectiveDisplayedF3PairTriple.leftIndex,
          EffectiveDisplayedF3PairTriple.rightIndex,
          sourceState_eq_pairState I, targetState_eq_tripleState I,
          pairState, singletonState, stateUnion, stateDifference,
          atomAt_slots_eq_iff I, atomAt_slot_ne_q B, q_ne_atomAt B,
          Fin.ext_iff] <;> aesop
  | oppositeReverse u v hfirst hsecond pair =>
      fin_cases u <;> fin_cases v <;>
        simp_all [residualSource, outerSource, outerTarget, Q,
          EffectiveDisplayedF3PairTriple.placement,
          EffectiveDisplayedF3PairTriple.leftIndex,
          EffectiveDisplayedF3PairTriple.rightIndex,
          sourceState_eq_pairState I, targetState_eq_tripleState I,
          pairState, singletonState, stateUnion, stateDifference,
          atomAt_slots_eq_iff I, atomAt_slot_ne_q B, q_ne_atomAt B,
          Fin.ext_iff] <;> aesop

private theorem signedResidualSource_eq_sourceState_of_targetTarget
    {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I)
    (hp : B.normalized.placement = .targetTarget) :
    B.signedResidualSource = I.sourceState := by
  have hshape : B.normalized.residualShape = .twoTwo := by
    unfold EffectiveDisplayedF3PairTriple.residualShape
    rw [hp]
  have h0 := signedResidualAtom_mem_sourceState_of_coefficient_one B hp 0 (by
    rw [hshape]
    decide)
  have h1 := signedResidualAtom_mem_sourceState_of_coefficient_one B hp 1 (by
    rw [hshape]
    decide)
  have hne : B.signedResidualAtom 0 ≠ B.signedResidualAtom 1 := by
    intro h
    have ht : B.signedResidual.term 0 = B.signedResidual.term 1 := by
      simpa only [← FieldFiveToFour.CertifiedFiveToFour.signedResidualAtom_val] using congrArg Atom.val h
    exact Fin.zero_ne_one (B.signedResidual.everyDeletionIndependent.injective _ ht)
  have mem_source_iff (x : Atom F3 a b c) :
      x ∈ I.sourceState ↔
        x = I.atomAt (I.slots (.inl 0)) ∨
          x = I.atomAt (I.slots (.inl 1)) := by
    constructor
    · intro hx
      rw [DisplayedF3PairTriple.sourceState] at hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨u, hu⟩ := hx
      fin_cases u
      · exact Or.inl hu.symm
      · exact Or.inr hu.symm
    · intro hx
      rw [DisplayedF3PairTriple.sourceState]
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      rcases hx with h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
  have h0d := (mem_source_iff _).mp h0
  have h1d := (mem_source_iff _).mp h1
  rw [FieldFiveToFour.CertifiedFiveToFour.signedResidualSource]
  simp only [EffectiveDisplayedF3PairTriple.signedResidualSource, hshape, pairState]
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton, mem_source_iff]
  rcases h0d with h00 | h01 <;> rcases h1d with h10 | h11 <;>
    simp_all [FieldFiveToFour.CertifiedFiveToFour.signedResidualAtom] <;> aesop

end BilinearComplexity.FieldFiveToFourContext.CertifiedFiveToFour
