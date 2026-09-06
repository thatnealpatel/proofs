import BilinearComplexity.FieldFiveToFour

set_option autoImplicit false

namespace BilinearComplexity
namespace FieldFiveToFourContext

open FieldRankOne FieldContextual FieldNativeMoves FieldNativePath
open FieldNativePairBridge FieldFiveToFour

abbrev F3 := FieldFiveToFour.F3

variable {a b c : ℕ}

namespace CertifiedFiveToFour

/-- The local source of the scanned bridge's stored outer native replacement. -/
noncomputable def outerSource {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I) :
    State F3 a b c :=
  match B.normalized.placement with
  | .sourceSource => pairState (I.atomAt B.normalized.leftIndex)
      (I.atomAt B.normalized.rightIndex)
  | .targetTarget => singletonState B.q
  | .opposite => singletonState (I.atomAt B.normalized.leftIndex)

/-- The local target of the scanned bridge's stored outer native replacement. -/
noncomputable def outerTarget {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I) :
    State F3 a b c :=
  match B.normalized.placement with
  | .sourceSource => singletonState B.q
  | .targetTarget => pairState (I.atomAt B.normalized.leftIndex)
      (I.atomAt B.normalized.rightIndex)
  | .opposite => pairState (I.atomAt B.normalized.rightIndex) B.q

/-- The stored outer replacement has the local endpoints computed above. -/
theorem outer_native {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I) :
    NativeReplacement (outerSource B) (outerTarget B) := by
  cases P : B.normalized <;>
    simpa only [outerSource, outerTarget, P, EffectiveDisplayedF3PairTriple.placement] using B.outer

/-- The effective contraction atom differs from every original displayed atom. -/
theorem q_ne_atomAt {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I)
    (i : Fin 5) : B.q ≠ I.atomAt i := by
  intro heq
  apply B.normalized.q_not_proportional i 1
  simpa only [FieldFiveToFour.CertifiedFiveToFour.q, one_smul] using congrArg Atom.val heq

/-- The effective contraction atom is absent from the original source endpoint. -/
theorem q_not_mem_sourceState {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) : B.q ∉ I.sourceState := by
  classical
  simp only [DisplayedF3PairTriple.sourceState, Finset.mem_image, Finset.mem_univ,
    true_and, not_exists]
  intro i
  exact (q_ne_atomAt B _).symm

/-- The effective contraction atom is absent from the original target endpoint. -/
theorem q_not_mem_targetState {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) : B.q ∉ I.targetState := by
  classical
  simp only [DisplayedF3PairTriple.targetState, Finset.mem_image, Finset.mem_univ,
    true_and, not_exists]
  intro i
  exact (q_ne_atomAt B _).symm

/-- Every local outer source is either an original source atom or the contraction atom. -/
theorem outerSource_subset {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) :
    outerSource B ⊆ stateUnion I.sourceState (singletonState B.q) := by
  classical
  cases P : B.normalized with
  | sourceSource u v huv hfirst hsecond pair =>
      fin_cases u <;> fin_cases v <;>
        simp_all [outerSource, P, EffectiveDisplayedF3PairTriple.placement,
          EffectiveDisplayedF3PairTriple.leftIndex, EffectiveDisplayedF3PairTriple.rightIndex,
          DisplayedF3PairTriple.sourceState, pairState, singletonState, stateUnion,
          Finset.subset_iff]
  | targetTarget u v huv hfirst hsecond pair =>
      simp [outerSource, P, EffectiveDisplayedF3PairTriple.placement, singletonState, stateUnion]
  | oppositeForward u v hfirst hsecond pair =>
      fin_cases u <;>
        simp_all [outerSource, P, EffectiveDisplayedF3PairTriple.placement,
          EffectiveDisplayedF3PairTriple.leftIndex, DisplayedF3PairTriple.sourceState,
          singletonState, stateUnion, Finset.subset_iff]
  | oppositeReverse u v hfirst hsecond pair =>
      fin_cases u <;>
        simp_all [outerSource, P, EffectiveDisplayedF3PairTriple.placement,
          EffectiveDisplayedF3PairTriple.leftIndex, DisplayedF3PairTriple.sourceState,
          singletonState, stateUnion, Finset.subset_iff]

/-- Every local outer target is either an original target atom or the contraction atom. -/
theorem outerTarget_subset {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) :
    outerTarget B ⊆ stateUnion I.targetState (singletonState B.q) := by
  classical
  cases P : B.normalized with
  | sourceSource u v huv hfirst hsecond pair =>
      simp [outerTarget, P, EffectiveDisplayedF3PairTriple.placement, singletonState, stateUnion]
  | targetTarget u v huv hfirst hsecond pair =>
      fin_cases u <;> fin_cases v <;>
        simp_all [outerTarget, P, EffectiveDisplayedF3PairTriple.placement,
          EffectiveDisplayedF3PairTriple.leftIndex, EffectiveDisplayedF3PairTriple.rightIndex,
          DisplayedF3PairTriple.targetState, pairState, singletonState, stateUnion,
          Finset.subset_iff]
  | oppositeForward u v hfirst hsecond pair =>
      fin_cases v <;>
        simp_all [outerTarget, P, EffectiveDisplayedF3PairTriple.placement,
          EffectiveDisplayedF3PairTriple.rightIndex, DisplayedF3PairTriple.targetState,
          pairState, singletonState, stateUnion, Finset.subset_iff]
  | oppositeReverse u v hfirst hsecond pair =>
      fin_cases v <;>
        simp_all [outerTarget, P, EffectiveDisplayedF3PairTriple.placement,
          EffectiveDisplayedF3PairTriple.rightIndex, DisplayedF3PairTriple.targetState,
          pairState, singletonState, stateUnion, Finset.subset_iff]

/-- The contraction atom is in the local source exactly in the target/target placement. -/
theorem q_mem_outerSource_iff {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) :
    B.q ∈ outerSource B ↔ B.normalized.placement = .targetTarget := by
  classical
  cases P : B.normalized <;>
    simp [outerSource, P, EffectiveDisplayedF3PairTriple.placement, singletonState, pairState,
      q_ne_atomAt B]

/-- The contraction atom is in the local target exactly outside the target/target placement. -/
theorem q_mem_outerTarget_iff {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) :
    B.q ∈ outerTarget B ↔ B.normalized.placement ≠ .targetTarget := by
  classical
  cases P : B.normalized <;>
    simp [outerTarget, P, EffectiveDisplayedF3PairTriple.placement, singletonState, pairState,
      q_ne_atomAt B]

/-- The actual local source and target of the scanned outer primitive are disjoint. -/
theorem outer_endpoints_disjoint {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) : Disjoint (outerSource B) (outerTarget B) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxS hxT
  have hxS' := outerSource_subset B hxS
  have hxT' := outerTarget_subset B hxT
  simp only [stateUnion, singletonState, Finset.mem_union, Finset.mem_singleton] at hxS' hxT'
  rcases hxS' with hxA | rfl
  · rcases hxT' with hxTarget | rfl
    · exact Finset.disjoint_left.mp I.source_target_disjoint hxA hxTarget
    · exact q_not_mem_sourceState B hxA
  · rcases hxT' with hxTarget | hqq
    · exact q_not_mem_targetState B hxTarget
    · have hsourcePlacement := (q_mem_outerSource_iff B).mp hxS
      have htargetPlacement := (q_mem_outerTarget_iff B).mp hxT
      exact htargetPlacement hsourcePlacement

end CertifiedFiveToFour


namespace Generic

variable {k : Type*} [Field k] {a b c : ℕ}

/-- Promote an actual stored native replacement to a strict whole-state step when its
source is present and its target is fresh. -/
noncomputable def actualOuterStrictNativeStep {D S T : State k a b c}
    (native : NativeReplacement S T) (hendpoints : Disjoint S T)
    (hsource : S ⊆ D) (hfresh : Disjoint T (stateDifference D S)) :
    StrictNativeStep D (stateUnion (stateDifference D S) T) := by
  refine {
    step := {
      source := S
      target := T
      native := native
      source_subset := hsource
      target_fresh := hfresh
      result_eq := rfl }
    endpoints_disjoint := hendpoints
    ne := ?_ }
  intro heq
  obtain ⟨x, hxS⟩ := nativeReplacement_source_nonempty native
  have hxD : x ∈ D := hsource hxS
  have hxOut : x ∈ stateUnion (stateDifference D S) T := heq ▸ hxD
  classical
  simp only [stateUnion, stateDifference, Finset.mem_union, Finset.mem_sdiff] at hxOut
  rcases hxOut with hxRest | hxT
  · exact hxRest.2 hxS
  · exact Finset.disjoint_left.mp hendpoints hxS hxT

/-- Construct the same actual strict outer step when its prescribed terminal state is
known and the local source is fresh against the terminal remainder. -/
noncomputable def actualOuterStrictNativeStepTo {E S T : State k a b c}
    (native : NativeReplacement S T) (hendpoints : Disjoint S T)
    (htarget : T ⊆ E) (hfresh : Disjoint S (stateDifference E T)) :
    StrictNativeStep (stateUnion (stateDifference E T) S) E := by
  classical
  have hcontext : Disjoint (stateDifference E T) S := hfresh.symm
  have htargetFresh : Disjoint T (stateDifference E T) := by
    rw [Finset.disjoint_left]
    intro x hxT hxRest
    simp only [stateDifference, Finset.mem_sdiff] at hxRest
    exact hxRest.2 hxT
  refine {
    step := {
      source := S
      target := T
      native := native
      source_subset := ?_
      target_fresh := ?_
      result_eq := ?_ }
    endpoints_disjoint := hendpoints
    ne := ?_ }
  · intro x hxS
    simp only [stateUnion, Finset.mem_union]
    exact Or.inr hxS
  · rw [erase_endpoint_restores_context hcontext]
    exact htargetFresh
  · rw [erase_endpoint_restores_context hcontext]
    exact (Finset.sdiff_union_of_subset htarget).symm
  · intro heq
    obtain ⟨x, hxS⟩ := nativeReplacement_source_nonempty native
    have hxStart : x ∈ stateUnion (stateDifference E T) S := by
      simp only [stateUnion, Finset.mem_union]
      exact Or.inr hxS
    have hxE : x ∈ E := heq ▸ hxStart
    by_cases hxT : x ∈ T
    · exact Finset.disjoint_left.mp hendpoints hxS hxT
    · have hxRest : x ∈ stateDifference E T := by
        simp only [stateDifference, Finset.mem_sdiff]
        exact ⟨hxE, hxT⟩
      exact Finset.disjoint_left.mp hfresh hxS hxRest

end Generic

namespace CertifiedFiveToFour

/-- Whether the outer primitive is scheduled before or after the supplied residual path. -/
inductive OuterSchedule
  | beforeResidual
  | afterResidual
  deriving DecidableEq, Repr

/-- The six-way schedule calculated from actual scanned placement and contraction-atom
occupancy. Source/source and opposite have `q` in the outer target; target/target has `q`
in the outer source. -/
noncomputable def schedule {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c) : OuterSchedule :=
  match B.normalized.placement with
  | .targetTarget => if B.q ∈ C then .beforeResidual else .afterResidual
  | .sourceSource | .opposite => if B.q ∈ C then .afterResidual else .beforeResidual

/-- The intrinsic source side of the signed residual four-circuit. -/
noncomputable def residualSource {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) : State F3 a b c :=
  stateUnion (stateDifference I.sourceState (outerSource B))
    (stateDifference (outerTarget B) I.targetState)

/-- The intrinsic target side of the signed residual four-circuit. -/
noncomputable def residualTarget {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) : State F3 a b c :=
  stateUnion (stateDifference I.targetState (outerTarget B))
    (stateDifference (outerSource B) I.sourceState)

/-- The exact retained context around the residual four-circuit for the selected schedule. -/
noncomputable def residualContext {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c) : State F3 a b c :=
  match schedule B C with
  | .beforeResidual =>
      stateUnion (stateDifference C (outerSource B))
        (stateDifference (outerTarget B) (singletonState B.q))
  | .afterResidual =>
      stateUnion (stateDifference C (outerTarget B))
        (stateDifference (outerSource B) (singletonState B.q))

/-- The calculated whole-state start requested of the checked residual path. -/
noncomputable def requestStart {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c) : State F3 a b c :=
  match schedule B C with
  | .beforeResidual => stateUnion
      (stateDifference (stateUnion C I.sourceState) (outerSource B)) (outerTarget B)
  | .afterResidual => stateUnion C I.sourceState

/-- The calculated whole-state finish requested of the checked residual path. -/
noncomputable def requestFinish {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c) : State F3 a b c :=
  match schedule B C with
  | .beforeResidual => stateUnion C I.targetState
  | .afterResidual => stateUnion
      (stateDifference (stateUnion C I.targetState) (outerTarget B)) (outerSource B)

private theorem context_source_disjoint {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c)
    (hC : Disjoint C (stateUnion I.sourceState I.targetState)) :
    Disjoint C I.sourceState := by
  rw [Finset.disjoint_left] at hC ⊢
  intro x hxC hxA
  exact hC hxC (by
    classical
    simp only [stateUnion, Finset.mem_union]
    exact Or.inl hxA)

private theorem context_target_disjoint {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c)
    (hC : Disjoint C (stateUnion I.sourceState I.targetState)) :
    Disjoint C I.targetState := by
  rw [Finset.disjoint_left] at hC ⊢
  intro x hxC hxT
  exact hC hxC (by
    classical
    simp only [stateUnion, Finset.mem_union]
    exact Or.inr hxT)

private theorem source_subset_initial {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c)
    (hq : B.q ∈ outerSource B → B.q ∈ C) :
    outerSource B ⊆ stateUnion C I.sourceState := by
  intro x hx
  have hs := outerSource_subset B hx
  classical
  simp only [stateUnion, singletonState, Finset.mem_union, Finset.mem_singleton] at hs ⊢
  rcases hs with hxA | rfl
  · exact Or.inr hxA
  · exact Or.inl (hq hx)

private theorem target_fresh_initial {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c)
    (hC : Disjoint C (stateUnion I.sourceState I.targetState))
    (hq : B.q ∈ outerTarget B → B.q ∉ C) :
    Disjoint (outerTarget B)
      (stateDifference (stateUnion C I.sourceState) (outerSource B)) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxT hxRest
  have ht := outerTarget_subset B hxT
  simp only [stateUnion, singletonState, stateDifference, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_sdiff] at ht hxRest
  rcases ht with hxB | rfl
  · rcases hxRest.1 with hxC | hxA
    · exact Finset.disjoint_left.mp (context_target_disjoint B C hC) hxC hxB
    · exact Finset.disjoint_left.mp I.source_target_disjoint hxA hxB
  · rcases hxRest.1 with hxC | hxA
    · exact hq hxT hxC
    · exact q_not_mem_sourceState B hxA

private theorem target_subset_final {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c)
    (hq : B.q ∈ outerTarget B → B.q ∈ C) :
    outerTarget B ⊆ stateUnion C I.targetState := by
  intro x hx
  have ht := outerTarget_subset B hx
  classical
  simp only [stateUnion, singletonState, Finset.mem_union, Finset.mem_singleton] at ht ⊢
  rcases ht with hxB | rfl
  · exact Or.inr hxB
  · exact Or.inl (hq hx)

private theorem source_fresh_final {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c)
    (hC : Disjoint C (stateUnion I.sourceState I.targetState))
    (hq : B.q ∈ outerSource B → B.q ∉ C) :
    Disjoint (outerSource B)
      (stateDifference (stateUnion C I.targetState) (outerTarget B)) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxS hxRest
  have hs := outerSource_subset B hxS
  simp only [stateUnion, singletonState, stateDifference, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_sdiff] at hs hxRest
  rcases hs with hxA | rfl
  · rcases hxRest.1 with hxC | hxB
    · exact Finset.disjoint_left.mp (context_source_disjoint B C hC) hxC hxA
    · exact Finset.disjoint_left.mp I.source_target_disjoint hxA hxB
  · rcases hxRest.1 with hxC | hxB
    · exact hq hxS hxC
    · exact q_not_mem_targetState B hxB

/-- Splice one already checked residual whole-state path into the actual full scanned
five-to-four bridge. This is conditional infrastructure: it constructs no residual path. -/
noncomputable def compose {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c)
    (hC : Disjoint C (stateUnion I.sourceState I.targetState))
    (fourPath : StrictNativePath (requestStart B C) (requestFinish B C)) :
    StrictNativePath (stateUnion C I.sourceState) (stateUnion C I.targetState) := by
  cases hp : B.normalized.placement with
  | sourceSource =>
      by_cases hqC : B.q ∈ C
      · have hsourceQ : B.q ∈ outerSource B → B.q ∉ C := by
          intro hqS
          have hplace := (q_mem_outerSource_iff B).mp hqS
          simp [hp] at hplace
        let last := Generic.actualOuterStrictNativeStepTo (outer_native B)
          (outer_endpoints_disjoint B)
          (target_subset_final B C (fun _ => hqC))
          (source_fresh_final B C hC hsourceQ)
        have hschedule : schedule B C = .afterResidual := by simp [schedule, hp, hqC]
        have fourPath' : StrictNativePath (stateUnion C I.sourceState)
            (stateUnion (stateDifference (stateUnion C I.targetState) (outerTarget B))
              (outerSource B)) := by
          simpa only [requestStart, requestFinish, hschedule] using fourPath
        exact Path.snoc fourPath' last
      · have hsourceQ : B.q ∈ outerSource B → B.q ∈ C := by
          intro hqS
          have hplace := (q_mem_outerSource_iff B).mp hqS
          simp [hp] at hplace
        let first := Generic.actualOuterStrictNativeStep (outer_native B)
          (outer_endpoints_disjoint B)
          (source_subset_initial B C hsourceQ)
          (target_fresh_initial B C hC (fun _ => hqC))
        have hschedule : schedule B C = .beforeResidual := by simp [schedule, hp, hqC]
        have fourPath' : StrictNativePath
            (stateUnion (stateDifference (stateUnion C I.sourceState) (outerSource B))
              (outerTarget B)) (stateUnion C I.targetState) := by
          simpa only [requestStart, requestFinish, hschedule] using fourPath
        exact .cons first fourPath'
  | targetTarget =>
      by_cases hqC : B.q ∈ C
      · have htargetQ : B.q ∈ outerTarget B → B.q ∉ C := by
          intro hqT
          exact False.elim (((q_mem_outerTarget_iff B).mp hqT) hp)
        let first := Generic.actualOuterStrictNativeStep (outer_native B)
          (outer_endpoints_disjoint B)
          (source_subset_initial B C (fun _ => hqC))
          (target_fresh_initial B C hC htargetQ)
        have hschedule : schedule B C = .beforeResidual := by simp [schedule, hp, hqC]
        have fourPath' : StrictNativePath
            (stateUnion (stateDifference (stateUnion C I.sourceState) (outerSource B))
              (outerTarget B)) (stateUnion C I.targetState) := by
          simpa only [requestStart, requestFinish, hschedule] using fourPath
        exact .cons first fourPath'
      · have htargetQ : B.q ∈ outerTarget B → B.q ∈ C := by
          intro hqT
          exact False.elim (((q_mem_outerTarget_iff B).mp hqT) hp)
        let last := Generic.actualOuterStrictNativeStepTo (outer_native B)
          (outer_endpoints_disjoint B)
          (target_subset_final B C htargetQ)
          (source_fresh_final B C hC (fun _ => hqC))
        have hschedule : schedule B C = .afterResidual := by simp [schedule, hp, hqC]
        have fourPath' : StrictNativePath (stateUnion C I.sourceState)
            (stateUnion (stateDifference (stateUnion C I.targetState) (outerTarget B))
              (outerSource B)) := by
          simpa only [requestStart, requestFinish, hschedule] using fourPath
        exact Path.snoc fourPath' last
  | opposite =>
      by_cases hqC : B.q ∈ C
      · have hsourceQ : B.q ∈ outerSource B → B.q ∉ C := by
          intro hqS
          have hplace := (q_mem_outerSource_iff B).mp hqS
          simp [hp] at hplace
        let last := Generic.actualOuterStrictNativeStepTo (outer_native B)
          (outer_endpoints_disjoint B)
          (target_subset_final B C (fun _ => hqC))
          (source_fresh_final B C hC hsourceQ)
        have hschedule : schedule B C = .afterResidual := by simp [schedule, hp, hqC]
        have fourPath' : StrictNativePath (stateUnion C I.sourceState)
            (stateUnion (stateDifference (stateUnion C I.targetState) (outerTarget B))
              (outerSource B)) := by
          simpa only [requestStart, requestFinish, hschedule] using fourPath
        exact Path.snoc fourPath' last
      · have hsourceQ : B.q ∈ outerSource B → B.q ∈ C := by
          intro hqS
          have hplace := (q_mem_outerSource_iff B).mp hqS
          simp [hp] at hplace
        let first := Generic.actualOuterStrictNativeStep (outer_native B)
          (outer_endpoints_disjoint B)
          (source_subset_initial B C hsourceQ)
          (target_fresh_initial B C hC (fun _ => hqC))
        have hschedule : schedule B C = .beforeResidual := by simp [schedule, hp, hqC]
        have fourPath' : StrictNativePath
            (stateUnion (stateDifference (stateUnion C I.sourceState) (outerSource B))
              (outerTarget B)) (stateUnion C I.targetState) := by
          simpa only [requestStart, requestFinish, hschedule] using fourPath
        exact .cons first fourPath'

end CertifiedFiveToFour

namespace CertifiedFiveToFour

/-- The conditional splice adds exactly its one actual outer native primitive. -/
theorem length_compose {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c)
    (hC : Disjoint C (stateUnion I.sourceState I.targetState))
    (fourPath : StrictNativePath (requestStart B C) (requestFinish B C)) :
    Path.length (compose B C hC fourPath) = Path.length fourPath + 1 := by
  unfold compose
  split <;> cases hplace : B.normalized.placement <;>
    simp [hplace, Path.length_snoc, Path.length]

/-- Reversing the completed splice preserves its exact primitive length. -/
theorem length_reverse_compose {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c)
    (hC : Disjoint C (stateUnion I.sourceState I.targetState))
    (fourPath : StrictNativePath (requestStart B C) (requestFinish B C)) :
    Path.length (Path.reverse (compose B C hC fourPath)) = Path.length fourPath + 1 := by
  rw [Path.length_reverse, length_compose]

end CertifiedFiveToFour

end FieldFiveToFourContext
end BilinearComplexity
