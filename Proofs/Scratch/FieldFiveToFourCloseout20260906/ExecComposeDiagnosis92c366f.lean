import BilinearComplexity.FieldFiveToFour
import BilinearComplexity.FieldNativeExecutablePath

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

/-- Transport a strict path across endpoint equalities without changing its steps. -/
noncomputable def castStrictNativePath {D E D' E' : State k a b c}
    (hD : D = D') (hE : E = E') (path : StrictNativePath D E) :
    StrictNativePath D' E' := by
  subst D'
  subst E'
  exact path

/-- Endpoint transport does not change primitive length. -/
theorem length_castStrictNativePath {D E D' E' : State k a b c}
    (hD : D = D') (hE : E = E') (path : StrictNativePath D E) :
    Path.length (castStrictNativePath hD hE path) = Path.length path := by
  subst D'
  subst E'
  rfl

/-- Endpoint transport preserves every height bound. -/
theorem heightBound_castStrictNativePath {D E D' E' : State k a b c}
    {H : ℕ} (hD : D = D') (hE : E = E') (path : StrictNativePath D E)
    (hpath : Path.HeightBound H path) :
    Path.HeightBound H (castStrictNativePath hD hE path) := by
  subst D'
  subst E'
  exact hpath

/-- A height bound may be weakened to a larger bound. -/
theorem heightBound_mono {D E : State k a b c} {path : StrictNativePath D E}
    {H H' : ℕ} (hpath : Path.HeightBound H path) (hHH' : H ≤ H') :
    Path.HeightBound H' path := by
  induction hpath with
  | nil D hD => exact .nil D (hD.trans hHH')
  | cons hD htail ih => exact .cons (hD.trans hHH') ih

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

private noncomputable def composeWithLength {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c)
    (hC : Disjoint C (stateUnion I.sourceState I.targetState))
    (fourPath : StrictNativePath (requestStart B C) (requestFinish B C)) :
    { path : StrictNativePath (stateUnion C I.sourceState) (stateUnion C I.targetState) //
      Path.length path = Path.length fourPath + 1 } := by
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
        let fourPath' : StrictNativePath (stateUnion C I.sourceState)
            (stateUnion (stateDifference (stateUnion C I.targetState) (outerTarget B))
              (outerSource B)) := Generic.castStrictNativePath
                (by simp only [requestStart, hschedule])
                (by simp only [requestFinish, hschedule]) fourPath
        refine ⟨Path.snoc fourPath' last, ?_⟩
        rw [Path.length_snoc, Generic.length_castStrictNativePath]
      · have hsourceQ : B.q ∈ outerSource B → B.q ∈ C := by
          intro hqS
          have hplace := (q_mem_outerSource_iff B).mp hqS
          simp [hp] at hplace
        let first := Generic.actualOuterStrictNativeStep (outer_native B)
          (outer_endpoints_disjoint B)
          (source_subset_initial B C hsourceQ)
          (target_fresh_initial B C hC (fun _ => hqC))
        have hschedule : schedule B C = .beforeResidual := by simp [schedule, hp, hqC]
        let fourPath' : StrictNativePath
            (stateUnion (stateDifference (stateUnion C I.sourceState) (outerSource B))
              (outerTarget B)) (stateUnion C I.targetState) :=
          Generic.castStrictNativePath (by simp only [requestStart, hschedule])
            (by simp only [requestFinish, hschedule]) fourPath
        refine ⟨.cons first fourPath', ?_⟩
        have hlength : Path.length fourPath' = Path.length fourPath := by
          exact Generic.length_castStrictNativePath _ _ fourPath
        simp only [Path.length]
        omega
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
        let fourPath' : StrictNativePath
            (stateUnion (stateDifference (stateUnion C I.sourceState) (outerSource B))
              (outerTarget B)) (stateUnion C I.targetState) :=
          Generic.castStrictNativePath (by simp only [requestStart, hschedule])
            (by simp only [requestFinish, hschedule]) fourPath
        refine ⟨.cons first fourPath', ?_⟩
        have hlength : Path.length fourPath' = Path.length fourPath := by
          exact Generic.length_castStrictNativePath _ _ fourPath
        simp only [Path.length]
        omega
      · have htargetQ : B.q ∈ outerTarget B → B.q ∈ C := by
          intro hqT
          exact False.elim (((q_mem_outerTarget_iff B).mp hqT) hp)
        let last := Generic.actualOuterStrictNativeStepTo (outer_native B)
          (outer_endpoints_disjoint B)
          (target_subset_final B C htargetQ)
          (source_fresh_final B C hC (fun _ => hqC))
        have hschedule : schedule B C = .afterResidual := by simp [schedule, hp, hqC]
        let fourPath' : StrictNativePath (stateUnion C I.sourceState)
            (stateUnion (stateDifference (stateUnion C I.targetState) (outerTarget B))
              (outerSource B)) := Generic.castStrictNativePath
                (by simp only [requestStart, hschedule])
                (by simp only [requestFinish, hschedule]) fourPath
        refine ⟨Path.snoc fourPath' last, ?_⟩
        rw [Path.length_snoc, Generic.length_castStrictNativePath]
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
        let fourPath' : StrictNativePath (stateUnion C I.sourceState)
            (stateUnion (stateDifference (stateUnion C I.targetState) (outerTarget B))
              (outerSource B)) := Generic.castStrictNativePath
                (by simp only [requestStart, hschedule])
                (by simp only [requestFinish, hschedule]) fourPath
        refine ⟨Path.snoc fourPath' last, ?_⟩
        rw [Path.length_snoc, Generic.length_castStrictNativePath]
      · have hsourceQ : B.q ∈ outerSource B → B.q ∈ C := by
          intro hqS
          have hplace := (q_mem_outerSource_iff B).mp hqS
          simp [hp] at hplace
        let first := Generic.actualOuterStrictNativeStep (outer_native B)
          (outer_endpoints_disjoint B)
          (source_subset_initial B C hsourceQ)
          (target_fresh_initial B C hC (fun _ => hqC))
        have hschedule : schedule B C = .beforeResidual := by simp [schedule, hp, hqC]
        let fourPath' : StrictNativePath
            (stateUnion (stateDifference (stateUnion C I.sourceState) (outerSource B))
              (outerTarget B)) (stateUnion C I.targetState) :=
          Generic.castStrictNativePath (by simp only [requestStart, hschedule])
            (by simp only [requestFinish, hschedule]) fourPath
        refine ⟨.cons first fourPath', ?_⟩
        have hlength : Path.length fourPath' = Path.length fourPath := by
          exact Generic.length_castStrictNativePath _ _ fourPath
        simp only [Path.length]
        omega

/-- Splice one already checked residual whole-state path into the actual full scanned
five-to-four bridge. This is conditional infrastructure: it constructs no residual path. -/
noncomputable def compose {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c)
    (hC : Disjoint C (stateUnion I.sourceState I.targetState))
    (fourPath : StrictNativePath (requestStart B C) (requestFinish B C)) :
    StrictNativePath (stateUnion C I.sourceState) (stateUnion C I.targetState) :=
  (composeWithLength B C hC fourPath).1

/-- The conditional splice adds exactly its one actual outer native primitive. -/
theorem length_compose {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c)
    (hC : Disjoint C (stateUnion I.sourceState I.targetState))
    (fourPath : StrictNativePath (requestStart B C) (requestFinish B C)) :
    Path.length (compose B C hC fourPath) = Path.length fourPath + 1 :=
  (composeWithLength B C hC fourPath).2

namespace Executable

open FieldNativeExecutablePath

/-- Computed two-atom source state of the displayed configuration. -/
def sourceState (I : DisplayedF3PairTriple a b c) : State F3 a b c :=
  Finset.image (fun i => I.atomAt (I.slots (.inl i))) Finset.univ

/-- Computed three-atom target state of the displayed configuration. -/
def targetState (I : DisplayedF3PairTriple a b c) : State F3 a b c :=
  Finset.image (fun i => I.atomAt (I.slots (.inr i))) Finset.univ

/-- Computed local source of the stored outer native primitive. -/
def outerSource {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I) :
    State F3 a b c :=
  match B.normalized.placement with
  | .sourceSource => ComputedState.pair (I.atomAt B.normalized.leftIndex)
      (I.atomAt B.normalized.rightIndex)
  | .targetTarget => ComputedState.singleton B.q
  | .opposite => ComputedState.singleton (I.atomAt B.normalized.leftIndex)

/-- Computed local target of the stored outer native primitive. -/
def outerTarget {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I) :
    State F3 a b c :=
  match B.normalized.placement with
  | .sourceSource => ComputedState.singleton B.q
  | .targetTarget => ComputedState.pair (I.atomAt B.normalized.leftIndex)
      (I.atomAt B.normalized.rightIndex)
  | .opposite => ComputedState.pair (I.atomAt B.normalized.rightIndex) B.q

/-- Computed source state agrees with the proof-side displayed source. -/
theorem sourceState_eq_spec (I : DisplayedF3PairTriple a b c) :
    sourceState I = I.sourceState := by
  classical
  ext x
  simp only [sourceState, DisplayedF3PairTriple.sourceState, Finset.mem_image]

/-- Computed target state agrees with the proof-side displayed target. -/
theorem targetState_eq_spec (I : DisplayedF3PairTriple a b c) :
    targetState I = I.targetState := by
  classical
  ext x
  simp only [targetState, DisplayedF3PairTriple.targetState, Finset.mem_image]

/-- Computed local source agrees with the proof-side outer source. -/
theorem outerSource_eq_spec {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) : outerSource B = CertifiedFiveToFour.outerSource B := by
  classical
  unfold outerSource CertifiedFiveToFour.outerSource
  split <;> simp only [ComputedState.pair_eq_spec, ComputedState.singleton_eq_spec]

/-- Computed local target agrees with the proof-side outer target. -/
theorem outerTarget_eq_spec {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) : outerTarget B = CertifiedFiveToFour.outerTarget B := by
  classical
  unfold outerTarget CertifiedFiveToFour.outerTarget
  split <;> simp only [ComputedState.pair_eq_spec, ComputedState.singleton_eq_spec]

/-- Computed full initial state of the contextual five-to-four splice. -/
def fullStart {I : DisplayedF3PairTriple a b c} (C : State F3 a b c) : State F3 a b c :=
  ComputedState.union C (sourceState I)

/-- Computed full terminal state of the contextual five-to-four splice. -/
def fullFinish {I : DisplayedF3PairTriple a b c} (C : State F3 a b c) : State F3 a b c :=
  ComputedState.union C (targetState I)

/-- Computed full initial state agrees with its proof-side specification. -/
theorem fullStart_eq_spec {I : DisplayedF3PairTriple a b c} (C : State F3 a b c) :
    fullStart (I := I) C = stateUnion C I.sourceState := by
  rw [fullStart, ComputedState.union_eq_spec, sourceState_eq_spec]

/-- Computed full terminal state agrees with its proof-side specification. -/
theorem fullFinish_eq_spec {I : DisplayedF3PairTriple a b c} (C : State F3 a b c) :
    fullFinish (I := I) C = stateUnion C I.targetState := by
  rw [fullFinish, ComputedState.union_eq_spec, targetState_eq_spec]

/-- Computed six-way placement/occupancy schedule. -/
def schedule {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c) : OuterSchedule :=
  match B.normalized.placement with
  | .targetTarget => if B.q ∈ C then .beforeResidual else .afterResidual
  | .sourceSource | .opposite => if B.q ∈ C then .afterResidual else .beforeResidual

/-- Computed residual-path start request. -/
def requestStart {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c) : State F3 a b c :=
  match schedule B C with
  | .beforeResidual => ComputedState.union
      (ComputedState.difference (fullStart (I := I) C) (outerSource B)) (outerTarget B)
  | .afterResidual => fullStart (I := I) C

/-- Computed residual-path finish request. -/
def requestFinish {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c) : State F3 a b c :=
  match schedule B C with
  | .beforeResidual => fullFinish (I := I) C
  | .afterResidual => ComputedState.union
      (ComputedState.difference (fullFinish (I := I) C) (outerTarget B)) (outerSource B)

/-- Computed schedule agrees with the proof-side six-way schedule. -/
theorem schedule_eq_spec {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c) :
    schedule B C = CertifiedFiveToFour.schedule B C := by
  classical
  unfold schedule CertifiedFiveToFour.schedule
  split <;> split <;> simp_all

/-- Computed residual start request agrees with its proof-side specification. -/
theorem requestStart_eq_spec {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c) :
    requestStart B C = CertifiedFiveToFour.requestStart B C := by
  classical
  rw [requestStart, CertifiedFiveToFour.requestStart, schedule_eq_spec]
  split
  · rw [ComputedState.union_eq_spec, ComputedState.difference_eq_spec,
      fullStart_eq_spec, outerSource_eq_spec, outerTarget_eq_spec]
  · exact fullStart_eq_spec C

/-- Computed residual finish request agrees with its proof-side specification. -/
theorem requestFinish_eq_spec {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c) :
    requestFinish B C = CertifiedFiveToFour.requestFinish B C := by
  classical
  rw [requestFinish, CertifiedFiveToFour.requestFinish, schedule_eq_spec]
  split
  · exact fullFinish_eq_spec C
  · rw [ComputedState.union_eq_spec, ComputedState.difference_eq_spec,
      fullFinish_eq_spec, outerSource_eq_spec, outerTarget_eq_spec]

/-- Transport a computed strict path across endpoint equalities without changing its data. -/
def castPath {D E D' E' : State F3 a b c} (hD : D = D') (hE : E = E')
    (path : StrictNativePath D E) : StrictNativePath D' E' := by
  subst D'
  subst E'
  exact path

/-- Construct the actual stored outer primitive from a computed initial state. -/
def outerStep {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I)
    (D : State F3 a b c) (hsource : outerSource B ⊆ D)
    (hfresh : Disjoint (outerTarget B) (ComputedState.difference D (outerSource B))) :
    StrictNativeStep D
      (ComputedState.union (ComputedState.difference D (outerSource B)) (outerTarget B)) := by
  let native : NativeReplacement (outerSource B) (outerTarget B) := by
    rw [outerSource_eq_spec, outerTarget_eq_spec]
    exact CertifiedFiveToFour.outer_native B
  let hendpoints : Disjoint (outerSource B) (outerTarget B) := by
    rw [outerSource_eq_spec, outerTarget_eq_spec]
    exact CertifiedFiveToFour.outer_endpoints_disjoint B
  refine {
    step := {
      source := outerSource B
      target := outerTarget B
      native := native
      source_subset := hsource
      target_fresh := by
        rw [ComputedState.difference_eq_spec] at hfresh
        exact hfresh
      result_eq := by
        rw [ComputedState.union_eq_spec, ComputedState.difference_eq_spec] }
    endpoints_disjoint := hendpoints
    ne := ?_ }
  intro heq
  obtain ⟨x, hxS⟩ := nativeReplacement_source_nonempty native
  have hxD : x ∈ D := hsource hxS
  have hxOut : x ∈ ComputedState.union
      (ComputedState.difference D (outerSource B)) (outerTarget B) := heq ▸ hxD
  simp only [ComputedState.union, ComputedState.difference, Finset.mem_union,
    Finset.mem_sdiff] at hxOut
  rcases hxOut with hxRest | hxT
  · exact hxRest.2 hxS
  · exact Finset.disjoint_left.mp hendpoints hxS hxT

/-- Construct the actual stored outer primitive toward a computed prescribed terminal state. -/
def outerStepTo {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I)
    (E : State F3 a b c) (htarget : outerTarget B ⊆ E)
    (hfresh : Disjoint (outerSource B) (ComputedState.difference E (outerTarget B))) :
    StrictNativeStep
      (ComputedState.union (ComputedState.difference E (outerTarget B)) (outerSource B)) E := by
  let reverseNative : NativeReplacement (outerTarget B) (outerSource B) := by
    have native := CertifiedFiveToFour.outer_native B
    rw [← outerSource_eq_spec, ← outerTarget_eq_spec] at native
    exact native.symm
  let reverseEndpoints : Disjoint (outerTarget B) (outerSource B) := by
    rw [outerSource_eq_spec, outerTarget_eq_spec]
    exact (CertifiedFiveToFour.outer_endpoints_disjoint B).symm
  let backwards : StrictNativeStep E
      (ComputedState.union (ComputedState.difference E (outerTarget B)) (outerSource B)) := by
    refine {
      step := {
        source := outerTarget B
        target := outerSource B
        native := reverseNative
        source_subset := htarget
        target_fresh := by
          rw [ComputedState.difference_eq_spec] at hfresh
          exact hfresh
        result_eq := by
          rw [ComputedState.union_eq_spec, ComputedState.difference_eq_spec] }
      endpoints_disjoint := reverseEndpoints
      ne := ?_ }
    intro heq
    obtain ⟨x, hxT⟩ := nativeReplacement_source_nonempty reverseNative
    have hxE : x ∈ E := htarget hxT
    have hxOut : x ∈ ComputedState.union
        (ComputedState.difference E (outerTarget B)) (outerSource B) := heq ▸ hxE
    simp only [ComputedState.union, ComputedState.difference, Finset.mem_union,
      Finset.mem_sdiff] at hxOut
    rcases hxOut with hxRest | hxS
    · exact hxRest.2 hxT
    · exact Finset.disjoint_left.mp reverseEndpoints hxT hxS
  exact FieldNativeExecutablePath.reverseStep backwards

/-- Computed carrier of all five displayed atoms. -/
def displayedCarrier (I : DisplayedF3PairTriple a b c) : State F3 a b c :=
  ComputedState.union (sourceState I) (targetState I)

/-- Computed displayed carrier agrees with the proof-side union. -/
theorem displayedCarrier_eq_spec (I : DisplayedF3PairTriple a b c) :
    displayedCarrier I = stateUnion I.sourceState I.targetState := by
  rw [displayedCarrier, ComputedState.union_eq_spec, sourceState_eq_spec,
    targetState_eq_spec]

private theorem before_source_q {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c)
    (hs : schedule B C = .beforeResidual) : B.q ∈ outerSource B → B.q ∈ C := by
  rw [outerSource_eq_spec]
  intro hqS
  have hp := (q_mem_outerSource_iff B).mp hqS
  cases hplace : B.normalized.placement with
  | sourceSource => simp [hplace] at hp
  | targetTarget => simpa [schedule, hplace] using hs
  | opposite => simp [hplace] at hp

private theorem before_target_q {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c)
    (hs : schedule B C = .beforeResidual) : B.q ∈ outerTarget B → B.q ∉ C := by
  rw [outerTarget_eq_spec]
  intro hqT
  have hp := (q_mem_outerTarget_iff B).mp hqT
  cases hplace : B.normalized.placement with
  | sourceSource => simpa [schedule, hplace] using hs
  | targetTarget => simp [hplace] at hp
  | opposite => simpa [schedule, hplace] using hs

private theorem after_source_q {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c)
    (hs : schedule B C = .afterResidual) : B.q ∈ outerSource B → B.q ∉ C := by
  rw [outerSource_eq_spec]
  intro hqS
  have hp := (q_mem_outerSource_iff B).mp hqS
  cases hplace : B.normalized.placement with
  | sourceSource => simp [hplace] at hp
  | targetTarget => simpa [schedule, hplace] using hs
  | opposite => simp [hplace] at hp

private theorem after_target_q {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c)
    (hs : schedule B C = .afterResidual) : B.q ∈ outerTarget B → B.q ∈ C := by
  rw [outerTarget_eq_spec]
  intro hqT
  have hp := (q_mem_outerTarget_iff B).mp hqT
  cases hplace : B.normalized.placement with
  | sourceSource => simpa [schedule, hplace] using hs
  | targetTarget => simp [hplace] at hp
  | opposite => simpa [schedule, hplace] using hs

private theorem subset_transport {S D S' D' : State F3 a b c}
    (hS : S = S') (hD : D = D') (h : S' ⊆ D') : S ⊆ D := by
  subst S'
  subst D'
  exact h

private theorem disjoint_transport {S D S' D' : State F3 a b c}
    (hS : S = S') (hD : D = D') (h : Disjoint S' D') : Disjoint S D := by
  subst S'
  subst D'
  exact h

private theorem disjoint_right_transport {S D D' : State F3 a b c}
    (hD : D = D') (h : Disjoint S D) : Disjoint S D' := by
  subst D'
  exact h

set_option diagnostics true in
set_option maxHeartbeats 1000000 in
/-- Computably splice a checked residual path with the stored actual outer primitive.
The returned packet contains computed endpoint states and the ordinary indexed strict path. -/
def execCompose {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c)
    (hC : Disjoint C (displayedCarrier I))
    (fourPath : StrictNativePath (requestStart B C) (requestFinish B C)) :
    FieldNativeExecutablePath.Packet F3 a b c := by
  have hCspec : Disjoint C (stateUnion I.sourceState I.targetState) :=
    disjoint_right_transport (S := C) (D := displayedCarrier I)
      (D' := stateUnion I.sourceState I.targetState) (displayedCarrier_eq_spec I) hC
  cases hs : schedule B C with
  | beforeResidual =>
      have hsource : outerSource B ⊆ fullStart (I := I) C :=
        subset_transport (S := outerSource B) (D := fullStart (I := I) C)
          (S' := CertifiedFiveToFour.outerSource B) (D' := stateUnion C I.sourceState)
          (outerSource_eq_spec B) (fullStart_eq_spec C)
          (source_subset_initial B C (before_source_q B C hs))
      have hfresh : Disjoint (outerTarget B)
          (ComputedState.difference (fullStart (I := I) C) (outerSource B)) := by
        let hrest : ComputedState.difference (fullStart (I := I) C) (outerSource B) =
            stateDifference (stateUnion C I.sourceState)
              (CertifiedFiveToFour.outerSource B) :=
          (ComputedState.difference_eq_spec _ _).trans
            (congrArg₂ stateDifference (fullStart_eq_spec C) (outerSource_eq_spec B))
        exact disjoint_transport (outerTarget_eq_spec B) hrest
          (target_fresh_initial B C hCspec (before_target_q B C hs))
      let first := outerStep B (fullStart (I := I) C) hsource hfresh
      let tail : StrictNativePath
          (ComputedState.union
            (ComputedState.difference (fullStart (I := I) C) (outerSource B))
            (outerTarget B))
          (fullFinish (I := I) C) := castPath
            (by simp only [requestStart, hs])
            (by simp only [requestFinish, hs]) fourPath
      exact {
        start := fullStart (I := I) C
        finish := fullFinish (I := I) C
        path := .cons first tail }
  | afterResidual =>
      have htarget : outerTarget B ⊆ fullFinish (I := I) C :=
        subset_transport (S := outerTarget B) (D := fullFinish (I := I) C)
          (S' := CertifiedFiveToFour.outerTarget B) (D' := stateUnion C I.targetState)
          (outerTarget_eq_spec B) (fullFinish_eq_spec C)
          (target_subset_final B C (after_target_q B C hs))
      have hfresh : Disjoint (outerSource B)
          (ComputedState.difference (fullFinish (I := I) C) (outerTarget B)) := by
        let hrest : ComputedState.difference (fullFinish (I := I) C) (outerTarget B) =
            stateDifference (stateUnion C I.targetState)
              (CertifiedFiveToFour.outerTarget B) :=
          (ComputedState.difference_eq_spec _ _).trans
            (congrArg₂ stateDifference (fullFinish_eq_spec C) (outerTarget_eq_spec B))
        exact disjoint_transport (outerSource_eq_spec B) hrest
          (source_fresh_final B C hCspec (after_source_q B C hs))
      let last := outerStepTo B (fullFinish (I := I) C) htarget hfresh
      let head : StrictNativePath
          (fullStart (I := I) C)
          (ComputedState.union
            (ComputedState.difference (fullFinish (I := I) C) (outerTarget B))
            (outerSource B)) := castPath
            (by simp only [requestStart, hs])
            (by simp only [requestFinish, hs]) fourPath
      exact {
        start := fullStart (I := I) C
        finish := fullFinish (I := I) C
        path := FieldNativeExecutablePath.snoc head last }

/-- Endpoint transport leaves the primitive length of a computed path unchanged. -/
theorem length_castPath {D E D' E' : State F3 a b c} (hD : D = D') (hE : E = E')
    (path : StrictNativePath D E) : Path.length (castPath hD hE path) = Path.length path := by
  subst D'
  subst E'
  rfl

set_option maxHeartbeats 10000000 in
/-- The executable splice adds exactly its stored outer native primitive. -/
theorem length_execCompose {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (C : State F3 a b c)
    (hC : Disjoint C (displayedCarrier I))
    (fourPath : StrictNativePath (requestStart B C) (requestFinish B C)) :
    Path.length (execCompose B C hC fourPath).path = Path.length fourPath + 1 := by
  unfold execCompose
  split
  · simp only [Path.length, length_castPath]
  · rw [FieldNativeExecutablePath.length_snoc, length_castPath]

end Executable

end CertifiedFiveToFour

end FieldFiveToFourContext
end BilinearComplexity
