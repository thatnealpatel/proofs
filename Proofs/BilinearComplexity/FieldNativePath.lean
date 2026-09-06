import BilinearComplexity.FieldNativeMoves

set_option autoImplicit false

namespace BilinearComplexity
namespace FieldNativePath

open FieldRankOne FieldContextual FieldNativeMoves

variable {k : Type*} {a b c : ℕ} [Field k]

/-- A strict native step is state-changing and has disjoint local source and target carriers.
The explicit local condition excludes self-loop and partially overlapping Flip presentations. -/
structure StrictNativeStep (D E : State k a b c) where
  /-- Underlying exact field-native step. -/
  step : NativeStep D E
  /-- No evaluated atom is both removed and inserted. -/
  endpoints_disjoint : Disjoint step.source step.target
  /-- The global state changes. -/
  ne : D ≠ E

/-- Strictness is preserved when a step is reversed. -/
def StrictNativeStep.reverse {D E : State k a b c}
    (h : StrictNativeStep D E) : StrictNativeStep E D := by
  rcases h with ⟨step, endpoints_disjoint, hne⟩
  refine {
    step := step.reverse
    endpoints_disjoint := ?_
    ne := hne.symm }
  rw [NativeStep.reverse_source step, NativeStep.reverse_target step]
  exact endpoints_disjoint.symm

/-- Complementing inside a finite carrier transports a strict step contravariantly. The
local relation is the coefficient-correct inverse of the reversed step, and disjointness
explicitly rules out self-loop Flip templates. -/
noncomputable def StrictNativeStep.complement {D E P : State k a b c}
    (h : StrictNativeStep D E) (hDP : D ⊆ P) (hEP : E ⊆ P) :
    StrictNativeStep (stateDifference P E) (stateDifference P D) := by
  have hdisjoint := h.endpoints_disjoint
  rw [Finset.disjoint_left] at hdisjoint
  have hsource_subset : h.step.source ⊆ stateDifference P E := by
    intro x hxSource
    have hxD := h.step.source_subset hxSource
    have hxP := hDP hxD
    simp only [stateDifference, Finset.mem_sdiff]
    refine ⟨hxP, ?_⟩
    intro hxE
    rw [h.step.result_eq] at hxE
    simp only [stateUnion, Finset.mem_union] at hxE
    rcases hxE with hxUnchanged | hxTarget
    · simp only [stateDifference, Finset.mem_sdiff] at hxUnchanged
      exact hxUnchanged.2 hxSource
    · exact hdisjoint hxSource hxTarget
  have htarget_fresh :
      Disjoint h.step.target (stateDifference (stateDifference P E) h.step.source) := by
    classical
    rw [Finset.disjoint_left]
    intro x hxTarget hxOutside
    simp only [stateDifference, Finset.mem_sdiff] at hxOutside
    exact hxOutside.1.2 (by
      rw [h.step.result_eq]
      simp only [stateUnion, Finset.mem_union]
      exact Or.inr hxTarget)
  have hresult :
      stateDifference P D = stateUnion
        (stateDifference (stateDifference P E) h.step.source) h.step.target := by
    classical
    ext x
    simp only [stateDifference, stateUnion, Finset.mem_sdiff, Finset.mem_union]
    constructor
    · intro hx
      by_cases hxTarget : x ∈ h.step.target
      · exact Or.inr hxTarget
      · refine Or.inl ⟨⟨hx.1, ?_⟩, ?_⟩
        · intro hxE
          rw [h.step.result_eq] at hxE
          simp only [stateUnion, Finset.mem_union] at hxE
          rcases hxE with hxUnchanged | hxTarget'
          · simp only [stateDifference, Finset.mem_sdiff] at hxUnchanged
            exact hx.2 hxUnchanged.1
          · exact hxTarget hxTarget'
        · intro hxSource
          exact hx.2 (h.step.source_subset hxSource)
    · rintro (hx | hxTarget)
      · refine ⟨hx.1.1, ?_⟩
        intro hxD
        by_cases hxSource : x ∈ h.step.source
        · exact hx.2 hxSource
        · apply hx.1.2
          rw [h.step.result_eq]
          simp only [stateUnion, Finset.mem_union]
          simp only [stateDifference, Finset.mem_sdiff]
          exact Or.inl ⟨hxD, hxSource⟩
      · refine ⟨hEP ?_, ?_⟩
        · rw [h.step.result_eq]
          simp only [stateUnion, Finset.mem_union]
          exact Or.inr hxTarget
        · intro hxD
          by_cases hxSource : x ∈ h.step.source
          · exact hdisjoint hxSource hxTarget
          · have hxUnchanged : x ∈ stateDifference D h.step.source := by
              simp only [stateDifference, Finset.mem_sdiff]
              exact ⟨hxD, hxSource⟩
            have htargetFresh := h.step.target_fresh
            rw [Finset.disjoint_left] at htargetFresh
            exact htargetFresh hxTarget hxUnchanged
  refine {
    step := {
      source := h.step.source
      target := h.step.target
      native := h.step.native
      source_subset := hsource_subset
      target_fresh := htarget_fresh
      result_eq := hresult }
    endpoints_disjoint := h.endpoints_disjoint
    ne := ?_ }
  intro heq
  apply h.ne
  classical
  ext x
  have hcomp := congrArg (fun S => x ∈ S) heq
  simp only [stateDifference, Finset.mem_sdiff] at hcomp
  by_cases hxP : x ∈ P
  · tauto
  · constructor <;> intro hx
    · exact False.elim (hxP (hDP hx))
    · exact False.elim (hxP (hEP hx))

/-- A finite strict native path is a list of states with a strict native step between
successive entries. -/
inductive StrictNativePath : State k a b c → State k a b c → Type _
  | nil (D : State k a b c) : StrictNativePath D D
  | cons {D E F : State k a b c} :
      StrictNativeStep D E → StrictNativePath E F → StrictNativePath D F

/-- A carrier-bounded strict native path stores the subset proof at every vertex. -/
inductive CarrierPath (P : State k a b c) : State k a b c → State k a b c → Type _
  | nil (D : State k a b c) (hD : D ⊆ P) : CarrierPath P D D
  | cons {D E F : State k a b c} (hD : D ⊆ P) :
      StrictNativeStep D E → CarrierPath P E F → CarrierPath P D F

/-- The initial vertex of a carrier-bounded path lies in its carrier. -/
theorem CarrierPath.start_subset {P D E : State k a b c} (path : CarrierPath P D E) :
    D ⊆ P := by
  cases path with
  | nil _ hD => exact hD
  | cons hD _ _ => exact hD


/-- The terminal vertex of a carrier-bounded path lies in its carrier. -/
theorem CarrierPath.end_subset {P D E : State k a b c} (path : CarrierPath P D E) :
    E ⊆ P := by
  induction path with
  | nil _ hD => exact hD
  | cons _ _ _ ih => exact ih

/-- Append one strict step to a carrier-bounded path. -/
noncomputable def CarrierPath.snoc {P D E F : State k a b c} (path : CarrierPath P D E)
    (last : StrictNativeStep E F) (hF : F ⊆ P) : CarrierPath P D F := by
  induction path generalizing F with
  | nil E hE => exact .cons hE last (.nil F hF)
  | cons hD first tail ih => exact .cons hD first (ih last hF)

/-- Complement every vertex of a carrier-bounded strict path and reverse its order.
Only strict locally disjoint steps are transported, so no self-loop Flip is asserted to
have a complement edge. -/
noncomputable def CarrierPath.complement {P D E : State k a b c}
    (path : CarrierPath P D E) :
    CarrierPath P (stateDifference P E) (stateDifference P D) := by
  induction path with
  | nil D hD =>
      exact .nil (stateDifference P D) (by
        classical
        exact Finset.sdiff_subset)
  | @cons D E F hD step tail ih =>
      exact ih.snoc (step.complement hD tail.start_subset) (by
        classical
        exact Finset.sdiff_subset)

#check @StrictNativeStep.reverse
#check @StrictNativeStep.complement
#check @CarrierPath.complement
#print axioms StrictNativeStep.complement
#print axioms CarrierPath.complement

end FieldNativePath
end BilinearComplexity
