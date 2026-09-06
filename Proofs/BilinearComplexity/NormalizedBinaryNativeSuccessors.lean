import Mathlib.Data.FinEnum
import BilinearComplexity.NormalizedBinaryAllModeMoveData
import BilinearComplexity.BinaryAmbientMoves
import BilinearComplexity.FiniteBoundedSearch

set_option autoImplicit false

/-!
# Complete native successor enumeration over F2 coordinates

This module constructively enumerates every tuple of normalized nonzero terms
needed by Split, Flip, and directed Reduction, packages those tuples in all six
orientations, and retains exactly the witnesses accepted by the existing
legality checker. Duplicate witnesses and endpoints are intentionally retained.
The resulting list is sound and complete for the existing normalized and
coordinate-ambient all-mode relations.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.NormalizedBinaryNativeSuccessors

open NormalizedBinaryCarrier
open NormalizedBinaryReplay221
open NormalizedBinaryModePermutation
open NormalizedBinaryAllModeMove
open NormalizedBinaryAllModeMoveData
open NormalizedBinaryAllModeMoveTransport
open Scheme.Action

private abbrev stateDecidableEq (q : Profile) : DecidableEq (State q) :=
  @Finset.decidableEq (Carrier q) inferInstance
local instance (q : Profile) : DecidableEq (State q) := stateDecidableEq q

private theorem f2_eq_zero_or_one (x : F2) : x = 0 ∨ x = 1 := by
  have hxval : x.val < 2 := ZMod.val_lt x
  have hval : x.val = 0 ∨ x.val = 1 := by omega
  rcases hval with hval | hval
  · left
    apply ZMod.val_injective
    simpa using hval
  · right
    apply ZMod.val_injective
    exact hval

local instance : FinEnum F2 :=
  FinEnum.ofList [0, 1] (by
    intro x
    rcases f2_eq_zero_or_one x with hx | hx
    · simp [hx]
    · simp [hx])

/-- Enumerate every normalized nonzero carrier term constructively. -/
private def carrierList (p : Profile) : List (Carrier p) := FinEnum.toList (Carrier p)

example : carrierList { first := 0, second := 0, third := 0 } = [] := by
  decide

/-- Enumerate every raw Split triple, Flip quadruple, and directed Reduction
triple over a normalized profile. Legality is checked only when a datum runs. -/
def allSourceMoveData (p : Profile) : List (SourceMoveData p) :=
  let terms := carrierList p
  (terms.flatMap fun source =>
    terms.flatMap fun outputLeft =>
      terms.map fun outputRight => .split source outputLeft outputRight) ++
  (terms.flatMap fun sourceLeft =>
    terms.flatMap fun sourceRight =>
      terms.flatMap fun targetLeft =>
        terms.map fun targetRight =>
          .flip sourceLeft sourceRight targetLeft targetRight) ++
  (terms.flatMap fun sourceLeft =>
    terms.flatMap fun sourceRight =>
      terms.map fun target => .reduction sourceLeft sourceRight target)

/-- Every raw source-operation datum occurs in the full tuple enumeration. -/
theorem mem_allSourceMoveData {p : Profile} (m : SourceMoveData p) :
    m ∈ allSourceMoveData p := by
  cases m with
  | split source outputLeft outputRight =>
      simp [allSourceMoveData, carrierList]
  | flip sourceLeft sourceRight targetLeft targetRight =>
      simp [allSourceMoveData, carrierList]
  | reduction sourceLeft sourceRight target =>
      simp [allSourceMoveData, carrierList]

/-- Every legal ordered normalized move has an enumerated datum whose exact
legality checker returns its target. -/
theorem sourceMoveData_complete {p : Profile} {D E : State p} (h : @Move p D E) :
    ∃ m ∈ allSourceMoveData p, m.step? D = some E := by
  cases h with
  | generatedFirstSplit hsplit =>
      rename_i source outputLeft outputRight
      rcases hsplit with ⟨hmem, hne, hfreshLeft, hfreshRight, hfirst,
        hleftSecond, hrightSecond, hleftThird, hrightThird, htarget⟩
      let m : SourceMoveData p := .split source outputLeft outputRight
      refine ⟨m, mem_allSourceMoveData m, ?_⟩
      have hlegal : m.Legal D := by
        exact ⟨hmem, hne, hfreshLeft, hfreshRight, hfirst,
          hleftSecond, hrightSecond, hleftThird, hrightThird, rfl⟩
      rw [SourceMoveData.step?_eq_some m D hlegal]
      exact congrArg some htarget.symm
  | sourceThirdFlip hflip =>
      rename_i sourceLeft sourceRight targetLeft targetRight
      rcases hflip with ⟨hleftMem, hrightMem, hsources, hfreshLeft,
        hfreshRight, htargets, hsourceThird, htargetLeftFirst,
        htargetLeftSecond, htargetLeftThird, htargetRightFirst,
        htargetRightSecond, htargetRightThird, htarget⟩
      let m : SourceMoveData p := .flip sourceLeft sourceRight targetLeft targetRight
      refine ⟨m, mem_allSourceMoveData m, ?_⟩
      have hlegal : m.Legal D := by
        exact ⟨hleftMem, hrightMem, hsources, hfreshLeft, hfreshRight,
          htargets, hsourceThird, htargetLeftFirst, htargetLeftSecond,
          htargetLeftThird, htargetRightFirst, htargetRightSecond,
          htargetRightThird, rfl⟩
      rw [SourceMoveData.step?_eq_some m D hlegal]
      exact congrArg some htarget.symm
  | directedNarrowPairReduction hreduction =>
      rename_i sourceLeft sourceRight target
      rcases hreduction with ⟨hleftMem, hrightMem, hsources, hfresh,
        hsecond, hthird, htargetFirst, htargetSecond, htargetThird, htarget⟩
      let m : SourceMoveData p := .reduction sourceLeft sourceRight target
      refine ⟨m, mem_allSourceMoveData m, ?_⟩
      have hlegal : m.Legal D := by
        exact ⟨hleftMem, hrightMem, hsources, hfresh, hsecond, hthird,
          htargetFirst, htargetSecond, htargetThird, rfl⟩
      rw [SourceMoveData.step?_eq_some m D hlegal]
      exact congrArg some htarget.symm

/-- Enumerate all source-operation data for one fixed target profile and one
orientation. -/
def fixedMoveDataAt (q : Profile) (o : Orientation) : List (FixedMoveData q) :=
  (allSourceMoveData (inversePermProfile o q)).map fun m => ⟨o, m⟩

example :
    fixedMoveDataAt { first := 0, second := 0, third := 0 } .abc = [] := by
  decide

/-- Enumerate fixed-profile witnesses in each of the six orientations, without
deduplicating alternative presentations. -/
def allFixedMoveData (q : Profile) : List (FixedMoveData q) :=
  fixedMoveDataAt q .abc ++ fixedMoveDataAt q .bca ++
  fixedMoveDataAt q .cab ++ fixedMoveDataAt q .acb ++
  fixedMoveDataAt q .cba ++ fixedMoveDataAt q .bac

/-- Every datum for an orientation occurs in that orientation's fixed list. -/
theorem mem_fixedMoveDataAt (q : Profile) (o : Orientation)
    (m : SourceMoveData (inversePermProfile o q)) :
    (⟨o, m⟩ : FixedMoveData q) ∈ fixedMoveDataAt q o := by
  simp [fixedMoveDataAt, mem_allSourceMoveData]

/-- Package source-coordinate operation data at its orientation's target
profile. -/
def fixedMoveOfSource {p : Profile} (o : Orientation) (m : SourceMoveData p) :
    FixedMoveData (permProfile o p) :=
  match o, p with
  | .abc, ⟨_, _, _⟩ => ⟨.abc, m⟩
  | .bca, ⟨_, _, _⟩ => ⟨.bca, m⟩
  | .cab, ⟨_, _, _⟩ => ⟨.cab, m⟩
  | .acb, ⟨_, _, _⟩ => ⟨.acb, m⟩
  | .cba, ⟨_, _, _⟩ => ⟨.cba, m⟩
  | .bac, ⟨_, _, _⟩ => ⟨.bac, m⟩

example {p : Profile} (m : SourceMoveData p) :
    (fixedMoveOfSource .abc m).orientation = .abc := by
  rcases p with ⟨a, b, c⟩
  rfl

/-- Packaged source data occur in the six-orientation fixed witness list. -/
theorem fixedMoveOfSource_mem {p : Profile} (o : Orientation)
    (m : SourceMoveData p) :
    fixedMoveOfSource o m ∈ allFixedMoveData (permProfile o p) := by
  rcases p with ⟨a, b, c⟩
  cases o
  · apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact mem_fixedMoveDataAt (permProfile .abc { first := a, second := b, third := c }) .abc m
  · apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_right
    exact mem_fixedMoveDataAt (permProfile .bca { first := a, second := b, third := c }) .bca m
  · apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_right
    exact mem_fixedMoveDataAt (permProfile .cab { first := a, second := b, third := c }) .cab m
  · apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_right
    exact mem_fixedMoveDataAt (permProfile .acb { first := a, second := b, third := c }) .acb m
  · apply List.mem_append_left
    apply List.mem_append_right
    exact mem_fixedMoveDataAt (permProfile .cba { first := a, second := b, third := c }) .cba m
  · apply List.mem_append_right
    exact mem_fixedMoveDataAt (permProfile .bac { first := a, second := b, third := c }) .bac m

/-- Executing packaged source data on permuted input reproduces the permuted
source execution target. -/
theorem fixedMoveOfSource_step? {p : Profile} (o : Orientation)
    (m : SourceMoveData p) {D E : State p} (hstep : m.step? D = some E) :
    (fixedMoveOfSource o m).step? (permuteState o D) =
      some (permuteState o E) := by
  rcases p with ⟨a, b, c⟩
  cases o
  · have hinverseD :
        inversePermuteState .abc (permuteState .abc D) = D := by
      have hforwardD :
          forwardState
            (q := permProfile .abc { first := a, second := b, third := c })
              .abc D = permuteState .abc D := by
        rfl
      rw [← hforwardD]
      exact inversePermuteState_forwardState
        (q := permProfile .abc { first := a, second := b, third := c })
          .abc D
    change Option.map
      (forwardState
        (q := permProfile .abc { first := a, second := b, third := c }) .abc)
      (m.step? (inversePermuteState .abc (permuteState .abc D))) =
        some (permuteState .abc E)
    rw [hinverseD, hstep]
    change Option.map (fun X : State { first := a, second := b, third := c } => permuteState .abc X)
      (some E) = some (permuteState .abc E)
    rfl
  · have hinverseD :
        inversePermuteState .bca (permuteState .bca D) = D := by
      have hforwardD :
          forwardState
            (q := permProfile .bca { first := a, second := b, third := c })
              .bca D = permuteState .bca D := by
        rfl
      rw [← hforwardD]
      exact inversePermuteState_forwardState
        (q := permProfile .bca { first := a, second := b, third := c })
          .bca D
    change Option.map
      (forwardState
        (q := permProfile .bca { first := a, second := b, third := c }) .bca)
      (m.step? (inversePermuteState .bca (permuteState .bca D))) =
        some (permuteState .bca E)
    rw [hinverseD, hstep]
    change Option.map (fun X : State { first := a, second := b, third := c } => permuteState .bca X)
      (some E) = some (permuteState .bca E)
    rfl
  · have hinverseD :
        inversePermuteState .cab (permuteState .cab D) = D := by
      have hforwardD :
          forwardState
            (q := permProfile .cab { first := a, second := b, third := c })
              .cab D = permuteState .cab D := by
        rfl
      rw [← hforwardD]
      exact inversePermuteState_forwardState
        (q := permProfile .cab { first := a, second := b, third := c })
          .cab D
    change Option.map
      (forwardState
        (q := permProfile .cab { first := a, second := b, third := c }) .cab)
      (m.step? (inversePermuteState .cab (permuteState .cab D))) =
        some (permuteState .cab E)
    rw [hinverseD, hstep]
    change Option.map (fun X : State { first := a, second := b, third := c } => permuteState .cab X)
      (some E) = some (permuteState .cab E)
    rfl
  · have hinverseD :
        inversePermuteState .acb (permuteState .acb D) = D := by
      have hforwardD :
          forwardState
            (q := permProfile .acb { first := a, second := b, third := c })
              .acb D = permuteState .acb D := by
        rfl
      rw [← hforwardD]
      exact inversePermuteState_forwardState
        (q := permProfile .acb { first := a, second := b, third := c })
          .acb D
    change Option.map
      (forwardState
        (q := permProfile .acb { first := a, second := b, third := c }) .acb)
      (m.step? (inversePermuteState .acb (permuteState .acb D))) =
        some (permuteState .acb E)
    rw [hinverseD, hstep]
    change Option.map (fun X : State { first := a, second := b, third := c } => permuteState .acb X)
      (some E) = some (permuteState .acb E)
    rfl
  · have hinverseD :
        inversePermuteState .cba (permuteState .cba D) = D := by
      have hforwardD :
          forwardState
            (q := permProfile .cba { first := a, second := b, third := c })
              .cba D = permuteState .cba D := by
        rfl
      rw [← hforwardD]
      exact inversePermuteState_forwardState
        (q := permProfile .cba { first := a, second := b, third := c })
          .cba D
    change Option.map
      (forwardState
        (q := permProfile .cba { first := a, second := b, third := c }) .cba)
      (m.step? (inversePermuteState .cba (permuteState .cba D))) =
        some (permuteState .cba E)
    rw [hinverseD, hstep]
    change Option.map (fun X : State { first := a, second := b, third := c } => permuteState .cba X)
      (some E) = some (permuteState .cba E)
    rfl
  · have hinverseD :
        inversePermuteState .bac (permuteState .bac D) = D := by
      have hforwardD :
          forwardState
            (q := permProfile .bac { first := a, second := b, third := c })
              .bac D = permuteState .bac D := by
        rfl
      rw [← hforwardD]
      exact inversePermuteState_forwardState
        (q := permProfile .bac { first := a, second := b, third := c })
          .bac D
    change Option.map
      (forwardState
        (q := permProfile .bac { first := a, second := b, third := c }) .bac)
      (m.step? (inversePermuteState .bac (permuteState .bac D))) =
        some (permuteState .bac E)
    rw [hinverseD, hstep]
    change Option.map (fun X : State { first := a, second := b, third := c } => permuteState .bac X)
      (some E) = some (permuteState .bac E)
    rfl

/-- Every normalized all-mode edge has an enumerated fixed witness whose exact
checker returns the edge target. -/
theorem fixedMoveData_complete {q : Profile} {D E : State q} (h : @AllModeMove q D E) :
    ∃ w ∈ allFixedMoveData q, w.step? D = some E := by
  obtain ⟨p, o, hp, D₀, E₀, hmove, hD, hE⟩ := h.provenance
  obtain ⟨m, hm, hstep⟩ := sourceMoveData_complete hmove
  let w := fixedMoveOfSource o m
  refine ⟨cast (congrArg FixedMoveData hp) w, ?_, ?_⟩
  · subst q
    simpa only [cast_eq] using fixedMoveOfSource_mem o m
  · subst q
    have hD' : D = permuteState o D₀ := by simpa using hD
    have hE' : E = permuteState o E₀ := by simpa using hE
    subst D
    subst E
    simpa only [cast_eq, w] using fixedMoveOfSource_step? o m hstep

/-- Enumerate every successful fixed-profile witness execution from `D`.
Duplicate endpoints and duplicate witness presentations are intentionally retained. -/
def successors {p : Profile} (D : State p) : List (State p) :=
  (allFixedMoveData p).filterMap fun w => w.step? D

/-- Every state emitted by `successors` is related to its input by the existing
six-orientation normalized all-mode move relation. -/
theorem successors_sound {p : Profile} {D E : State p}
    (hE : E ∈ successors D) : @AllModeMove p D E := by
  obtain ⟨w, hw, hstep⟩ := List.mem_filterMap.mp hE
  exact w.step?_sound hstep

/-- Every normalized all-mode move, in every orientation and presentation,
is emitted by `successors`. -/
theorem successors_complete {p : Profile} {D E : State p}
    (h : @AllModeMove p D E) : E ∈ successors D := by
  obtain ⟨w, hw, hstep⟩ := fixedMoveData_complete h
  exact List.mem_filterMap.mpr ⟨w, hw, hstep⟩

/-- Membership in the executable successor list is exactly normalized
six-orientation all-mode legality. -/
theorem mem_successors_iff {p : Profile} {D E : State p} :
    E ∈ successors D ↔ @AllModeMove p D E :=
  ⟨successors_sound, successors_complete⟩

/-- Membership in the executable normalized successor list is exactly the
intrinsic ambient all-mode relation on coordinate factor spaces. -/
theorem mem_successors_iff_ambient {p : Profile} {D E : State p} :
    E ∈ successors D ↔
      BinaryAmbientMoves.AllModeMove
        (U := CoordinateVector p.first) (V := CoordinateVector p.second)
        (W := CoordinateVector p.third) D E := by
  rw [mem_successors_iff]
  exact BinaryAmbientMoves.Coordinate.allModeMove_iff_normalized.symm

/-- Convert the complete endpoint list into the witness-bearing interface used
by the generic bounded-search layer. -/
def certifiedSuccessors {p : Profile} (D : State p) :
    List (FiniteBoundedSearch.Successor (@AllModeMove p) D) :=
  (successors D).attach.map fun E =>
    { finish := E.1
      edge := successors_sound E.2 }

/-- A state is the endpoint of an emitted witness-bearing successor exactly
when it is related to the source by a normalized all-mode move. -/
theorem exists_mem_certifiedSuccessors_iff {p : Profile} {D E : State p} :
    (∃ edge ∈ certifiedSuccessors D, edge.finish = E) ↔
      @AllModeMove p D E := by
  constructor
  · rintro ⟨edge, hedge, hfinish⟩
    rw [← hfinish]
    exact edge.edge
  · intro hmove
    let endpoint : {X // X ∈ successors D} :=
      ⟨E, successors_complete hmove⟩
    refine ⟨{ finish := endpoint.1, edge := successors_sound endpoint.2 }, ?_, rfl⟩
    exact List.mem_map.mpr ⟨endpoint, List.mem_attach _ endpoint, rfl⟩

/-- The witness-bearing adapter preserves the number and order of emitted
endpoints. -/
theorem certifiedSuccessors_length {p : Profile} (D : State p) :
    (certifiedSuccessors D).length = (successors D).length := by
  simp only [certifiedSuccessors, List.length_map, List.length_attach]

example :
    (allSourceMoveData { first := 0, second := 0, third := 0 }).length = 0 := by
  decide

example :
    (allFixedMoveData { first := 0, second := 0, third := 0 }).length = 0 := by
  decide

example :
    successors (∅ : State { first := 0, second := 0, third := 0 }) = [] := by
  decide

example : S1 ∈ successors S0 := by
  apply successors_complete
  exact allModeMove_of_move (.generatedFirstSplit forwardSplit)

#eval (successors S0).length

#check @allSourceMoveData
#check @allFixedMoveData
#check @fixedMoveData_complete
#check @successors
#check @successors_sound
#check @successors_complete
#check @mem_successors_iff
#check @mem_successors_iff_ambient
#check @certifiedSuccessors
#check @exists_mem_certifiedSuccessors_iff

#print axioms mem_successors_iff
#print axioms mem_successors_iff_ambient
#print axioms exists_mem_certifiedSuccessors_iff

end BilinearComplexity.NormalizedBinaryNativeSuccessors
