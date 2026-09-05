import BilinearComplexity.NormalizedBinaryAllModeMoveData

set_option autoImplicit false

/-!
# Guarded contextual move certificates

This module is the proof-producing kernel for compact contextual certificates.
A template records a short list of existing `FixedMoveData` witnesses and only
those initial occupancy bits read by that list.  A decision tree branches on
context membership.  Its coverage proof is structural: every branch reaches a
leaf whose guard follows from the tested bits.  No enumeration of all ambient
contexts and no native-code evaluator enters the trusted argument.
-/

namespace BilinearComplexity.NormalizedBinaryContextualKernel

open BinaryCircuit
open NormalizedBinaryCarrier
open NormalizedBinaryReplay221
open NormalizedBinaryModePermutation
open NormalizedBinaryAllModeMove
open NormalizedBinaryAllModeMoveTransport
open NormalizedBinaryAllModeMoveData
open Scheme.Action

private abbrev stateDecidableEq (q : Profile) : DecidableEq (State q) :=
  @Finset.decidableEq (Carrier q) inferInstance

local instance (q : Profile) : DecidableEq (State q) := stateDecidableEq q

/-- The terms whose occupancy is read or changed by source-coordinate move data. -/
def sourceMoveSupport {p : Profile} (m : SourceMoveData p) : State p :=
  match m with
  | .split source outputLeft outputRight => {source, outputLeft, outputRight}
  | .flip sourceLeft sourceRight targetLeft targetRight =>
      {sourceLeft, sourceRight, targetLeft, targetRight}
  | .reduction sourceLeft sourceRight target =>
      {sourceLeft, sourceRight, target}

example : sourceMoveSupport
    (.split E11 E21 E31 : SourceMoveData profile221) = {E11, E21, E31} := rfl

/-- Adding terms disjoint from a source move's support commutes with its exact
finite-set target operation. -/
theorem SourceMoveData.target_union_of_disjoint {p : Profile}
    (m : SourceMoveData p) (D R : State p)
    (hR : Disjoint R (sourceMoveSupport m)) :
    m.target (D ∪ R) = m.target D ∪ R := by
  cases m with
  | split source outputLeft outputRight =>
      simp only [sourceMoveSupport, Finset.disjoint_insert_right,
        Finset.disjoint_singleton_right] at hR
      simp only [SourceMoveData.target, Finset.erase_union_distrib,
        Finset.erase_eq_self.mpr hR.1, Finset.insert_union]
  | flip sourceLeft sourceRight targetLeft targetRight =>
      simp only [sourceMoveSupport, Finset.disjoint_insert_right,
        Finset.disjoint_singleton_right] at hR
      simp only [SourceMoveData.target, Finset.erase_union_distrib,
        Finset.erase_eq_self.mpr hR.1,
        Finset.erase_eq_self.mpr hR.2.1, Finset.insert_union]
  | reduction sourceLeft sourceRight target =>
      simp only [sourceMoveSupport, Finset.disjoint_insert_right,
        Finset.disjoint_singleton_right] at hR
      simp only [SourceMoveData.target, Finset.erase_union_distrib,
        Finset.erase_eq_self.mpr hR.1,
        Finset.erase_eq_self.mpr hR.2.1, Finset.insert_union]

/-- Source move legality is unchanged by adding terms disjoint from every
source and target named by the witness. -/
theorem SourceMoveData.legal_union_iff_of_disjoint {p : Profile}
    (m : SourceMoveData p) (D R : State p)
    (hR : Disjoint R (sourceMoveSupport m)) :
    m.Legal (D ∪ R) ↔ m.Legal D := by
  cases m <;>
    simp only [sourceMoveSupport, Finset.disjoint_insert_right,
      Finset.disjoint_singleton_right] at hR <;>
    simp [SourceMoveData.Legal, GeneratedFirstSplit, SourceThirdFlip,
      DirectedNarrowPairReduction, hR]

/-- Deterministic source execution commutes with adjoining a background
which is disjoint from the witness support. -/
theorem SourceMoveData.step?_union_of_disjoint {p : Profile}
    (m : SourceMoveData p) (D R : State p)
    (hR : Disjoint R (sourceMoveSupport m)) :
    m.step? (D ∪ R) = (m.step? D).map (fun E => E ∪ R) := by
  have hlegal := SourceMoveData.legal_union_iff_of_disjoint m D R hR
  by_cases h : m.Legal D
  · have hunion : m.Legal (D ∪ R) := hlegal.mpr h
    simp only [SourceMoveData.step?, h, hunion, if_true, Option.map_some,
      SourceMoveData.target_union_of_disjoint m D R hR]
  · have hunion : ¬m.Legal (D ∪ R) := fun h' => h (hlegal.mp h')
    simp only [SourceMoveData.step?, h, hunion, if_false, Option.map_none]

/-- The target-coordinate support of fixed-profile move data. -/
def fixedMoveSupport {q : Profile} (w : FixedMoveData q) : State q :=
  forwardState w.orientation (sourceMoveSupport w.sourceMove)

example : fixedMoveSupport forwardSplitMoveData221 = {E11, E21, E31} := by
  decide

/-- Inverse permutation of terms is injective. -/
theorem inversePermuteTerm_injective {q : Profile} (o : Orientation) :
    Function.Injective (@inversePermuteTerm q o) := by
  intro x y h
  have hpull := congrArg
    (fun t => cast (congrArg Carrier (permProfile_inversePermProfile o q))
      (permuteTerm o t)) h
  simpa only [cast_permuteTerm_inversePermuteTerm] using hpull

/-- Pulling a union back through an orientation distributes over the union. -/
theorem inversePermuteState_union {q : Profile} (o : Orientation)
    (D R : State q) :
    inversePermuteState o (D ∪ R) =
      inversePermuteState o D ∪ inversePermuteState o R := by
  exact Finset.image_union D R

/-- Casting a state along a profile equality distributes over union. -/
theorem cast_state_union {p q : Profile} (h : p = q) (D R : State p) :
    cast (congrArg State h) (D ∪ R) =
      cast (congrArg State h) D ∪ cast (congrArg State h) R := by
  subst q
  rfl

/-- Pushing a union forward through an orientation distributes over the union. -/
theorem forwardState_union {q : Profile} (o : Orientation)
    (D R : State (inversePermProfile o q)) :
    forwardState o (D ∪ R) = forwardState o D ∪ forwardState o R := by
  unfold forwardState permuteState
  rw [Finset.image_union,
    cast_state_union (permProfile_inversePermProfile o q)]

/-- Target-coordinate disjointness from a fixed witness support pulls back to
source-coordinate disjointness. -/
theorem inversePermuteState_disjoint_sourceMoveSupport {q : Profile}
    (w : FixedMoveData q) (R : State q)
    (hR : Disjoint R (fixedMoveSupport w)) :
    Disjoint (inversePermuteState w.orientation R)
      (sourceMoveSupport w.sourceMove) := by
  have himage := (Finset.disjoint_image
    (inversePermuteTerm_injective w.orientation)).mpr hR
  change Disjoint (inversePermuteState w.orientation R)
    (inversePermuteState w.orientation (fixedMoveSupport w)) at himage
  simpa only [fixedMoveSupport, inversePermuteState_forwardState] using himage

/-- Deterministic fixed-profile execution commutes with adjoining a background
which is disjoint from the target-coordinate witness support. -/
theorem FixedMoveData.step?_union_of_disjoint {q : Profile}
    (w : FixedMoveData q) (D R : State q)
    (hR : Disjoint R (fixedMoveSupport w)) :
    w.step? (D ∪ R) = (w.step? D).map (fun E => E ∪ R) := by
  unfold FixedMoveData.step?
  rw [inversePermuteState_union]
  rw [SourceMoveData.step?_union_of_disjoint w.sourceMove _ _
    (inversePermuteState_disjoint_sourceMoveSupport w R hR)]
  cases w.sourceMove.step? (inversePermuteState w.orientation D) <;>
    simp only [Option.map_none, Option.map_some, forwardState_union,
      forwardState_inversePermuteState]

/-- A fixed witness executes when its source-coordinate legality and exact
forward target are supplied separately.  This form keeps finite generated
replay proofs small and kernel-reducible. -/
theorem FixedMoveData.step?_eq_some_of_source {q : Profile}
    (w : FixedMoveData q) (D E : State q)
    (hlegal : w.sourceMove.Legal (inversePermuteState w.orientation D))
    (htarget : forwardState w.orientation
      (w.sourceMove.target (inversePermuteState w.orientation D)) = E) :
    w.step? D = some E := by
  unfold FixedMoveData.step?
  rw [SourceMoveData.step?_eq_some _ _ hlegal]
  simpa only [Option.map_some] using congrArg some htarget

/-- The union of all target-coordinate supports read or changed by a witness list. -/
def pathSupport {q : Profile} : List (FixedMoveData q) → State q
  | [] => ∅
  | w :: ws => fixedMoveSupport w ∪ pathSupport ws

example {q : Profile} : pathSupport ([] : List (FixedMoveData q)) = ∅ := rfl

/-- Replaying a fixed witness list commutes with adjoining a background disjoint
from every move support in the list. -/
theorem run?_union_of_disjoint {q : Profile} (ws : List (FixedMoveData q))
    (D R : State q) (hR : Disjoint R (pathSupport ws)) :
    run? (D ∪ R) ws = (run? D ws).map (fun E => E ∪ R) := by
  induction ws generalizing D with
  | nil => simp only [run?, Option.map_some]
  | cons w ws ih =>
      simp only [pathSupport, Finset.disjoint_union_right] at hR
      simp only [run?, FixedMoveData.step?_union_of_disjoint w D R hR.1]
      cases hstep : w.step? D with
      | none => simp only [Option.map_none, Option.bind_none]
      | some E =>
          simp only [Option.map_some, Option.bind_some]
          rw [ih E hR.2]

/-- A guarded template stores an actual native witness list, its complete
non-endpoint occupancy guard, and kernel proofs of support and base replay. -/
structure ContextualPathTemplate (q : Profile) (start finish : State q) where
  /-- Existing proof-producing fixed move witnesses. -/
  moves : List (FixedMoveData q)
  /-- Support terms required to occur in the initial context. -/
  present : State q
  /-- Support terms required not to occur in the initial context. -/
  absent : State q
  /-- The guard accounts for every non-endpoint term touched by the list. -/
  support_eq : pathSupport moves = start ∪ finish ∪ present ∪ absent
  /-- Replay succeeds on the small occupied part of the support. -/
  replay : run? (start ∪ present) moves = some (finish ∪ present)

/-- A guarded template replays in every irrelevant background, temporarily
borrowing local context terms while restoring them at the endpoint. -/
theorem ContextualPathTemplate.run_context {q : Profile}
    {start finish C : State q}
    (t : ContextualPathTemplate q start finish)
    (hCZ : Disjoint C (start ∪ finish))
    (hpresent : t.present ⊆ C) (habsent : Disjoint C t.absent) :
    run? (C ∪ start) t.moves = some (C ∪ finish) := by
  let R := C \ pathSupport t.moves
  have hcontext : C = t.present ∪ R := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, R]
    constructor
    · intro hxC
      by_cases hxS : x ∈ pathSupport t.moves
      · rw [t.support_eq] at hxS
        simp only [Finset.mem_union] at hxS
        rcases hxS with ((hxStart | hxFinish) | hxPresent) | hxAbsent
        · exact False.elim ((Finset.disjoint_left.mp hCZ) hxC
            (Finset.mem_union_left finish hxStart))
        · exact False.elim ((Finset.disjoint_left.mp hCZ) hxC
            (Finset.mem_union_right start hxFinish))
        · exact Or.inl hxPresent
        · exact False.elim
            ((Finset.disjoint_left.mp habsent) hxC hxAbsent)
      · exact Or.inr ⟨hxC, hxS⟩
    · intro hx
      rcases hx with hxPresent | hxR
      · exact hpresent hxPresent
      · exact hxR.1
  have hR : Disjoint R (pathSupport t.moves) := Finset.sdiff_disjoint
  have hstart : C ∪ start = (start ∪ t.present) ∪ R := by
    rw [hcontext]
    ac_rfl
  have hfinish : C ∪ finish = (finish ∪ t.present) ∪ R := by
    rw [hcontext]
    ac_rfl
  rw [hstart, run?_union_of_disjoint t.moves (start ∪ t.present) R hR,
    t.replay, Option.map_some, hfinish]

/-- A total occupancy decision tree whose leaves carry guarded native paths of
one prescribed constructed length.  The absent child is chosen when the tested
context term is absent and the present child otherwise.  The length parameter
does not assert shortestness. -/
inductive ContextualDecisionTree (q : Profile) (start finish : State q)
    (distance : Nat) where
  | leaf (template : ContextualPathTemplate q start finish)
      (length_eq : template.moves.length = distance)
  | branch (term : Carrier q)
      (absent present : ContextualDecisionTree q start finish distance)

/-- Execute the decision tree and return its selected native witness list. -/
def ContextualDecisionTree.selectMoves {q : Profile} {start finish : State q}
    {distance : Nat} (C : State q) :
    ContextualDecisionTree q start finish distance → List (FixedMoveData q)
  | .leaf template _ => template.moves
  | .branch term absent present =>
      if term ∈ C then selectMoves C present else selectMoves C absent

example {q : Profile} {start finish : State q}
    (t : ContextualPathTemplate q start finish) (h : t.moves.length = 2)
    (C : State q) :
    (ContextualDecisionTree.leaf t h).selectMoves C = t.moves := rfl

/-- Structural coverage: every leaf guard is implied by the context-membership
facts accumulated on the route from the root. -/
def ContextualDecisionTree.Valid {q : Profile} {start finish : State q}
    {distance : Nat} : ContextualDecisionTree q start finish distance →
      State q → State q → Prop
  | .leaf template _, knownPresent, knownAbsent =>
      template.present ⊆ knownPresent ∧ template.absent ⊆ knownAbsent
  | .branch term absent present, knownPresent, knownAbsent =>
      absent.Valid knownPresent (insert term knownAbsent) ∧
        present.Valid (insert term knownPresent) knownAbsent

example {q : Profile} {start finish : State q}
    (t : ContextualPathTemplate q start finish) (h : t.moves.length = 2) :
    (ContextualDecisionTree.leaf t h).Valid t.present t.absent := by
  exact ⟨Finset.Subset.rfl, Finset.Subset.rfl⟩

/-- A structurally valid tree selects a witness list which replays for every
context disjoint from the two endpoints. -/
theorem ContextualDecisionTree.selectMoves_run? {q : Profile}
    {start finish C : State q} {distance : Nat}
    (tree : ContextualDecisionTree q start finish distance) (P N : State q)
    (hvalid : tree.Valid P N) (hP : P ⊆ C) (hN : Disjoint C N)
    (hCZ : Disjoint C (start ∪ finish)) :
    run? (C ∪ start) (tree.selectMoves C) = some (C ∪ finish) := by
  induction tree generalizing P N with
  | leaf template hlength =>
      simp only [ContextualDecisionTree.Valid] at hvalid
      exact template.run_context hCZ (hvalid.1.trans hP)
        (hN.mono_right hvalid.2)
  | branch term absent present ihAbsent ihPresent =>
      simp only [ContextualDecisionTree.Valid] at hvalid
      simp only [ContextualDecisionTree.selectMoves]
      by_cases hterm : term ∈ C
      · simp only [hterm, if_true]
        apply ihPresent (insert term P) N hvalid.2
        · intro x hx
          simp only [Finset.mem_insert] at hx
          exact hx.elim (fun h => h ▸ hterm) (fun hxP => hP hxP)
        · exact hN
      · simp only [hterm, if_false]
        apply ihAbsent P (insert term N) hvalid.1 hP
        exact Finset.disjoint_insert_right.mpr ⟨hterm, hN⟩

/-- Every selected witness list has the prescribed length parameter carried by
the tree. -/
theorem ContextualDecisionTree.selectMoves_length {q : Profile}
    {start finish : State q} {distance : Nat}
    (tree : ContextualDecisionTree q start finish distance) (C : State q) :
    (tree.selectMoves C).length = distance := by
  induction tree with
  | leaf template h => exact h
  | branch term absent present ihAbsent ihPresent =>
      simp only [ContextualDecisionTree.selectMoves]
      split
      · exact ihPresent
      · exact ihAbsent

/-- Compile a structurally covered contextual tree to an actual dependent
`AllModeMove` path.  This is executable apart from its erased proof inputs. -/
def ContextualDecisionTree.toMovePath {q : Profile}
    {start finish C : State q} {distance : Nat}
    (tree : ContextualDecisionTree q start finish distance)
    (hvalid : tree.Valid ∅ ∅) (hCZ : Disjoint C (start ∪ finish)) :
    MovePath (@AllModeMove q) (C ∪ start) (C ∪ finish) :=
  run?_path (tree.selectMoves_run? ∅ ∅ hvalid
    (Finset.empty_subset C) (Finset.disjoint_empty_right C) hCZ)

/-- The compiled dependent path has the prescribed constructed path length. -/
@[simp] theorem ContextualDecisionTree.toMovePath_length {q : Profile}
    {start finish C : State q} {distance : Nat}
    (tree : ContextualDecisionTree q start finish distance)
    (hvalid : tree.Valid ∅ ∅) (hCZ : Disjoint C (start ∪ finish)) :
    (tree.toMovePath hvalid hCZ).length = distance := by
  rw [ContextualDecisionTree.toMovePath, run?_path_length,
    tree.selectMoves_length]

#print axioms SourceMoveData.step?_union_of_disjoint
#print axioms ContextualPathTemplate.run_context
#print axioms ContextualDecisionTree.selectMoves_run?
#print axioms ContextualDecisionTree.toMovePath_length

end BilinearComplexity.NormalizedBinaryContextualKernel
