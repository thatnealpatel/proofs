import BilinearComplexity.BinaryAmbientCarrier
import BilinearComplexity.NormalizedBinaryAllModeMove

set_option autoImplicit false

/-!
# Intrinsic moves in arbitrary binary factor spaces

The three ordered predicates below are the coordinate-free finite-set laws used
by the normalized replay: they retain every membership, collision, factor
formula, and exact replacement clause.  `AllModeMove` then exposes their six
simultaneous reorderings.  Its constructors carry intrinsic algebraic move
witnesses, not certificates emitted by an executable move compiler.
-/

namespace BilinearComplexity.BinaryAmbientMoves

open BinaryCircuit
open BinaryAmbientCarrier
open NormalizedBinaryCarrier (F2 CoordinateVector Profile)

universe u v w

variable {U : Type u} {V : Type v} {W : Type w}
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [Module F2 U] [Module F2 V] [Module F2 W]
variable [DecidableEq U] [DecidableEq V] [DecidableEq W]

/-- An intrinsic ordered first-mode Split replaces one present term by two
distinct fresh terms, preserving the other factors and splitting the first
factor additively. -/
def GeneratedFirstSplit
    (source outputLeft outputRight : Carrier U V W)
    (D E : State U V W) : Prop :=
  source ∈ D ∧
  outputLeft ≠ outputRight ∧
  outputLeft ∉ D.erase source ∧
  outputRight ∉ D.erase source ∧
  source.1.1 = outputLeft.1.1 + outputRight.1.1 ∧
  outputLeft.2.1.1 = source.2.1.1 ∧
  outputRight.2.1.1 = source.2.1.1 ∧
  outputLeft.2.2.1 = source.2.2.1 ∧
  outputRight.2.2.1 = source.2.2.1 ∧
  E = insert outputLeft (insert outputRight (D.erase source))

/-- An intrinsic ordered third-mode Flip is the displayed unit shear on an
ordered present pair.  The common third factor, freshness, and exact finite-set
replacement are all part of the law. -/
def SourceThirdFlip
    (sourceLeft sourceRight targetLeft targetRight : Carrier U V W)
    (D E : State U V W) : Prop :=
  sourceLeft ∈ D ∧
  sourceRight ∈ D ∧
  sourceLeft ≠ sourceRight ∧
  targetLeft ∉ (D.erase sourceLeft).erase sourceRight ∧
  targetRight ∉ (D.erase sourceLeft).erase sourceRight ∧
  targetLeft ≠ targetRight ∧
  sourceRight.2.2.1 = sourceLeft.2.2.1 ∧
  targetLeft.1.1 = sourceLeft.1.1 + sourceRight.1.1 ∧
  targetLeft.2.1.1 = sourceLeft.2.1.1 ∧
  targetLeft.2.2.1 = sourceLeft.2.2.1 ∧
  targetRight.1.1 = sourceRight.1.1 ∧
  targetRight.2.1.1 = sourceRight.2.1.1 - sourceLeft.2.1.1 ∧
  targetRight.2.2.1 = sourceLeft.2.2.1 ∧
  E = insert targetLeft
    (insert targetRight ((D.erase sourceLeft).erase sourceRight))

/-- An intrinsic directed narrow Reduction replaces an ordered pair sharing
its second and third factors by one fresh term whose first factor is their sum.
The relation is directed from the pair to the singleton replacement. -/
def DirectedNarrowPairReduction
    (sourceLeft sourceRight target : Carrier U V W)
    (D E : State U V W) : Prop :=
  sourceLeft ∈ D ∧
  sourceRight ∈ D ∧
  sourceLeft ≠ sourceRight ∧
  target ∉ (D.erase sourceLeft).erase sourceRight ∧
  sourceRight.2.1.1 = sourceLeft.2.1.1 ∧
  sourceRight.2.2.1 = sourceLeft.2.2.1 ∧
  target.1.1 = sourceLeft.1.1 + sourceRight.1.1 ∧
  target.2.1.1 = sourceLeft.2.1.1 ∧
  target.2.2.1 = sourceLeft.2.2.1 ∧
  E = insert target ((D.erase sourceLeft).erase sourceRight)

/-- The three intrinsic directed ordered move forms. -/
inductive Move : State U V W → State U V W → Prop
  /-- A forward first-mode Split. -/
  | generatedFirstSplit
      {source outputLeft outputRight : Carrier U V W} {D E : State U V W} :
      GeneratedFirstSplit source outputLeft outputRight D E → Move D E
  /-- An ordered third-mode Flip. -/
  | sourceThirdFlip
      {sourceLeft sourceRight targetLeft targetRight : Carrier U V W}
      {D E : State U V W} :
      SourceThirdFlip sourceLeft sourceRight targetLeft targetRight D E → Move D E
  /-- A directed narrow first-mode Reduction. -/
  | directedNarrowPairReduction
      {sourceLeft sourceRight target : Carrier U V W} {D E : State U V W} :
      DirectedNarrowPairReduction sourceLeft sourceRight target D E → Move D E

/-- Reorder a `(W,U,V)` term cyclically into `(U,V,W)`. -/
def permuteBCATerm (t : Carrier W U V) : Carrier U V W :=
  (t.2.1, t.2.2, t.1)

/-- Reorder a `(V,W,U)` term cyclically into `(U,V,W)`. -/
def permuteCABTerm (t : Carrier V W U) : Carrier U V W :=
  (t.2.2, t.1, t.2.1)

/-- Reorder a `(U,W,V)` term into `(U,V,W)`. -/
def permuteACBTerm (t : Carrier U W V) : Carrier U V W :=
  (t.1, t.2.2, t.2.1)

/-- Reorder a `(W,V,U)` term into `(U,V,W)`. -/
def permuteCBATerm (t : Carrier W V U) : Carrier U V W :=
  (t.2.2, t.2.1, t.1)

/-- Reorder a `(V,U,W)` term into `(U,V,W)`. -/
def permuteBACTerm (t : Carrier V U W) : Carrier U V W :=
  (t.2.1, t.1, t.2.2)

/-- Map a `(W,U,V)` state cyclically into the fixed ambient order `(U,V,W)`. -/
def permuteBCAState (D : State W U V) : State U V W :=
  D.image permuteBCATerm

/-- Map a `(V,W,U)` state cyclically into the fixed ambient order `(U,V,W)`. -/
def permuteCABState (D : State V W U) : State U V W :=
  D.image permuteCABTerm

/-- Map a `(U,W,V)` state into the fixed ambient order `(U,V,W)`. -/
def permuteACBState (D : State U W V) : State U V W :=
  D.image permuteACBTerm

/-- Map a `(W,V,U)` state into the fixed ambient order `(U,V,W)`. -/
def permuteCBAState (D : State W V U) : State U V W :=
  D.image permuteCBATerm

/-- Map a `(V,U,W)` state into the fixed ambient order `(U,V,W)`. -/
def permuteBACState (D : State V U W) : State U V W :=
  D.image permuteBACTerm

/-- An intrinsic ambient move in any of the six simultaneous mode orderings.
Every branch is the exact relational image of an intrinsic algebraic `Move` in
the displayed reordered ambient spaces. -/
inductive AllModeMove : State U V W → State U V W → Prop
  /-- Keep mode order `(U,V,W)`. -/
  | abc {D E : State U V W} : Move D E → AllModeMove D E
  /-- Use source order `(W,U,V)` and output order `(U,V,W)`. -/
  | bca {D₀ E₀ : State W U V} {D E : State U V W} :
      Move D₀ E₀ → D = permuteBCAState D₀ → E = permuteBCAState E₀ →
      AllModeMove D E
  /-- Use source order `(V,W,U)` and output order `(U,V,W)`. -/
  | cab {D₀ E₀ : State V W U} {D E : State U V W} :
      Move D₀ E₀ → D = permuteCABState D₀ → E = permuteCABState E₀ →
      AllModeMove D E
  /-- Use source order `(U,W,V)` and output order `(U,V,W)`. -/
  | acb {D₀ E₀ : State U W V} {D E : State U V W} :
      Move D₀ E₀ → D = permuteACBState D₀ → E = permuteACBState E₀ →
      AllModeMove D E
  /-- Use source order `(W,V,U)` and output order `(U,V,W)`. -/
  | cba {D₀ E₀ : State W V U} {D E : State U V W} :
      Move D₀ E₀ → D = permuteCBAState D₀ → E = permuteCBAState E₀ →
      AllModeMove D E
  /-- Use source order `(V,U,W)` and output order `(U,V,W)`. -/
  | bac {D₀ E₀ : State V U W} {D E : State U V W} :
      Move D₀ E₀ → D = permuteBACState D₀ → E = permuteBACState E₀ →
      AllModeMove D E

namespace Coordinate

open NormalizedBinaryCarrier
open NormalizedBinaryReplay221
open NormalizedBinaryModePermutation
open NormalizedBinaryAllModeMove

/-- On coordinate spaces, the intrinsic Split law is definitionally the
normalized Split law. -/
theorem generatedFirstSplit_iff {p : Profile}
    {source outputLeft outputRight : Carrier p} {D E : State p} :
    BinaryAmbientMoves.GeneratedFirstSplit
        (U := CoordinateVector p.first) (V := CoordinateVector p.second)
        (W := CoordinateVector p.third)
        source outputLeft outputRight D E ↔
      NormalizedBinaryReplay221.GeneratedFirstSplit
        source outputLeft outputRight D E :=
  Iff.rfl

/-- On coordinate spaces, the intrinsic Flip law is definitionally the
normalized Flip law. -/
theorem sourceThirdFlip_iff {p : Profile}
    {sourceLeft sourceRight targetLeft targetRight : Carrier p} {D E : State p} :
    BinaryAmbientMoves.SourceThirdFlip
        (U := CoordinateVector p.first) (V := CoordinateVector p.second)
        (W := CoordinateVector p.third)
        sourceLeft sourceRight targetLeft targetRight D E ↔
      NormalizedBinaryReplay221.SourceThirdFlip
        sourceLeft sourceRight targetLeft targetRight D E :=
  Iff.rfl

/-- On coordinate spaces, the intrinsic Reduction law is definitionally the
normalized directed Reduction law. -/
theorem directedNarrowPairReduction_iff {p : Profile}
    {sourceLeft sourceRight target : Carrier p} {D E : State p} :
    BinaryAmbientMoves.DirectedNarrowPairReduction
        (U := CoordinateVector p.first) (V := CoordinateVector p.second)
        (W := CoordinateVector p.third)
        sourceLeft sourceRight target D E ↔
      NormalizedBinaryReplay221.DirectedNarrowPairReduction
        sourceLeft sourceRight target D E :=
  Iff.rfl

/-- Convert an intrinsic coordinate ordered move to the normalized ordered
move with the same witnesses and direction. -/
theorem move_to_normalized {p : Profile} {D E : State p}
    (h : BinaryAmbientMoves.Move
      (U := CoordinateVector p.first) (V := CoordinateVector p.second)
      (W := CoordinateVector p.third) D E) :
    @NormalizedBinaryReplay221.Move p D E := by
  cases h with
  | generatedFirstSplit hsplit => exact .generatedFirstSplit hsplit
  | sourceThirdFlip hflip => exact .sourceThirdFlip hflip
  | directedNarrowPairReduction hreduction =>
      exact .directedNarrowPairReduction hreduction

/-- Convert a normalized ordered move to the intrinsic coordinate ordered move
with the same witnesses and direction. -/
theorem move_from_normalized {p : Profile} {D E : State p}
    (h : @NormalizedBinaryReplay221.Move p D E) :
    BinaryAmbientMoves.Move
      (U := CoordinateVector p.first) (V := CoordinateVector p.second)
      (W := CoordinateVector p.third) D E := by
  cases h with
  | generatedFirstSplit hsplit => exact .generatedFirstSplit hsplit
  | sourceThirdFlip hflip => exact .sourceThirdFlip hflip
  | directedNarrowPairReduction hreduction =>
      exact .directedNarrowPairReduction hreduction

/-- Identity-coordinate specialization: intrinsic ambient all-mode legality is
exactly normalized all-mode legality.  In particular, the intrinsic relation
introduces no additional coordinate edges. -/
theorem allModeMove_iff_normalized {p : Profile} {D E : State p} :
    BinaryAmbientMoves.AllModeMove
        (U := CoordinateVector p.first) (V := CoordinateVector p.second)
        (W := CoordinateVector p.third) D E ↔
      @NormalizedBinaryAllModeMove.AllModeMove p D E := by
  constructor
  · intro h
    rcases p with ⟨a, b, c⟩
    cases h with
    | abc hmove =>
        exact allModeMove_of_move (move_to_normalized hmove)
    | bca hmove hD hE =>
        rw [hD, hE]
        exact allModeMove_of_orientationMove
          (permuteMove .bca (move_to_normalized (p := ⟨c, a, b⟩) hmove))
    | cab hmove hD hE =>
        rw [hD, hE]
        exact allModeMove_of_orientationMove
          (permuteMove .cab (move_to_normalized (p := ⟨b, c, a⟩) hmove))
    | acb hmove hD hE =>
        rw [hD, hE]
        exact allModeMove_of_orientationMove
          (permuteMove .acb (move_to_normalized (p := ⟨a, c, b⟩) hmove))
    | cba hmove hD hE =>
        rw [hD, hE]
        exact allModeMove_of_orientationMove
          (permuteMove .cba (move_to_normalized (p := ⟨c, b, a⟩) hmove))
    | bac hmove hD hE =>
        rw [hD, hE]
        exact allModeMove_of_orientationMove
          (permuteMove .bac (move_to_normalized (p := ⟨b, a, c⟩) hmove))
  · intro h
    rcases h with ⟨q, o, rfl, hmove⟩
    have horientation : @OrientationMove q o D E := by
      simpa only [cast_eq] using hmove
    obtain ⟨D₀, E₀, hold, hD, hE⟩ := horientation.provenance
    rcases q with ⟨a, b, c⟩
    cases o with
    | abc =>
        rw [hD, hE]
        simpa [Scheme.Action.Orientation.firstDim,
          Scheme.Action.Orientation.secondDim,
          Scheme.Action.Orientation.thirdDim] using
          (BinaryAmbientMoves.AllModeMove.abc (move_from_normalized hold))
    | bca =>
        exact BinaryAmbientMoves.AllModeMove.bca
          (move_from_normalized hold) hD hE
    | cab =>
        exact BinaryAmbientMoves.AllModeMove.cab
          (move_from_normalized hold) hD hE
    | acb =>
        exact BinaryAmbientMoves.AllModeMove.acb
          (move_from_normalized hold) hD hE
    | cba =>
        exact BinaryAmbientMoves.AllModeMove.cba
          (move_from_normalized hold) hD hE
    | bac =>
        exact BinaryAmbientMoves.AllModeMove.bac
          (move_from_normalized hold) hD hE

end Coordinate

/-! Ground and specification checks. -/

open NormalizedBinaryCarrier
open NormalizedBinaryReplay221

example : GeneratedFirstSplit
    (U := CoordinateVector 2) (V := CoordinateVector 2)
    (W := CoordinateVector 1) E11 E21 E31 S0 S1 :=
  Coordinate.generatedFirstSplit_iff.mpr forwardSplit

example : SourceThirdFlip
    (U := CoordinateVector 2) (V := CoordinateVector 2)
    (W := CoordinateVector 1) E22 E31 E12 J S1 S2 :=
  Coordinate.sourceThirdFlip_iff.mpr forwardFlip

example : DirectedNarrowPairReduction
    (U := CoordinateVector 2) (V := CoordinateVector 2)
    (W := CoordinateVector 1) E21 E31 E11 S1 S0 :=
  Coordinate.directedNarrowPairReduction_iff.mpr reverseReduction

example (t : Carrier U V W) :
    permuteBCATerm (U := U) (V := V) (W := W) (t.2.2, t.1, t.2.1) = t := rfl

example (t : Carrier U V W) :
    permuteCABTerm (U := U) (V := V) (W := W) (t.2.1, t.2.2, t.1) = t := rfl

example (t : Carrier U V W) :
    permuteACBTerm (U := U) (V := V) (W := W) (t.1, t.2.2, t.2.1) = t := rfl

example (t : Carrier U V W) :
    permuteCBATerm (U := U) (V := V) (W := W) (t.2.2, t.2.1, t.1) = t := rfl

example (t : Carrier U V W) :
    permuteBACTerm (U := U) (V := V) (W := W) (t.2.1, t.1, t.2.2) = t := rfl

example : permuteBCAState (U := CoordinateVector 2) (V := CoordinateVector 2)
    (W := CoordinateVector 1) (∅ : State (CoordinateVector 1)
      (CoordinateVector 2) (CoordinateVector 2)) = ∅ := rfl

example : permuteCABState (U := CoordinateVector 2) (V := CoordinateVector 2)
    (W := CoordinateVector 1) (∅ : State (CoordinateVector 2)
      (CoordinateVector 1) (CoordinateVector 2)) = ∅ := rfl

example : permuteACBState (U := CoordinateVector 2) (V := CoordinateVector 2)
    (W := CoordinateVector 1) (∅ : State (CoordinateVector 2)
      (CoordinateVector 1) (CoordinateVector 2)) = ∅ := rfl

example : permuteCBAState (U := CoordinateVector 2) (V := CoordinateVector 2)
    (W := CoordinateVector 1) (∅ : State (CoordinateVector 1)
      (CoordinateVector 2) (CoordinateVector 2)) = ∅ := rfl

example : permuteBACState (U := CoordinateVector 2) (V := CoordinateVector 2)
    (W := CoordinateVector 1) (∅ : State (CoordinateVector 2)
      (CoordinateVector 2) (CoordinateVector 1)) = ∅ := rfl

example : Move (U := CoordinateVector 2) (V := CoordinateVector 2)
    (W := CoordinateVector 1) S0 S1 :=
  .generatedFirstSplit (Coordinate.generatedFirstSplit_iff.mpr forwardSplit)

example : AllModeMove (U := CoordinateVector 2) (V := CoordinateVector 2)
    (W := CoordinateVector 1) S0 S1 :=
  .abc (.generatedFirstSplit (Coordinate.generatedFirstSplit_iff.mpr forwardSplit))

#check @GeneratedFirstSplit
#check @SourceThirdFlip
#check @DirectedNarrowPairReduction
#check @Move
#check @AllModeMove
#check @Coordinate.allModeMove_iff_normalized
#print axioms Coordinate.allModeMove_iff_normalized

end BilinearComplexity.BinaryAmbientMoves
