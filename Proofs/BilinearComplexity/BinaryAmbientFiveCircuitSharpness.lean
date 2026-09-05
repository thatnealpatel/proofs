import BilinearComplexity.BinaryAmbientMoves
import BilinearComplexity.NormalizedBinaryFiveCircuitSharpness

set_option autoImplicit false

/-!
# Intrinsic ambient sharpness for the selected profile-411 circuit

The normalized row `411-01` lives definitionally in the actual coordinate
factor spaces `Fin 4 → F2`, `Fin 1 → F2`, and `Fin 1 → F2`.  The identity
coordinate equivalence for intrinsic `AllModeMove` therefore transports both
certified length-three paths to the intrinsic ambient relation.  In the other
direction it sends every intrinsic ambient path back to a normalized path, so
the two normalized lower bounds rule out extra shorter ambient paths.

This is only the sharpness lift on the actual coordinate factor spaces.  It
does not claim an arbitrary-space completeness theorem or package the
abstract-tensor circuit model.
-/

namespace BilinearComplexity.BinaryAmbientFiveCircuitSharpness

open BinaryCircuit
open NormalizedBinaryCarrier
open NormalizedBinaryAllModeMove
open NormalizedBinaryFiveCircuitRows
open NormalizedBinaryFiveCircuitSharpness

universe u

/-- Mapping every edge of a concrete path along a relation implication does
not change its number of edges. -/
theorem movePath_mono_length {α : Type u}
    {R S : BinaryCircuit.Scheme α → BinaryCircuit.Scheme α → Prop}
    (hRS : ∀ {X Y}, R X Y → S X Y) {D E : BinaryCircuit.Scheme α}
    (path : MovePath R D E) :
    (path.mono hRS).length = path.length := by
  induction path with
  | singleton => simp only [MovePath.mono, MovePath.length]
  | snoc path _ ih =>
      simp only [MovePath.mono, MovePath.length, ih]

/-- Mapping every edge of a concrete path along a relation implication does
not change its maximum vertex cardinality. -/
theorem movePath_mono_altitude {α : Type u}
    {R S : BinaryCircuit.Scheme α → BinaryCircuit.Scheme α → Prop}
    (hRS : ∀ {X Y}, R X Y → S X Y) {D E : BinaryCircuit.Scheme α}
    (path : MovePath R D E) :
    (path.mono hRS).altitude = path.altitude := by
  induction path with
  | singleton => simp only [MovePath.mono, MovePath.altitude]
  | snoc path _ ih =>
      simp only [MovePath.mono, MovePath.altitude, ih]

private theorem normalizedAllModeMove_to_ambient411
    {D E : State profile411} (h : @AllModeMove profile411 D E) :
    BinaryAmbientMoves.AllModeMove
      (U := CoordinateVector profile411.first)
      (V := CoordinateVector profile411.second)
      (W := CoordinateVector profile411.third) D E :=
  (@BinaryAmbientMoves.Coordinate.allModeMove_iff_normalized
    profile411 D E).mpr h

private theorem ambientAllModeMove_to_normalized411
    {D E : State profile411}
    (h : BinaryAmbientMoves.AllModeMove
      (U := CoordinateVector profile411.first)
      (V := CoordinateVector profile411.second)
      (W := CoordinateVector profile411.third) D E) :
    @AllModeMove profile411 D E :=
  (@BinaryAmbientMoves.Coordinate.allModeMove_iff_normalized
    profile411 D E).mp h

/-- The certified normalized forward path, regarded as an intrinsic ambient
path in the actual coordinate factor spaces of profile `(4,1,1)`. -/
def row41101AmbientForwardPath :
    MovePath
      (BinaryAmbientMoves.AllModeMove
        (U := CoordinateVector profile411.first)
        (V := CoordinateVector profile411.second)
        (W := CoordinateVector profile411.third))
      row41101Start row41101Finish :=
  row41101ForwardPath.mono normalizedAllModeMove_to_ambient411

/-- The certified normalized reverse path, regarded as an intrinsic ambient
path in the actual coordinate factor spaces of profile `(4,1,1)`. -/
def row41101AmbientReversePath :
    MovePath
      (BinaryAmbientMoves.AllModeMove
        (U := CoordinateVector profile411.first)
        (V := CoordinateVector profile411.second)
        (W := CoordinateVector profile411.third))
      row41101Finish row41101Start :=
  row41101ReversePath.mono normalizedAllModeMove_to_ambient411

/-- The intrinsic ambient forward witness has exactly three edges. -/
@[simp] theorem row41101AmbientForwardPath_length :
    row41101AmbientForwardPath.length = 3 := by
  unfold row41101AmbientForwardPath
  exact (movePath_mono_length
    (α := NormalizedBinaryCarrier.Carrier profile411)
    normalizedAllModeMove_to_ambient411 row41101ForwardPath).trans row41101ForwardPath_length

/-- The intrinsic ambient reverse witness has exactly three edges. -/
@[simp] theorem row41101AmbientReversePath_length :
    row41101AmbientReversePath.length = 3 := by
  unfold row41101AmbientReversePath
  exact (movePath_mono_length
    (α := NormalizedBinaryCarrier.Carrier profile411)
    normalizedAllModeMove_to_ambient411 row41101ReversePath).trans row41101ReversePath_length

/-- Every vertex of the intrinsic ambient forward witness has at most four
terms. -/
theorem row41101AmbientForwardPath_altitude_le_four :
    row41101AmbientForwardPath.altitude ≤ 4 := by
  unfold row41101AmbientForwardPath
  rw [movePath_mono_altitude
    (α := NormalizedBinaryCarrier.Carrier profile411)
    normalizedAllModeMove_to_ambient411]
  apply allModeMovePath_altitude_le_four row41101ForwardPath
  · rw [row41101_card_start]
    omega
  · rw [row41101_card_finish]
  · rw [row41101ForwardPath_length]

/-- Every vertex of the intrinsic ambient reverse witness has at most four
terms. -/
theorem row41101AmbientReversePath_altitude_le_four :
    row41101AmbientReversePath.altitude ≤ 4 := by
  unfold row41101AmbientReversePath
  rw [movePath_mono_altitude
    (α := NormalizedBinaryCarrier.Carrier profile411)
    normalizedAllModeMove_to_ambient411]
  apply allModeMovePath_altitude_le_four row41101ReversePath
  · rw [row41101_card_finish]
  · rw [row41101_card_start]
    omega
  · rw [row41101ReversePath_length]

/-- No intrinsic ambient all-mode path from the selected two-term endpoint to
the three-term endpoint has at most two edges. -/
theorem row41101_no_ambient_forward_path_length_le_two
    (path : MovePath
      (BinaryAmbientMoves.AllModeMove
        (U := CoordinateVector profile411.first)
        (V := CoordinateVector profile411.second)
        (W := CoordinateVector profile411.third))
      row41101Start row41101Finish) :
    ¬ path.length ≤ 2 := by
  let coordinatePath := path.mono ambientAllModeMove_to_normalized411
  have hlength : coordinatePath.length = path.length :=
    movePath_mono_length ambientAllModeMove_to_normalized411 path
  intro hshort
  have hcoordinateShort : coordinatePath.length ≤ 2 := by
    calc
      coordinatePath.length = path.length := hlength
      _ ≤ 2 := hshort
  exact row41101_no_forward_path_length_le_two coordinatePath hcoordinateShort

/-- No intrinsic ambient all-mode path from the selected three-term endpoint
to the two-term endpoint has at most two edges. -/
theorem row41101_no_ambient_reverse_path_length_le_two
    (path : MovePath
      (BinaryAmbientMoves.AllModeMove
        (U := CoordinateVector profile411.first)
        (V := CoordinateVector profile411.second)
        (W := CoordinateVector profile411.third))
      row41101Finish row41101Start) :
    ¬ path.length ≤ 2 := by
  let coordinatePath := path.mono ambientAllModeMove_to_normalized411
  have hlength : coordinatePath.length = path.length :=
    movePath_mono_length ambientAllModeMove_to_normalized411 path
  intro hshort
  have hcoordinateShort : coordinatePath.length ≤ 2 := by
    calc
      coordinatePath.length = path.length := hlength
      _ ≤ 2 := hshort
  exact row41101_no_reverse_path_length_le_two coordinatePath hcoordinateShort

/-- On the actual coordinate factor spaces of profile `(4,1,1)`, intrinsic
ambient all-mode distance between the selected ordered endpoints is exactly
three in both directions, with witnesses of altitude at most four. -/
theorem row41101_intrinsic_ambient_exact_directed_length_three :
    row41101AmbientForwardPath.length = 3 ∧
      row41101AmbientReversePath.length = 3 ∧
      row41101AmbientForwardPath.altitude ≤ 4 ∧
      row41101AmbientReversePath.altitude ≤ 4 ∧
      (∀ path : MovePath
        (BinaryAmbientMoves.AllModeMove
          (U := CoordinateVector profile411.first)
        (V := CoordinateVector profile411.second)
        (W := CoordinateVector profile411.third))
        row41101Start row41101Finish, ¬ path.length ≤ 2) ∧
      (∀ path : MovePath
        (BinaryAmbientMoves.AllModeMove
          (U := CoordinateVector profile411.first)
        (V := CoordinateVector profile411.second)
        (W := CoordinateVector profile411.third))
        row41101Finish row41101Start, ¬ path.length ≤ 2) := by
  exact ⟨row41101AmbientForwardPath_length,
    row41101AmbientReversePath_length,
    row41101AmbientForwardPath_altitude_le_four,
    row41101AmbientReversePath_altitude_le_four,
    row41101_no_ambient_forward_path_length_le_two,
    row41101_no_ambient_reverse_path_length_le_two⟩

example : MovePath
    (BinaryAmbientMoves.AllModeMove
      (U := Fin 4 → F2) (V := Fin 1 → F2) (W := Fin 1 → F2))
    row41101Start row41101Finish :=
  row41101AmbientForwardPath

example : MovePath
    (BinaryAmbientMoves.AllModeMove
      (U := Fin 4 → F2) (V := Fin 1 → F2) (W := Fin 1 → F2))
    row41101Finish row41101Start :=
  row41101AmbientReversePath

example : row41101AmbientForwardPath.length = 3 ∧
    row41101AmbientForwardPath.altitude ≤ 4 :=
  ⟨row41101AmbientForwardPath_length,
    row41101AmbientForwardPath_altitude_le_four⟩

example : row41101AmbientReversePath.length = 3 ∧
    row41101AmbientReversePath.altitude ≤ 4 :=
  ⟨row41101AmbientReversePath_length,
    row41101AmbientReversePath_altitude_le_four⟩

#check @movePath_mono_length
#check @movePath_mono_altitude
#check @row41101AmbientForwardPath
#check @row41101AmbientReversePath
#check @row41101AmbientForwardPath_length
#check @row41101AmbientReversePath_length
#check @row41101AmbientForwardPath_altitude_le_four
#check @row41101AmbientReversePath_altitude_le_four
#check @row41101_no_ambient_forward_path_length_le_two
#check @row41101_no_ambient_reverse_path_length_le_two
#check @row41101_intrinsic_ambient_exact_directed_length_three

#print axioms row41101AmbientForwardPath_length
#print axioms row41101AmbientReversePath_length
#print axioms row41101AmbientForwardPath_altitude_le_four
#print axioms row41101AmbientReversePath_altitude_le_four
#print axioms row41101_no_ambient_forward_path_length_le_two
#print axioms row41101_no_ambient_reverse_path_length_le_two
#print axioms row41101_intrinsic_ambient_exact_directed_length_three

end BilinearComplexity.BinaryAmbientFiveCircuitSharpness
