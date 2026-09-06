import BilinearComplexity.BinaryAmbientFullFrame
import BilinearComplexity.NormalizedBinaryBoundedSearch

set_option autoImplicit false

/-!
# Certified bounded search in full binary ambient coordinates

Explicit full coordinate equivalences reduce an ambient bounded-search problem
to the complete normalized native search and realize its selected path back in
the original factor spaces. Competitors are arbitrary intrinsic ambient paths;
they need not remain in the spans of the initial or terminal state.

The executable data path uses only the supplied equivalences. No basis,
coverage certificate, lower-bound oracle, or caller-provided optimizer is
chosen at runtime.
-/

namespace BilinearComplexity.BinaryAmbientBoundedSearch

open BinaryCircuit
open BinaryAmbientCarrier
open BinaryAmbientMoves
open NormalizedBinaryCarrier (F2)
open BinaryAmbientTensorCoordinates
open BinaryAmbientFullFrame

universe u v w

variable {U : Type u} {V : Type v} {W : Type w}
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [Module F2 U] [Module F2 V] [Module F2 W]
variable [DecidableEq U] [DecidableEq V] [DecidableEq W]
variable {a b c : ℕ}

private def castPathStart {α : Type*} [DecidableEq α]
    {R : Finset α → Finset α → Prop} {D D' E : Finset α}
    (h : D = D') (path : MovePath R D E) : MovePath R D' E :=
  h ▸ path

private theorem castPathStart_length {α : Type*} [DecidableEq α]
    {R : Finset α → Finset α → Prop} {D D' E : Finset α}
    (h : D = D') (path : MovePath R D E) :
    (castPathStart h path).length = path.length := by
  cases h
  rfl

private theorem castPathStart_altitude {α : Type*} [DecidableEq α]
    {R : Finset α → Finset α → Prop} {D D' E : Finset α}
    (h : D = D') (path : MovePath R D E) :
    (castPathStart h path).altitude = path.altitude := by
  cases h
  rfl

/-- A certified ambient endpoint minimizing cardinality among all intrinsic
all-mode paths satisfying the same primitive-depth and altitude bounds. -/
structure Result (D : State U V W) (k H : ℕ) where
  /-- The selected ambient terminal state. -/
  finish : State U V W
  /-- An actual intrinsic ambient path from the original state to the selected
  terminal state. -/
  path : MovePath (AllModeMove (U := U) (V := V) (W := W)) D finish
  /-- The selected path respects the primitive-edge budget. -/
  length_le : path.length ≤ k
  /-- Every selected-path vertex respects the cardinality ceiling. -/
  altitude_le : path.altitude ≤ H
  /-- No ambient competitor under the same bounds has smaller endpoint
  cardinality. -/
  optimal : ∀ {E : State U V W}
    (competitor : MovePath (AllModeMove (U := U) (V := V) (W := W)) D E),
    competitor.length ≤ k → competitor.altitude ≤ H → finish.card ≤ E.card
  /-- The selected endpoint has the same ambient tensor evaluation as the
  original state. -/
  preserves_evaluation : stateEvaluation finish = stateEvaluation D
  /-- The selected endpoint has no more terms than the original state. -/
  card_le_original : finish.card ≤ D.card

/-- Using supplied full coordinate equivalences, exhaustively optimize over all
bounded intrinsic ambient paths and return an ambient path and its complete
minimum-cardinality certificate. -/
def optimize
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) (D : State U V W) (k H : ℕ)
    (hD : D.card ≤ H) : Result D k H := by
  let normalizedD := normalizeState eU eV eW D
  have hnormalizedD : normalizedD.card ≤ H := by
    simpa only [normalizedD, normalizeState_card] using hD
  let normalized :=
    NormalizedBinaryBoundedSearch.optimize normalizedD k H hnormalizedD
  let finish := denormalizeState eU eV eW normalized.finish
  have hstart : denormalizeState eU eV eW normalizedD = D := by
    simpa only [normalizedD] using
      denormalizeState_normalizeState eU eV eW D
  let path : MovePath (AllModeMove (U := U) (V := V) (W := W)) D finish :=
    castPathStart hstart (denormalizePath eU eV eW normalized.path)
  have hpathLength : path.length = normalized.path.length := by
    calc
      path.length = (denormalizePath eU eV eW normalized.path).length :=
        castPathStart_length hstart _
      _ = normalized.path.length :=
        denormalizePath_length eU eV eW normalized.path
  have hpathAltitude : path.altitude = normalized.path.altitude := by
    calc
      path.altitude = (denormalizePath eU eV eW normalized.path).altitude :=
        castPathStart_altitude hstart _
      _ = normalized.path.altitude :=
        denormalizePath_altitude eU eV eW normalized.path
  refine {
    finish := finish
    path := path
    length_le := hpathLength.trans_le normalized.length_le
    altitude_le := hpathAltitude.trans_le normalized.altitude_le
    optimal := ?_
    preserves_evaluation := ?_
    card_le_original := ?_ }
  · intro E competitor hlength haltitude
    let normalizedCompetitor := normalizePath eU eV eW competitor
    have hnormalizedLength : normalizedCompetitor.length ≤ k := by
      simpa only [normalizedCompetitor, normalizePath_length] using hlength
    have hnormalizedAltitude : normalizedCompetitor.altitude ≤ H := by
      simpa only [normalizedCompetitor, normalizePath_altitude] using haltitude
    have hoptimal :
        normalized.finish.card ≤ (normalizeState eU eV eW E).card :=
      normalized.optimal normalizedCompetitor hnormalizedLength
        hnormalizedAltitude
    simpa only [finish, denormalizeState_card, normalizeState_card] using
      hoptimal
  · apply (normalized_stateEvaluation_eq_iff eU eV eW finish D).mp
    simpa only [finish, normalizeState_denormalizeState, normalizedD] using
      normalized.preserves_evaluation
  · have hrootLength :
        (.singleton normalizedD : MovePath
          (@NormalizedBinaryAllModeMove.AllModeMove (coordinateProfile a b c))
          normalizedD normalizedD).length ≤ k := by
      simp only [MovePath.length, Nat.zero_le]
    have hrootAltitude :
        (.singleton normalizedD : MovePath
          (@NormalizedBinaryAllModeMove.AllModeMove (coordinateProfile a b c))
          normalizedD normalizedD).altitude ≤ H := by
      simpa only [MovePath.altitude] using hnormalizedD
    have hoptimal := normalized.optimal
      (.singleton normalizedD : MovePath
        (@NormalizedBinaryAllModeMove.AllModeMove (coordinateProfile a b c))
        normalizedD normalizedD) hrootLength hrootAltitude
    simpa only [finish, denormalizeState_card, normalizedD,
      normalizeState_card] using hoptimal

/-! Ground, executability, signature, and trust checks. -/

open NormalizedBinaryReplay221

example :
    let result := optimize (LinearEquiv.refl F2 (Coord 2))
      (LinearEquiv.refl F2 (Coord 2)) (LinearEquiv.refl F2 (Coord 1))
      S1 1 3 (by decide)
    result.path.length ≤ 1 ∧ result.path.altitude ≤ 3 ∧
      result.finish.card ≤ S1.card := by
  dsimp only
  exact ⟨Result.length_le _, Result.altitude_le _, Result.card_le_original _⟩

#eval
  let result := optimize (LinearEquiv.refl F2 (Coord 2))
    (LinearEquiv.refl F2 (Coord 2)) (LinearEquiv.refl F2 (Coord 1))
    S1 1 3 (by decide)
  (result.finish.card, result.path.length, result.path.altitude)

#check @Result
#check @Result.optimal
#check @Result.preserves_evaluation
#check @Result.card_le_original
#check @optimize
#print axioms optimize

end BilinearComplexity.BinaryAmbientBoundedSearch
