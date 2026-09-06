import BilinearComplexity.BinaryAmbientMoveTransport
import BilinearComplexity.BinaryAmbientTensorCoordinates

set_option autoImplicit false

/-!
# Full-frame reflection for binary ambient moves

Three explicitly supplied linear equivalences identify the complete ambient
factor spaces with finite binary coordinate spaces. Unlike endpoint-span
presentations, these full frames cover every possible ambient competitor.
This module proves that intrinsic six-orientation edges are equivalent to
normalized edges, then reflects executable paths in both directions while
preserving vertices, edge count, and altitude. It constructs no basis and
uses no runtime choice.
-/

namespace BilinearComplexity.BinaryAmbientFullFrame

open BinaryCircuit
open BinaryAmbientCarrier
open BinaryAmbientMoves
open NormalizedBinaryCarrier (F2 CoordinateVector Profile)
open BinaryAmbientTensorCoordinates

universe u v w

variable {U : Type u} {V : Type v} {W : Type w}
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [Module F2 U] [Module F2 V] [Module F2 W]
variable [DecidableEq U] [DecidableEq V] [DecidableEq W]
variable {a b c : ℕ}

omit [DecidableEq U] [DecidableEq V] [DecidableEq W] in
private theorem normalizeState_mem
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    {t : Carrier U V W} {D : State U V W} :
    normalizeTerm eU eV eW t ∈ normalizeState eU eV eW D ↔ t ∈ D := by
  constructor
  · intro h
    obtain ⟨s, hs, hst⟩ := Finset.mem_map.mp h
    have hst' : s = t := (carrierEquiv eU eV eW).symm.injective hst
    simpa only [hst'] using hs
  · intro h
    exact Finset.mem_map.mpr ⟨t, h, rfl⟩

private theorem normalizeState_erase
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    (D : State U V W) (t : Carrier U V W) :
    normalizeState eU eV eW (D.erase t) =
      (normalizeState eU eV eW D).erase (normalizeTerm eU eV eW t) := by
  exact Finset.map_erase (carrierEquiv eU eV eW).symm.toEmbedding D t

private theorem normalizeState_insert
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    (D : State U V W) (t : Carrier U V W) :
    normalizeState eU eV eW (insert t D) =
      insert (normalizeTerm eU eV eW t) (normalizeState eU eV eW D) := by
  exact Finset.map_insert (carrierEquiv eU eV eW).symm.toEmbedding t D

private theorem reflectGeneratedFirstSplit
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    {source outputLeft outputRight : Carrier U V W}
    {D E : State U V W}
    (h : GeneratedFirstSplit source outputLeft outputRight D E) :
    GeneratedFirstSplit
      (U := CoordinateVector (coordinateProfile a b c).first)
      (V := CoordinateVector (coordinateProfile a b c).second)
      (W := CoordinateVector (coordinateProfile a b c).third)
      (normalizeTerm eU eV eW source)
      (normalizeTerm eU eV eW outputLeft)
      (normalizeTerm eU eV eW outputRight)
      (normalizeState eU eV eW D) (normalizeState eU eV eW E) := by
  rcases h with ⟨hmem, hne, hfreshLeft, hfreshRight, hfirst, hleftSecond,
    hrightSecond, hleftThird, hrightThird, htarget⟩
  refine ⟨(normalizeState_mem eU eV eW).mpr hmem,
    fun heq => hne ((carrierEquiv eU eV eW).symm.injective heq), ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← normalizeState_erase]
    exact fun hmem' => hfreshLeft ((normalizeState_mem eU eV eW).mp hmem')
  · rw [← normalizeState_erase]
    exact fun hmem' => hfreshRight ((normalizeState_mem eU eV eW).mp hmem')
  · exact congrArg eU.symm hfirst |>.trans (eU.symm.map_add _ _)
  · exact congrArg eV.symm hleftSecond
  · exact congrArg eV.symm hrightSecond
  · exact congrArg eW.symm hleftThird
  · exact congrArg eW.symm hrightThird
  · rw [htarget, normalizeState_insert, normalizeState_insert,
      normalizeState_erase]

private theorem reflectSourceThirdFlip
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    {sourceLeft sourceRight targetLeft targetRight : Carrier U V W}
    {D E : State U V W}
    (h : SourceThirdFlip sourceLeft sourceRight targetLeft targetRight D E) :
    SourceThirdFlip
      (U := CoordinateVector (coordinateProfile a b c).first)
      (V := CoordinateVector (coordinateProfile a b c).second)
      (W := CoordinateVector (coordinateProfile a b c).third)
      (normalizeTerm eU eV eW sourceLeft)
      (normalizeTerm eU eV eW sourceRight)
      (normalizeTerm eU eV eW targetLeft)
      (normalizeTerm eU eV eW targetRight)
      (normalizeState eU eV eW D) (normalizeState eU eV eW E) := by
  rcases h with ⟨hleftMem, hrightMem, hsources, hfreshLeft, hfreshRight,
    htargets, hsourceThird, htargetLeftFirst, htargetLeftSecond,
    htargetLeftThird, htargetRightFirst, htargetRightSecond, htargetRightThird,
    htarget⟩
  refine ⟨(normalizeState_mem eU eV eW).mpr hleftMem,
    (normalizeState_mem eU eV eW).mpr hrightMem,
    fun heq => hsources ((carrierEquiv eU eV eW).symm.injective heq), ?_, ?_,
    fun heq => htargets ((carrierEquiv eU eV eW).symm.injective heq),
    congrArg eW.symm hsourceThird, ?_, congrArg eV.symm htargetLeftSecond,
    congrArg eW.symm htargetLeftThird, congrArg eU.symm htargetRightFirst,
    ?_, congrArg eW.symm htargetRightThird, ?_⟩
  · rw [← normalizeState_erase, ← normalizeState_erase]
    exact fun hmem' => hfreshLeft ((normalizeState_mem eU eV eW).mp hmem')
  · rw [← normalizeState_erase, ← normalizeState_erase]
    exact fun hmem' => hfreshRight ((normalizeState_mem eU eV eW).mp hmem')
  · exact congrArg eU.symm htargetLeftFirst |>.trans (eU.symm.map_add _ _)
  · exact congrArg eV.symm htargetRightSecond |>.trans (eV.symm.map_sub _ _)
  · rw [htarget, normalizeState_insert, normalizeState_insert,
      normalizeState_erase, normalizeState_erase]

private theorem reflectDirectedNarrowPairReduction
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    {sourceLeft sourceRight target : Carrier U V W}
    {D E : State U V W}
    (h : DirectedNarrowPairReduction sourceLeft sourceRight target D E) :
    DirectedNarrowPairReduction
      (U := CoordinateVector (coordinateProfile a b c).first)
      (V := CoordinateVector (coordinateProfile a b c).second)
      (W := CoordinateVector (coordinateProfile a b c).third)
      (normalizeTerm eU eV eW sourceLeft)
      (normalizeTerm eU eV eW sourceRight)
      (normalizeTerm eU eV eW target)
      (normalizeState eU eV eW D) (normalizeState eU eV eW E) := by
  rcases h with ⟨hleftMem, hrightMem, hsources, hfresh, hsecond, hthird,
    htargetFirst, htargetSecond, htargetThird, htarget⟩
  refine ⟨(normalizeState_mem eU eV eW).mpr hleftMem,
    (normalizeState_mem eU eV eW).mpr hrightMem,
    fun heq => hsources ((carrierEquiv eU eV eW).symm.injective heq), ?_,
    congrArg eV.symm hsecond, congrArg eW.symm hthird, ?_,
    congrArg eV.symm htargetSecond, congrArg eW.symm htargetThird, ?_⟩
  · rw [← normalizeState_erase, ← normalizeState_erase]
    exact fun hmem' => hfresh ((normalizeState_mem eU eV eW).mp hmem')
  · exact congrArg eU.symm htargetFirst |>.trans (eU.symm.map_add _ _)
  · rw [htarget, normalizeState_insert, normalizeState_erase,
      normalizeState_erase]

private theorem reflectMove
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) {D E : State U V W}
    (h : Move D E) :
    Move (U := CoordinateVector (coordinateProfile a b c).first)
      (V := CoordinateVector (coordinateProfile a b c).second)
      (W := CoordinateVector (coordinateProfile a b c).third)
      (normalizeState eU eV eW D) (normalizeState eU eV eW E) := by
  cases h with
  | generatedFirstSplit hsplit =>
      exact .generatedFirstSplit (reflectGeneratedFirstSplit eU eV eW hsplit)
  | sourceThirdFlip hflip =>
      exact .sourceThirdFlip (reflectSourceThirdFlip eU eV eW hflip)
  | directedNarrowPairReduction hreduction =>
      exact .directedNarrowPairReduction
        (reflectDirectedNarrowPairReduction eU eV eW hreduction)

private theorem normalizeState_permuteBCA
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) (D : State W U V) :
    normalizeState eU eV eW (permuteBCAState D) =
      permuteBCAState (normalizeState eW eU eV D) := by
  unfold normalizeState permuteBCAState
  rw [Finset.map_eq_image, Finset.image_image, Finset.map_eq_image,
    Finset.image_image]
  apply Finset.image_congr
  intro t _ht
  rfl

private theorem normalizeState_permuteCAB
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) (D : State V W U) :
    normalizeState eU eV eW (permuteCABState D) =
      permuteCABState (normalizeState eV eW eU D) := by
  unfold normalizeState permuteCABState
  rw [Finset.map_eq_image, Finset.image_image, Finset.map_eq_image,
    Finset.image_image]
  apply Finset.image_congr
  intro t _ht
  rfl

private theorem normalizeState_permuteACB
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) (D : State U W V) :
    normalizeState eU eV eW (permuteACBState D) =
      permuteACBState (normalizeState eU eW eV D) := by
  unfold normalizeState permuteACBState
  rw [Finset.map_eq_image, Finset.image_image, Finset.map_eq_image,
    Finset.image_image]
  apply Finset.image_congr
  intro t _ht
  rfl

private theorem normalizeState_permuteCBA
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) (D : State W V U) :
    normalizeState eU eV eW (permuteCBAState D) =
      permuteCBAState (normalizeState eW eV eU D) := by
  unfold normalizeState permuteCBAState
  rw [Finset.map_eq_image, Finset.image_image, Finset.map_eq_image,
    Finset.image_image]
  apply Finset.image_congr
  intro t _ht
  rfl

private theorem normalizeState_permuteBAC
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) (D : State V U W) :
    normalizeState eU eV eW (permuteBACState D) =
      permuteBACState (normalizeState eV eU eW D) := by
  unfold normalizeState permuteBACState
  rw [Finset.map_eq_image, Finset.image_image, Finset.map_eq_image,
    Finset.image_image]
  apply Finset.image_congr
  intro t _ht
  rfl

private theorem reflectCoordinateAllModeMove
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) {D E : State U V W}
    (h : AllModeMove D E) :
    AllModeMove (U := CoordinateVector (coordinateProfile a b c).first)
      (V := CoordinateVector (coordinateProfile a b c).second)
      (W := CoordinateVector (coordinateProfile a b c).third)
      (normalizeState eU eV eW D) (normalizeState eU eV eW E) := by
  cases h with
  | abc hmove => exact .abc (reflectMove eU eV eW hmove)
  | bca hmove hD hE =>
      refine .bca (reflectMove eW eU eV hmove) ?_ ?_
      · rw [hD]
        exact normalizeState_permuteBCA eU eV eW _
      · rw [hE]
        exact normalizeState_permuteBCA eU eV eW _
  | cab hmove hD hE =>
      refine .cab (reflectMove eV eW eU hmove) ?_ ?_
      · rw [hD]
        exact normalizeState_permuteCAB eU eV eW _
      · rw [hE]
        exact normalizeState_permuteCAB eU eV eW _
  | acb hmove hD hE =>
      refine .acb (reflectMove eU eW eV hmove) ?_ ?_
      · rw [hD]
        exact normalizeState_permuteACB eU eV eW _
      · rw [hE]
        exact normalizeState_permuteACB eU eV eW _
  | cba hmove hD hE =>
      refine .cba (reflectMove eW eV eU hmove) ?_ ?_
      · rw [hD]
        exact normalizeState_permuteCBA eU eV eW _
      · rw [hE]
        exact normalizeState_permuteCBA eU eV eW _
  | bac hmove hD hE =>
      refine .bac (reflectMove eV eU eW hmove) ?_ ?_
      · rw [hD]
        exact normalizeState_permuteBAC eU eV eW _
      · rw [hE]
        exact normalizeState_permuteBAC eU eV eW _

private def fullFrameEmbedding
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) :
    BinaryAmbientMoveTransport.CoordinateEmbedding
      (coordinateProfile a b c) U V W := by
  change BinaryAmbientMoveTransport.CoordinateEmbedding ⟨a, b, c⟩ U V W
  exact {
    first := eU
    second := eV
    third := eW
    first_injective := eU.injective
    second_injective := eV.injective
    third_injective := eW.injective }

omit [DecidableEq U] [DecidableEq V] [DecidableEq W] in
private theorem mapTerm_fullFrameEmbedding
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    (t : NormalizedBinaryCarrier.Carrier (coordinateProfile a b c)) :
    BinaryAmbientMoveTransport.mapTerm (fullFrameEmbedding eU eV eW) t =
      denormalizeTerm eU eV eW t := by
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl

private theorem mapState_fullFrameEmbedding
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    (D : NormalizedBinaryCarrier.State (coordinateProfile a b c)) :
    BinaryAmbientMoveTransport.mapState (fullFrameEmbedding eU eV eW) D =
      denormalizeState eU eV eW D := by
  unfold BinaryAmbientMoveTransport.mapState denormalizeState
  rw [Finset.map_eq_image]
  apply Finset.image_congr
  intro t _ht
  exact mapTerm_fullFrameEmbedding eU eV eW t

/-- A supplied full coordinate frame identifies intrinsic ambient all-mode
legality with normalized all-mode legality. -/
theorem allModeMove_iff_normalized
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) (D E : State U V W) :
    AllModeMove D E ↔
      @NormalizedBinaryAllModeMove.AllModeMove (coordinateProfile a b c)
        (normalizeState eU eV eW D) (normalizeState eU eV eW E) := by
  constructor
  · intro h
    apply BinaryAmbientMoves.Coordinate.allModeMove_iff_normalized.mp
    exact reflectCoordinateAllModeMove eU eV eW h
  · intro h
    let f := fullFrameEmbedding eU eV eW
    have hambient :=
      BinaryAmbientMoveTransport.transportNormalizedAllModeMove f h
    rw [mapState_fullFrameEmbedding, mapState_fullFrameEmbedding,
      denormalizeState_normalizeState, denormalizeState_normalizeState] at hambient
    exact hambient

/-- Normalize every vertex and edge of an ambient path through a supplied full
coordinate frame. -/
def normalizePath
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) :
    {D E : State U V W} → MovePath (AllModeMove (U := U) (V := V) (W := W)) D E →
      MovePath (@NormalizedBinaryAllModeMove.AllModeMove (coordinateProfile a b c))
        (normalizeState eU eV eW D) (normalizeState eU eV eW E)
  | _, _, .singleton D => .singleton (normalizeState eU eV eW D)
  | _, _, .snoc path h =>
      .snoc (normalizePath eU eV eW path)
        ((allModeMove_iff_normalized eU eV eW _ _).mp h)

example
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) (D : State U V W) :
    normalizePath eU eV eW
        (.singleton D : MovePath (AllModeMove (U := U) (V := V) (W := W)) D D) =
      (.singleton (normalizeState eU eV eW D) :
        MovePath (@NormalizedBinaryAllModeMove.AllModeMove (coordinateProfile a b c))
          (normalizeState eU eV eW D) (normalizeState eU eV eW D)) :=
  by simp only [normalizePath]

/-- Denormalize every vertex and edge of a coordinate path through a supplied
full ambient frame. -/
def denormalizePath
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) :
    {D E : NormalizedBinaryCarrier.State (coordinateProfile a b c)} →
      MovePath (@NormalizedBinaryAllModeMove.AllModeMove (coordinateProfile a b c)) D E →
      MovePath (AllModeMove (U := U) (V := V) (W := W))
        (denormalizeState eU eV eW D) (denormalizeState eU eV eW E)
  | _, _, .singleton D => .singleton (denormalizeState eU eV eW D)
  | _, _, .snoc path h =>
      .snoc (denormalizePath eU eV eW path)
        ((allModeMove_iff_normalized eU eV eW _ _).mpr (by simpa using h))

example
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    (D : NormalizedBinaryCarrier.State (coordinateProfile a b c)) :
    denormalizePath eU eV eW
        (.singleton D : MovePath (@NormalizedBinaryAllModeMove.AllModeMove
          (coordinateProfile a b c)) D D) =
      (.singleton (denormalizeState eU eV eW D) :
        MovePath (AllModeMove (U := U) (V := V) (W := W))
          (denormalizeState eU eV eW D) (denormalizeState eU eV eW D)) :=
  by simp only [denormalizePath]

/-- Normalizing a path maps its ordered vertex list pointwise. -/
theorem normalizePath_vertices
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) {D E : State U V W}
    (path : MovePath (AllModeMove (U := U) (V := V) (W := W)) D E) :
    (normalizePath eU eV eW path).vertices =
      path.vertices.map (normalizeState eU eV eW) := by
  induction path with
  | singleton => simp only [normalizePath, MovePath.vertices, List.map_singleton]
  | snoc path _ ih =>
      simp only [normalizePath, MovePath.vertices, ih, List.map_append,
        List.map_singleton]

/-- Denormalizing a path maps its ordered vertex list pointwise. -/
theorem denormalizePath_vertices
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    {D E : NormalizedBinaryCarrier.State (coordinateProfile a b c)}
    (path : MovePath (@NormalizedBinaryAllModeMove.AllModeMove
      (coordinateProfile a b c)) D E) :
    (denormalizePath eU eV eW path).vertices =
      path.vertices.map (denormalizeState eU eV eW) := by
  induction path with
  | singleton => simp only [denormalizePath, MovePath.vertices, List.map_singleton]
  | snoc path _ ih =>
      simp only [denormalizePath, MovePath.vertices, ih, List.map_append,
        List.map_singleton]

/-- Full-frame path normalization preserves the exact edge count. -/
@[simp] theorem normalizePath_length
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) {D E : State U V W}
    (path : MovePath (AllModeMove (U := U) (V := V) (W := W)) D E) :
    (normalizePath eU eV eW path).length = path.length := by
  induction path with
  | singleton => simp only [normalizePath, MovePath.length]
  | snoc path _ ih => simp only [normalizePath, MovePath.length, ih]

/-- Full-frame path normalization preserves exact altitude. -/
@[simp] theorem normalizePath_altitude
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) {D E : State U V W}
    (path : MovePath (AllModeMove (U := U) (V := V) (W := W)) D E) :
    (normalizePath eU eV eW path).altitude = path.altitude := by
  induction path with
  | singleton =>
      simp only [normalizePath, MovePath.altitude, normalizeState_card]
  | snoc path _ ih =>
      simp only [normalizePath, MovePath.altitude, ih, normalizeState_card]

/-- Full-frame path denormalization preserves the exact edge count. -/
@[simp] theorem denormalizePath_length
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    {D E : NormalizedBinaryCarrier.State (coordinateProfile a b c)}
    (path : MovePath (@NormalizedBinaryAllModeMove.AllModeMove
      (coordinateProfile a b c)) D E) :
    (denormalizePath eU eV eW path).length = path.length := by
  induction path with
  | singleton => simp only [denormalizePath, MovePath.length]
  | snoc path _ ih => simp only [denormalizePath, MovePath.length, ih]

/-- Full-frame path denormalization preserves exact altitude. -/
@[simp] theorem denormalizePath_altitude
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    {D E : NormalizedBinaryCarrier.State (coordinateProfile a b c)}
    (path : MovePath (@NormalizedBinaryAllModeMove.AllModeMove
      (coordinateProfile a b c)) D E) :
    (denormalizePath eU eV eW path).altitude = path.altitude := by
  induction path with
  | singleton =>
      simp only [denormalizePath, MovePath.altitude, denormalizeState_card]
  | snoc path _ ih =>
      simp only [denormalizePath, MovePath.altitude, ih, denormalizeState_card]

/-- Normalizing a denormalized path restores its ordered vertex sequence. -/
theorem normalizePath_denormalizePath_vertices
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W)
    {D E : NormalizedBinaryCarrier.State (coordinateProfile a b c)}
    (path : MovePath (@NormalizedBinaryAllModeMove.AllModeMove
      (coordinateProfile a b c)) D E) :
    (normalizePath eU eV eW (denormalizePath eU eV eW path)).vertices =
      path.vertices := by
  rw [normalizePath_vertices, denormalizePath_vertices, List.map_map]
  have hfun : normalizeState eU eV eW ∘ denormalizeState eU eV eW = id := by
    funext X
    exact normalizeState_denormalizeState eU eV eW X
  rw [hfun, List.map_id]

/-- Denormalizing a normalized path restores its ordered ambient vertex sequence. -/
theorem denormalizePath_normalizePath_vertices
    (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) {D E : State U V W}
    (path : MovePath (AllModeMove (U := U) (V := V) (W := W)) D E) :
    (denormalizePath eU eV eW (normalizePath eU eV eW path)).vertices =
      path.vertices := by
  rw [denormalizePath_vertices, normalizePath_vertices, List.map_map]
  have hfun : denormalizeState eU eV eW ∘ normalizeState eU eV eW = id := by
    funext X
    exact denormalizeState_normalizeState eU eV eW X
  rw [hfun, List.map_id]

/-! Ground, executability, signature, and trust checks. -/

open NormalizedBinaryCarrier
open NormalizedBinaryReplay221

example :
    AllModeMove
      (U := CoordinateVector 2) (V := CoordinateVector 2)
      (W := CoordinateVector 1) S0 S1 :=
  .abc (.generatedFirstSplit
    (BinaryAmbientMoves.Coordinate.generatedFirstSplit_iff.mpr forwardSplit))

example :
    AllModeMove
        (U := CoordinateVector 2) (V := CoordinateVector 2)
        (W := CoordinateVector 1) S0 S1 ↔
      @NormalizedBinaryAllModeMove.AllModeMove (coordinateProfile 2 2 1)
        (normalizeState (LinearEquiv.refl F2 (Coord 2))
          (LinearEquiv.refl F2 (Coord 2)) (LinearEquiv.refl F2 (Coord 1)) S0)
        (normalizeState (LinearEquiv.refl F2 (Coord 2))
          (LinearEquiv.refl F2 (Coord 2)) (LinearEquiv.refl F2 (Coord 1)) S1) :=
  allModeMove_iff_normalized _ _ _ _ _

example :
    normalizeState (LinearEquiv.refl F2 (Coord 2))
        (LinearEquiv.refl F2 (Coord 2)) (LinearEquiv.refl F2 (Coord 1)) S0 =
      S0 := by
  rfl

#eval (normalizeState (LinearEquiv.refl F2 (Coord 2))
  (LinearEquiv.refl F2 (Coord 2)) (LinearEquiv.refl F2 (Coord 1)) S0).card

#check @allModeMove_iff_normalized
#check @normalizePath
#check @denormalizePath
#check @normalizePath_vertices
#check @denormalizePath_vertices
#check @normalizePath_length
#check @normalizePath_altitude
#check @denormalizePath_length
#check @denormalizePath_altitude
#check @normalizePath_denormalizePath_vertices
#check @denormalizePath_normalizePath_vertices

#print axioms allModeMove_iff_normalized
#print axioms normalizePath
#print axioms denormalizePath
#print axioms normalizePath_vertices
#print axioms denormalizePath_vertices
#print axioms normalizePath_length
#print axioms normalizePath_altitude
#print axioms denormalizePath_length
#print axioms denormalizePath_altitude
#print axioms normalizePath_denormalizePath_vertices
#print axioms denormalizePath_normalizePath_vertices

end BilinearComplexity.BinaryAmbientFullFrame
