import BilinearComplexity.BinaryAmbientMoves

set_option autoImplicit false

/-!
# Transport normalized moves into arbitrary binary factor spaces

Injective factorwise linear maps send normalized coordinate terms and states to
ambient terms and states.  This module proves transport of every intrinsic
primitive and every mixed all-mode edge, and recursively transports concrete
`BinaryCircuit.MovePath` data while preserving its exact vertices, length, and
altitude.
-/

namespace BilinearComplexity.BinaryAmbientMoveTransport

open BinaryCircuit
open BinaryAmbientCarrier
open BinaryAmbientMoves
open NormalizedBinaryCarrier (F2 CoordinateVector Profile)

universe u v w

variable {U : Type u} {V : Type v} {W : Type w}
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [Module F2 U] [Module F2 V] [Module F2 W]
variable [DecidableEq U] [DecidableEq V] [DecidableEq W]

/-- Injective linear coordinate maps into the three ordered ambient factor
spaces.  No surjectivity or basis choice is included. -/
structure CoordinateEmbedding (p : Profile) (U : Type u) (V : Type v)
    (W : Type w) [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W] where
  /-- Linear map for the first factor. -/
  first : CoordinateVector p.first →ₗ[F2] U
  /-- Linear map for the second factor. -/
  second : CoordinateVector p.second →ₗ[F2] V
  /-- Linear map for the third factor. -/
  third : CoordinateVector p.third →ₗ[F2] W
  /-- The first factor map is injective. -/
  first_injective : Function.Injective first
  /-- The second factor map is injective. -/
  second_injective : Function.Injective second
  /-- The third factor map is injective. -/
  third_injective : Function.Injective third

/-- An injective linear map sends a nonzero vector to a nonzero vector. -/
def mapNonzeroVector {X : Type*} {Y : Type*}
    [AddCommGroup X] [AddCommGroup Y] [Module F2 X] [Module F2 Y]
    (g : X →ₗ[F2] Y) (hg : Function.Injective g)
    (x : NonzeroVector X) : NonzeroVector Y :=
  ⟨g x.1, fun hzero => x.2 (hg (hzero.trans g.map_zero.symm))⟩

/-- Map a normalized coordinate term factorwise into the ambient carrier. -/
def mapTerm {p : Profile} (f : CoordinateEmbedding p U V W)
    (t : NormalizedBinaryCarrier.Carrier p) : Carrier U V W :=
  (mapNonzeroVector f.first f.first_injective t.1,
    mapNonzeroVector f.second f.second_injective t.2.1,
    mapNonzeroVector f.third f.third_injective t.2.2)

/-- Map a normalized finite-set state into the ambient finite-set state. -/
def mapState {p : Profile} (f : CoordinateEmbedding p U V W)
    (D : NormalizedBinaryCarrier.State p) : State U V W :=
  D.image (mapTerm f)

omit [DecidableEq U] [DecidableEq V] [DecidableEq W] in
/-- The factorwise map on normalized terms is injective. -/
theorem mapTerm_injective {p : Profile} (f : CoordinateEmbedding p U V W) :
    Function.Injective (mapTerm f) := by
  intro s t hst
  apply Prod.ext
  · apply Subtype.ext
    exact f.first_injective (congrArg (fun z => z.1.1) hst)
  · apply Prod.ext
    · apply Subtype.ext
      exact f.second_injective (congrArg (fun z => z.2.1.1) hst)
    · apply Subtype.ext
      exact f.third_injective (congrArg (fun z => z.2.2.1) hst)

/-- A mapped source term belongs to the mapped state exactly when the source
term belongs to the coordinate state. -/
@[simp] theorem mapState_mem {p : Profile} (f : CoordinateEmbedding p U V W)
    {t : NormalizedBinaryCarrier.Carrier p}
    {D : NormalizedBinaryCarrier.State p} :
    mapTerm f t ∈ mapState f D ↔ t ∈ D := by
  constructor
  · intro hmem
    obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp hmem
    have heq : s = t := mapTerm_injective f hst
    simpa only [heq] using hs
  · intro hmem
    exact Finset.mem_image.mpr ⟨t, hmem, rfl⟩

/-- Mapping coordinate states commutes with finite-set union. -/
@[simp] theorem mapState_union {p : Profile} (f : CoordinateEmbedding p U V W)
    (D E : NormalizedBinaryCarrier.State p) :
    mapState f (D ∪ E) = mapState f D ∪ mapState f E := by
  exact Finset.image_union D E

/-- Mapping by injective factor maps preserves exact state cardinality. -/
@[simp] theorem mapState_card {p : Profile} (f : CoordinateEmbedding p U V W)
    (D : NormalizedBinaryCarrier.State p) :
    (mapState f D).card = D.card := by
  exact Finset.card_image_of_injective D (mapTerm_injective f)

/-- Mapping commutes exactly with erasing a source term. -/
@[simp] theorem mapState_erase {p : Profile} (f : CoordinateEmbedding p U V W)
    (D : NormalizedBinaryCarrier.State p)
    (t : NormalizedBinaryCarrier.Carrier p) :
    mapState f (D.erase t) = (mapState f D).erase (mapTerm f t) := by
  exact Finset.image_erase (mapTerm_injective f) D t

/-- Mapping commutes exactly with inserting a source term. -/
@[simp] theorem mapState_insert {p : Profile} (f : CoordinateEmbedding p U V W)
    (D : NormalizedBinaryCarrier.State p)
    (t : NormalizedBinaryCarrier.Carrier p) :
    mapState f (insert t D) = insert (mapTerm f t) (mapState f D) := by
  exact Finset.image_insert (mapTerm f) t D

/-- Factorwise linear embedding transports every clause of an intrinsic
coordinate first-mode Split. -/
theorem transportGeneratedFirstSplit {p : Profile}
    (f : CoordinateEmbedding p U V W)
    {source outputLeft outputRight : NormalizedBinaryCarrier.Carrier p}
    {D E : NormalizedBinaryCarrier.State p}
    (h : BinaryAmbientMoves.GeneratedFirstSplit
      (U := CoordinateVector p.first) (V := CoordinateVector p.second)
      (W := CoordinateVector p.third)
      source outputLeft outputRight D E) :
    BinaryAmbientMoves.GeneratedFirstSplit
      (mapTerm f source) (mapTerm f outputLeft) (mapTerm f outputRight)
      (mapState f D) (mapState f E) := by
  rcases h with ⟨hmem, hne, hfreshLeft, hfreshRight, hfirst, hleftSecond,
    hrightSecond, hleftThird, hrightThird, htarget⟩
  refine ⟨(mapState_mem f).mpr hmem,
    fun heq => hne (mapTerm_injective f heq), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← mapState_erase]
    exact fun hmem' => hfreshLeft ((mapState_mem f).mp hmem')
  · rw [← mapState_erase]
    exact fun hmem' => hfreshRight ((mapState_mem f).mp hmem')
  · exact congrArg f.first hfirst |>.trans (f.first.map_add _ _)
  · exact congrArg f.second hleftSecond
  · exact congrArg f.second hrightSecond
  · exact congrArg f.third hleftThird
  · exact congrArg f.third hrightThird
  · rw [htarget, mapState_insert, mapState_insert, mapState_erase]

/-- Factorwise linear embedding transports every clause of an intrinsic
coordinate ordered Flip, including its subtraction formula and order. -/
theorem transportSourceThirdFlip {p : Profile}
    (f : CoordinateEmbedding p U V W)
    {sourceLeft sourceRight targetLeft targetRight :
      NormalizedBinaryCarrier.Carrier p}
    {D E : NormalizedBinaryCarrier.State p}
    (h : BinaryAmbientMoves.SourceThirdFlip
      (U := CoordinateVector p.first) (V := CoordinateVector p.second)
      (W := CoordinateVector p.third)
      sourceLeft sourceRight targetLeft targetRight D E) :
    BinaryAmbientMoves.SourceThirdFlip
      (mapTerm f sourceLeft) (mapTerm f sourceRight)
      (mapTerm f targetLeft) (mapTerm f targetRight)
      (mapState f D) (mapState f E) := by
  rcases h with ⟨hleftMem, hrightMem, hsources, hfreshLeft, hfreshRight,
    htargets, hsourceThird, htargetLeftFirst, htargetLeftSecond,
    htargetLeftThird, htargetRightFirst, htargetRightSecond, htargetRightThird,
    htarget⟩
  refine ⟨(mapState_mem f).mpr hleftMem, (mapState_mem f).mpr hrightMem,
    fun heq => hsources (mapTerm_injective f heq), ?_, ?_,
    fun heq => htargets (mapTerm_injective f heq), congrArg f.third hsourceThird,
    ?_, congrArg f.second htargetLeftSecond, congrArg f.third htargetLeftThird,
    congrArg f.first htargetRightFirst, ?_, congrArg f.third htargetRightThird, ?_⟩
  · rw [← mapState_erase, ← mapState_erase]
    exact fun hmem' => hfreshLeft ((mapState_mem f).mp hmem')
  · rw [← mapState_erase, ← mapState_erase]
    exact fun hmem' => hfreshRight ((mapState_mem f).mp hmem')
  · exact congrArg f.first htargetLeftFirst |>.trans (f.first.map_add _ _)
  · exact congrArg f.second htargetRightSecond |>.trans (f.second.map_sub _ _)
  · rw [htarget, mapState_insert, mapState_insert, mapState_erase, mapState_erase]

/-- Factorwise linear embedding transports every clause of an intrinsic
coordinate directed Reduction without reversing its endpoints. -/
theorem transportDirectedNarrowPairReduction {p : Profile}
    (f : CoordinateEmbedding p U V W)
    {sourceLeft sourceRight target : NormalizedBinaryCarrier.Carrier p}
    {D E : NormalizedBinaryCarrier.State p}
    (h : BinaryAmbientMoves.DirectedNarrowPairReduction
      (U := CoordinateVector p.first) (V := CoordinateVector p.second)
      (W := CoordinateVector p.third)
      sourceLeft sourceRight target D E) :
    BinaryAmbientMoves.DirectedNarrowPairReduction
      (mapTerm f sourceLeft) (mapTerm f sourceRight) (mapTerm f target)
      (mapState f D) (mapState f E) := by
  rcases h with ⟨hleftMem, hrightMem, hsources, hfresh, hsecond, hthird,
    htargetFirst, htargetSecond, htargetThird, htarget⟩
  refine ⟨(mapState_mem f).mpr hleftMem, (mapState_mem f).mpr hrightMem,
    fun heq => hsources (mapTerm_injective f heq), ?_, congrArg f.second hsecond,
    congrArg f.third hthird, ?_, congrArg f.second htargetSecond,
    congrArg f.third htargetThird, ?_⟩
  · rw [← mapState_erase, ← mapState_erase]
    exact fun hmem' => hfresh ((mapState_mem f).mp hmem')
  · exact congrArg f.first htargetFirst |>.trans (f.first.map_add _ _)
  · rw [htarget, mapState_insert, mapState_erase, mapState_erase]

/-- Transport one intrinsic ordered coordinate move, preserving its constructor
and endpoint direction. -/
theorem transportMove {p : Profile} (f : CoordinateEmbedding p U V W)
    {D E : NormalizedBinaryCarrier.State p}
    (h : BinaryAmbientMoves.Move
      (U := CoordinateVector p.first) (V := CoordinateVector p.second)
      (W := CoordinateVector p.third) D E) :
    BinaryAmbientMoves.Move (U := U) (V := V) (W := W)
      (mapState f D) (mapState f E) := by
  cases h with
  | generatedFirstSplit hsplit =>
      exact .generatedFirstSplit (transportGeneratedFirstSplit f hsplit)
  | sourceThirdFlip hflip =>
      exact .sourceThirdFlip (transportSourceThirdFlip f hflip)
  | directedNarrowPairReduction hreduction =>
      exact .directedNarrowPairReduction
        (transportDirectedNarrowPairReduction f hreduction)

private theorem mapState_permuteBCA {p : Profile}
    (f : CoordinateEmbedding p U V W)
    (g : CoordinateEmbedding ⟨p.third, p.first, p.second⟩ W U V)
    (hfirst : g.first = f.third) (hsecond : g.second = f.first)
    (hthird : g.third = f.second)
    (D : NormalizedBinaryCarrier.State ⟨p.third, p.first, p.second⟩) :
    mapState f (BinaryAmbientMoves.permuteBCAState D) =
      BinaryAmbientMoves.permuteBCAState (mapState g D) := by
  simp only [mapState, BinaryAmbientMoves.permuteBCAState, Finset.image_image]
  apply Finset.image_congr
  intro t _ht
  simp only [Function.comp_apply]
  apply Prod.ext
  · apply Subtype.ext
    exact (congrArg (fun k => k t.2.1.1) hsecond).symm
  · apply Prod.ext
    · apply Subtype.ext
      exact (congrArg (fun k => k t.2.2.1) hthird).symm
    · apply Subtype.ext
      exact (congrArg (fun k => k t.1.1) hfirst).symm

private theorem mapState_permuteCAB {p : Profile}
    (f : CoordinateEmbedding p U V W)
    (g : CoordinateEmbedding ⟨p.second, p.third, p.first⟩ V W U)
    (hfirst : g.first = f.second) (hsecond : g.second = f.third)
    (hthird : g.third = f.first)
    (D : NormalizedBinaryCarrier.State ⟨p.second, p.third, p.first⟩) :
    mapState f (BinaryAmbientMoves.permuteCABState D) =
      BinaryAmbientMoves.permuteCABState (mapState g D) := by
  simp only [mapState, BinaryAmbientMoves.permuteCABState, Finset.image_image]
  apply Finset.image_congr
  intro t _ht
  simp only [Function.comp_apply]
  apply Prod.ext
  · apply Subtype.ext
    exact (congrArg (fun k => k t.2.2.1) hthird).symm
  · apply Prod.ext
    · apply Subtype.ext
      exact (congrArg (fun k => k t.1.1) hfirst).symm
    · apply Subtype.ext
      exact (congrArg (fun k => k t.2.1.1) hsecond).symm

private theorem mapState_permuteACB {p : Profile}
    (f : CoordinateEmbedding p U V W)
    (g : CoordinateEmbedding ⟨p.first, p.third, p.second⟩ U W V)
    (hfirst : g.first = f.first) (hsecond : g.second = f.third)
    (hthird : g.third = f.second)
    (D : NormalizedBinaryCarrier.State ⟨p.first, p.third, p.second⟩) :
    mapState f (BinaryAmbientMoves.permuteACBState D) =
      BinaryAmbientMoves.permuteACBState (mapState g D) := by
  simp only [mapState, BinaryAmbientMoves.permuteACBState, Finset.image_image]
  apply Finset.image_congr
  intro t _ht
  simp only [Function.comp_apply]
  apply Prod.ext
  · apply Subtype.ext
    exact (congrArg (fun k => k t.1.1) hfirst).symm
  · apply Prod.ext
    · apply Subtype.ext
      exact (congrArg (fun k => k t.2.2.1) hthird).symm
    · apply Subtype.ext
      exact (congrArg (fun k => k t.2.1.1) hsecond).symm

private theorem mapState_permuteCBA {p : Profile}
    (f : CoordinateEmbedding p U V W)
    (g : CoordinateEmbedding ⟨p.third, p.second, p.first⟩ W V U)
    (hfirst : g.first = f.third) (hsecond : g.second = f.second)
    (hthird : g.third = f.first)
    (D : NormalizedBinaryCarrier.State ⟨p.third, p.second, p.first⟩) :
    mapState f (BinaryAmbientMoves.permuteCBAState D) =
      BinaryAmbientMoves.permuteCBAState (mapState g D) := by
  simp only [mapState, BinaryAmbientMoves.permuteCBAState, Finset.image_image]
  apply Finset.image_congr
  intro t _ht
  simp only [Function.comp_apply]
  apply Prod.ext
  · apply Subtype.ext
    exact (congrArg (fun k => k t.2.2.1) hthird).symm
  · apply Prod.ext
    · apply Subtype.ext
      exact (congrArg (fun k => k t.2.1.1) hsecond).symm
    · apply Subtype.ext
      exact (congrArg (fun k => k t.1.1) hfirst).symm

private theorem mapState_permuteBAC {p : Profile}
    (f : CoordinateEmbedding p U V W)
    (g : CoordinateEmbedding ⟨p.second, p.first, p.third⟩ V U W)
    (hfirst : g.first = f.second) (hsecond : g.second = f.first)
    (hthird : g.third = f.third)
    (D : NormalizedBinaryCarrier.State ⟨p.second, p.first, p.third⟩) :
    mapState f (BinaryAmbientMoves.permuteBACState D) =
      BinaryAmbientMoves.permuteBACState (mapState g D) := by
  simp only [mapState, BinaryAmbientMoves.permuteBACState, Finset.image_image]
  apply Finset.image_congr
  intro t _ht
  simp only [Function.comp_apply]
  apply Prod.ext
  · apply Subtype.ext
    exact (congrArg (fun k => k t.2.1.1) hsecond).symm
  · apply Prod.ext
    · apply Subtype.ext
      exact (congrArg (fun k => k t.1.1) hfirst).symm
    · apply Subtype.ext
      exact (congrArg (fun k => k t.2.2.1) hthird).symm

/-- Transport an intrinsic coordinate all-mode edge along arbitrary injective
factorwise linear maps.  Each of the six mode permutations is retained. -/
theorem transportCoordinateAllModeMove {p : Profile}
    (f : CoordinateEmbedding p U V W) {D E : NormalizedBinaryCarrier.State p}
    (h : BinaryAmbientMoves.AllModeMove
      (U := CoordinateVector p.first) (V := CoordinateVector p.second)
      (W := CoordinateVector p.third) D E) :
    BinaryAmbientMoves.AllModeMove (U := U) (V := V) (W := W)
      (mapState f D) (mapState f E) := by
  cases h with
  | abc hmove => exact .abc (transportMove f hmove)
  | @bca D₀ E₀ _ _ hmove hD hE =>
      let g : CoordinateEmbedding ⟨p.third, p.first, p.second⟩ W U V := {
        first := f.third
        second := f.first
        third := f.second
        first_injective := f.third_injective
        second_injective := f.first_injective
        third_injective := f.second_injective }
      refine .bca (transportMove g hmove) ?_ ?_
      · rw [hD]
        exact mapState_permuteBCA f g rfl rfl rfl D₀
      · rw [hE]
        exact mapState_permuteBCA f g rfl rfl rfl E₀
  | @cab D₀ E₀ _ _ hmove hD hE =>
      let g : CoordinateEmbedding ⟨p.second, p.third, p.first⟩ V W U := {
        first := f.second
        second := f.third
        third := f.first
        first_injective := f.second_injective
        second_injective := f.third_injective
        third_injective := f.first_injective }
      refine .cab (transportMove g hmove) ?_ ?_
      · rw [hD]
        exact mapState_permuteCAB f g rfl rfl rfl D₀
      · rw [hE]
        exact mapState_permuteCAB f g rfl rfl rfl E₀
  | @acb D₀ E₀ _ _ hmove hD hE =>
      let g : CoordinateEmbedding ⟨p.first, p.third, p.second⟩ U W V := {
        first := f.first
        second := f.third
        third := f.second
        first_injective := f.first_injective
        second_injective := f.third_injective
        third_injective := f.second_injective }
      refine .acb (transportMove g hmove) ?_ ?_
      · rw [hD]
        exact mapState_permuteACB f g rfl rfl rfl D₀
      · rw [hE]
        exact mapState_permuteACB f g rfl rfl rfl E₀
  | @cba D₀ E₀ _ _ hmove hD hE =>
      let g : CoordinateEmbedding ⟨p.third, p.second, p.first⟩ W V U := {
        first := f.third
        second := f.second
        third := f.first
        first_injective := f.third_injective
        second_injective := f.second_injective
        third_injective := f.first_injective }
      refine .cba (transportMove g hmove) ?_ ?_
      · rw [hD]
        exact mapState_permuteCBA f g rfl rfl rfl D₀
      · rw [hE]
        exact mapState_permuteCBA f g rfl rfl rfl E₀
  | @bac D₀ E₀ _ _ hmove hD hE =>
      let g : CoordinateEmbedding ⟨p.second, p.first, p.third⟩ V U W := {
        first := f.second
        second := f.first
        third := f.third
        first_injective := f.second_injective
        second_injective := f.first_injective
        third_injective := f.third_injective }
      refine .bac (transportMove g hmove) ?_ ?_
      · rw [hD]
        exact mapState_permuteBAC f g rfl rfl rfl D₀
      · rw [hE]
        exact mapState_permuteBAC f g rfl rfl rfl E₀

/-- Transport a normalized all-mode edge to intrinsic ambient all-mode
legality.  This uses only injectivity and linearity, never surjectivity or
tensor covariance. -/
theorem transportNormalizedAllModeMove {p : Profile}
    (f : CoordinateEmbedding p U V W) {D E : NormalizedBinaryCarrier.State p}
    (h : @NormalizedBinaryAllModeMove.AllModeMove p D E) :
    BinaryAmbientMoves.AllModeMove (U := U) (V := V) (W := W)
      (mapState f D) (mapState f E) := by
  apply transportCoordinateAllModeMove f
  exact BinaryAmbientMoves.Coordinate.allModeMove_iff_normalized.mpr h

/-- Recursively map a concrete normalized all-mode path to intrinsic ambient
`MovePath` data. -/
def mapPath {p : Profile} (f : CoordinateEmbedding p U V W) :
    {D E : NormalizedBinaryCarrier.State p} →
      MovePath (@NormalizedBinaryAllModeMove.AllModeMove p) D E →
      MovePath (BinaryAmbientMoves.AllModeMove (U := U) (V := V) (W := W))
        (mapState f D) (mapState f E)
  | _, _, .singleton D => .singleton (mapState f D)
  | _, _, .snoc path h =>
      .snoc (mapPath f path) (transportNormalizedAllModeMove f h)

/-- The ambient path records exactly the pointwise images of the normalized
vertex list. -/
theorem mapPath_vertices {p : Profile} (f : CoordinateEmbedding p U V W)
    {D E : NormalizedBinaryCarrier.State p}
    (path : MovePath (@NormalizedBinaryAllModeMove.AllModeMove p) D E) :
    (mapPath f path).vertices = path.vertices.map (mapState f) := by
  induction path with
  | singleton =>
      simp only [mapPath, MovePath.vertices, List.map_singleton]
  | snoc path _ ih =>
      simp only [mapPath, MovePath.vertices, ih, List.map_append,
        List.map_singleton]

/-- Coordinate-to-ambient path transport preserves the exact edge count. -/
@[simp] theorem mapPath_length {p : Profile} (f : CoordinateEmbedding p U V W)
    {D E : NormalizedBinaryCarrier.State p}
    (path : MovePath (@NormalizedBinaryAllModeMove.AllModeMove p) D E) :
    (mapPath f path).length = path.length := by
  induction path with
  | singleton => simp only [mapPath, MovePath.length]
  | snoc path _ ih => simp only [mapPath, MovePath.length, ih]

/-- Coordinate-to-ambient path transport preserves exact altitude because it
preserves every finite-set vertex cardinality. -/
@[simp] theorem mapPath_altitude {p : Profile} (f : CoordinateEmbedding p U V W)
    {D E : NormalizedBinaryCarrier.State p}
    (path : MovePath (@NormalizedBinaryAllModeMove.AllModeMove p) D E) :
    (mapPath f path).altitude = path.altitude := by
  induction path with
  | singleton => simp only [mapPath, MovePath.altitude, mapState_card]
  | snoc path _ ih =>
      simp only [mapPath, MovePath.altitude, ih, mapState_card]

/-- An ambient state is a transported path vertex exactly when it is the image
of an actual normalized source vertex. -/
theorem mapPath_pathVertex_iff {p : Profile}
    (f : CoordinateEmbedding p U V W)
    {D E : NormalizedBinaryCarrier.State p}
    (path : MovePath (@NormalizedBinaryAllModeMove.AllModeMove p) D E)
    (Y : State U V W) :
    PathVertex (mapPath f path) Y ↔
      ∃ X, PathVertex path X ∧ mapState f X = Y := by
  simp only [PathVertex, mapPath_vertices, List.mem_map]

/-- Every normalized path vertex gives its corresponding ambient path vertex. -/
theorem mapPath_pathVertex {p : Profile} (f : CoordinateEmbedding p U V W)
    {D E X : NormalizedBinaryCarrier.State p}
    {path : MovePath (@NormalizedBinaryAllModeMove.AllModeMove p) D E}
    (hX : PathVertex path X) :
    PathVertex (mapPath f path) (mapState f X) := by
  rw [PathVertex, mapPath_vertices]
  exact List.mem_map.mpr ⟨X, hX, rfl⟩

/-! Ground and specification checks. -/

open NormalizedBinaryCarrier
open NormalizedBinaryReplay221

example (p : Profile) :
    Nonempty (CoordinateEmbedding p (CoordinateVector p.first)
      (CoordinateVector p.second) (CoordinateVector p.third)) := by
  refine ⟨{
    first := LinearMap.id
    second := LinearMap.id
    third := LinearMap.id
    first_injective := ?_
    second_injective := ?_
    third_injective := ?_ }⟩
  all_goals
    intro x y hxy
    exact hxy

example {p : Profile} (f : CoordinateEmbedding p U V W)
    (t : NormalizedBinaryCarrier.Carrier p) :
    (mapTerm f t).1.1 = f.first t.1.1 := rfl

example {p : Profile} (f : CoordinateEmbedding p U V W) :
    mapState f (∅ : NormalizedBinaryCarrier.State p) = ∅ := rfl

example {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Module F2 X] [Module F2 Y] (x : NonzeroVector X) :
    mapNonzeroVector (LinearMap.id (R := F2) (M := X))
      (fun _ _ h => h) x = x := by
  apply Subtype.ext
  rfl

example (f : CoordinateEmbedding profile221 U V W) :
    BinaryAmbientMoves.AllModeMove (U := U) (V := V) (W := W)
      (mapState f S0) (mapState f S1) :=
  transportNormalizedAllModeMove f
    (NormalizedBinaryAllModeMove.allModeMove_of_move
      (.generatedFirstSplit forwardSplit))

example (f : CoordinateEmbedding profile221 U V W) :
    (mapPath f
      (MovePath.one
        (NormalizedBinaryAllModeMove.allModeMove_of_move
          (.generatedFirstSplit forwardSplit)))).length = 1 := by
  rw [mapPath_length]
  simp only [MovePath.one, MovePath.length]

#check @CoordinateEmbedding
#check @mapNonzeroVector
#check @mapTerm
#check @mapState
#check @mapTerm_injective
#check @mapState_union
#check @transportGeneratedFirstSplit
#check @transportSourceThirdFlip
#check @transportDirectedNarrowPairReduction
#check @transportNormalizedAllModeMove
#check @mapPath
#check @mapPath_vertices
#check @mapPath_length
#check @mapPath_altitude
#check @mapPath_pathVertex_iff
#print axioms mapTerm_injective
#print axioms transportNormalizedAllModeMove
#print axioms mapPath_vertices
#print axioms mapPath_pathVertex_iff

end BilinearComplexity.BinaryAmbientMoveTransport
