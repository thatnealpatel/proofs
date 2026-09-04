import BilinearComplexity.NormalizedBinaryReplay221

set_option autoImplicit false

/-!
# Ordered factorwise transport of normalized binary moves

This module transports the three normalized binary move labels and their
concrete paths along injective additive maps in each corresponding factor.
The factors remain ordered: no mode permutation is performed or represented.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.NormalizedBinaryMoveTransport

open NormalizedBinaryCarrier
open NormalizedBinaryReplay221
open BinaryCircuit

/-- Three injective additive maps between the corresponding, ordered factor
spaces of profiles `p` and `q`. This structure does not permute factor modes. -/
structure FactorwiseAdditiveInjection (p q : Profile) where
  first : CoordinateVector p.first →+ CoordinateVector q.first
  second : CoordinateVector p.second →+ CoordinateVector q.second
  third : CoordinateVector p.third →+ CoordinateVector q.third
  first_injective : Function.Injective first
  second_injective : Function.Injective second
  third_injective : Function.Injective third

example (p : Profile) : Nonempty (FactorwiseAdditiveInjection p p) := by
  refine ⟨{
    first := AddMonoidHom.id (CoordinateVector p.first)
    second := AddMonoidHom.id (CoordinateVector p.second)
    third := AddMonoidHom.id (CoordinateVector p.third)
    first_injective := ?_
    second_injective := ?_
    third_injective := ?_ }⟩
  all_goals
    intro u v huv
    exact huv

/-- An injective additive map sends a nonzero coordinate vector to a nonzero
coordinate vector. -/
def mapNonzeroVector {a b : ℕ}
    (g : CoordinateVector a →+ CoordinateVector b)
    (hg : Function.Injective g) (u : NonzeroVector a) : NonzeroVector b :=
  ⟨g u.1, fun hzero => u.2 (hg (hzero.trans g.map_zero.symm))⟩

example {a : ℕ} (u : NonzeroVector a) :
    mapNonzeroVector (AddMonoidHom.id (CoordinateVector a))
      (fun _ _ huv => huv) u = u := by
  apply Subtype.ext
  rfl

/-- The carrier map induced by the three corresponding ordered factor maps. -/
def mapTerm {p q : Profile} (f : FactorwiseAdditiveInjection p q)
    (t : Carrier p) : Carrier q :=
  (mapNonzeroVector f.first f.first_injective t.1,
    mapNonzeroVector f.second f.second_injective t.2.1,
    mapNonzeroVector f.third f.third_injective t.2.2)

example {p q : Profile} (f : FactorwiseAdditiveInjection p q) (t : Carrier p) :
    (mapTerm f t).1.1 = f.first t.1.1 := rfl

/-- The finite-set state map induced by the carrier map. -/
def mapState {p q : Profile} (f : FactorwiseAdditiveInjection p q)
    (D : State p) : State q :=
  D.image (mapTerm f)

example {p q : Profile} (f : FactorwiseAdditiveInjection p q) :
    mapState f (∅ : State p) = ∅ := rfl

/-- The induced ordered carrier map is injective. -/
theorem mapTerm_injective {p q : Profile} (f : FactorwiseAdditiveInjection p q) :
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

/-- Mapping a state by an injective carrier map preserves its exact finite-set
cardinality. -/
@[simp] theorem mapState_card {p q : Profile}
    (f : FactorwiseAdditiveInjection p q) (D : State p) :
    (mapState f D).card = D.card := by
  exact Finset.card_image_of_injective D (mapTerm_injective f)

/-- A mapped source term belongs to the mapped state exactly when the source
term belongs to the source state. -/
@[simp] theorem mapState_mem {p q : Profile}
    (f : FactorwiseAdditiveInjection p q) {t : Carrier p} {D : State p} :
    mapTerm f t ∈ mapState f D ↔ t ∈ D := by
  constructor
  · intro hmem
    obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp hmem
    have heq : s = t := mapTerm_injective f hst
    simpa only [heq] using hs
  · intro hmem
    exact Finset.mem_image.mpr ⟨t, hmem, rfl⟩

/-- Mapping commutes exactly with erasing a term. -/
@[simp] theorem mapState_erase {p q : Profile}
    (f : FactorwiseAdditiveInjection p q) (D : State p) (t : Carrier p) :
    mapState f (D.erase t) = (mapState f D).erase (mapTerm f t) := by
  exact Finset.image_erase (mapTerm_injective f) D t

/-- Mapping commutes exactly with inserting a term. -/
@[simp] theorem mapState_insert {p q : Profile}
    (f : FactorwiseAdditiveInjection p q) (D : State p) (t : Carrier p) :
    mapState f (insert t D) = insert (mapTerm f t) (mapState f D) := by
  exact Finset.image_insert (mapTerm f) t D

/-- An ordered factorwise additive injection transports every membership,
freshness, formula, and exact-replacement clause of a generated first-factor
Split. -/
theorem transportGeneratedFirstSplit {p q : Profile}
    (f : FactorwiseAdditiveInjection p q)
    {source outputLeft outputRight : Carrier p} {D E : State p}
    (h : GeneratedFirstSplit source outputLeft outputRight D E) :
    GeneratedFirstSplit (mapTerm f source) (mapTerm f outputLeft)
      (mapTerm f outputRight) (mapState f D) (mapState f E) := by
  rcases h with ⟨hmem, hne, hfreshLeft, hfreshRight, hfirst, hleftSecond,
    hrightSecond, hleftThird, hrightThird, htarget⟩
  refine ⟨mapState_mem f |>.mpr hmem,
    fun heq => hne (mapTerm_injective f heq), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← mapState_erase]
    exact fun hmem => hfreshLeft (mapState_mem f |>.mp hmem)
  · rw [← mapState_erase]
    exact fun hmem => hfreshRight (mapState_mem f |>.mp hmem)
  · exact congrArg f.first hfirst |>.trans (f.first.map_add _ _)
  · exact congrArg f.second hleftSecond
  · exact congrArg f.second hrightSecond
  · exact congrArg f.third hleftThird
  · exact congrArg f.third hrightThird
  · rw [htarget, mapState_insert, mapState_insert, mapState_erase]

/-- An ordered factorwise additive injection transports every membership,
collision, additive/subtractive formula, and exact-replacement clause of a
source third-factor Flip without changing its orientation. -/
theorem transportSourceThirdFlip {p q : Profile}
    (f : FactorwiseAdditiveInjection p q)
    {sourceLeft sourceRight targetLeft targetRight : Carrier p} {D E : State p}
    (h : SourceThirdFlip sourceLeft sourceRight targetLeft targetRight D E) :
    SourceThirdFlip (mapTerm f sourceLeft) (mapTerm f sourceRight)
      (mapTerm f targetLeft) (mapTerm f targetRight)
      (mapState f D) (mapState f E) := by
  rcases h with ⟨hleftMem, hrightMem, hsources, hfreshLeft, hfreshRight,
    htargets, hsourceThird, htargetLeftFirst, htargetLeftSecond,
    htargetLeftThird, htargetRightFirst, htargetRightSecond, htargetRightThird,
    htarget⟩
  refine ⟨mapState_mem f |>.mpr hleftMem, mapState_mem f |>.mpr hrightMem,
    fun heq => hsources (mapTerm_injective f heq), ?_, ?_,
    fun heq => htargets (mapTerm_injective f heq), congrArg f.third hsourceThird,
    ?_, congrArg f.second htargetLeftSecond, congrArg f.third htargetLeftThird,
    congrArg f.first htargetRightFirst, ?_, congrArg f.third htargetRightThird, ?_⟩
  · rw [← mapState_erase, ← mapState_erase]
    exact fun hmem => hfreshLeft (mapState_mem f |>.mp hmem)
  · rw [← mapState_erase, ← mapState_erase]
    exact fun hmem => hfreshRight (mapState_mem f |>.mp hmem)
  · exact congrArg f.first htargetLeftFirst |>.trans (f.first.map_add _ _)
  · exact congrArg f.second htargetRightSecond |>.trans (f.second.map_sub _ _)
  · rw [htarget, mapState_insert, mapState_insert, mapState_erase, mapState_erase]

/-- An ordered factorwise additive injection transports every membership,
freshness, additive formula, and exact-replacement clause of a directed narrow
pair Reduction without reversing its source and target. -/
theorem transportDirectedNarrowPairReduction {p q : Profile}
    (f : FactorwiseAdditiveInjection p q)
    {sourceLeft sourceRight target : Carrier p} {D E : State p}
    (h : DirectedNarrowPairReduction sourceLeft sourceRight target D E) :
    DirectedNarrowPairReduction (mapTerm f sourceLeft) (mapTerm f sourceRight)
      (mapTerm f target) (mapState f D) (mapState f E) := by
  rcases h with ⟨hleftMem, hrightMem, hsources, hfresh, hsecond, hthird,
    htargetFirst, htargetSecond, htargetThird, htarget⟩
  refine ⟨mapState_mem f |>.mpr hleftMem, mapState_mem f |>.mpr hrightMem,
    fun heq => hsources (mapTerm_injective f heq), ?_, congrArg f.second hsecond,
    congrArg f.third hthird, ?_, congrArg f.second htargetSecond,
    congrArg f.third htargetThird, ?_⟩
  · rw [← mapState_erase, ← mapState_erase]
    exact fun hmem => hfresh (mapState_mem f |>.mp hmem)
  · exact congrArg f.first htargetFirst |>.trans (f.first.map_add _ _)
  · rw [htarget, mapState_insert, mapState_erase, mapState_erase]

/-- Transport of one typed move preserves its constructor label and its
intrinsic source-to-target orientation. -/
theorem transportMove {p q : Profile} (f : FactorwiseAdditiveInjection p q)
    {D E : State p} (h : @Move p D E) :
    @Move q (mapState f D) (mapState f E) := by
  cases h with
  | generatedFirstSplit hsplit =>
      exact .generatedFirstSplit (transportGeneratedFirstSplit f hsplit)
  | sourceThirdFlip hflip =>
      exact .sourceThirdFlip (transportSourceThirdFlip f hflip)
  | directedNarrowPairReduction hreduction =>
      exact .directedNarrowPairReduction
        (transportDirectedNarrowPairReduction f hreduction)

/-- Map a concrete dependent move path to concrete target-profile `MovePath`
data, preserving all constructor labels in their original order. -/
def mapPath {p q : Profile} (f : FactorwiseAdditiveInjection p q) :
    {D E : State p} → MovePath (@Move p) D E →
      MovePath (@Move q) (mapState f D) (mapState f E)
  | _, _, .singleton D => .singleton (mapState f D)
  | _, _, .snoc path h => .snoc (mapPath f path) (transportMove f h)

example {p q : Profile} (f : FactorwiseAdditiveInjection p q) (D : State p) :
    mapPath f (.singleton D : MovePath (@Move p) D D) =
      (.singleton (mapState f D) :
        MovePath (@Move q) (mapState f D) (mapState f D)) := by
  simp only [mapPath]

/-- The mapped dependent path has exactly the source vertex list mapped by
`mapState`. -/
theorem mapPath_vertices {p q : Profile} (f : FactorwiseAdditiveInjection p q)
    {D E : State p} (path : MovePath (@Move p) D E) :
    (mapPath f path).vertices = path.vertices.map (mapState f) := by
  induction path with
  | singleton =>
      simp only [mapPath, MovePath.vertices, List.map_singleton]
  | snoc path _ ih =>
      simp only [mapPath, MovePath.vertices, ih, List.map_append,
        List.map_singleton]

/-- Mapping a dependent path preserves its exact number of edges. -/
@[simp] theorem mapPath_length {p q : Profile}
    (f : FactorwiseAdditiveInjection p q)
    {D E : State p} (path : MovePath (@Move p) D E) :
    (mapPath f path).length = path.length := by
  induction path with
  | singleton =>
      simp only [mapPath, MovePath.length]
  | snoc path _ ih =>
      simp only [mapPath, MovePath.length, ih]

/-- Mapping a dependent path preserves its exact altitude because every mapped
finite-set vertex has exactly the source cardinality. -/
@[simp] theorem mapPath_altitude {p q : Profile}
    (f : FactorwiseAdditiveInjection p q)
    {D E : State p} (path : MovePath (@Move p) D E) :
    (mapPath f path).altitude = path.altitude := by
  induction path with
  | singleton =>
      simp only [mapPath, MovePath.altitude, mapState_card]
  | snoc path _ ih =>
      simp only [mapPath, MovePath.altitude, ih, mapState_card]

/-- A target state is a mapped path vertex exactly when it has a source
`PathVertex` witness with that mapped value. -/
theorem mapPath_pathVertex_iff {p q : Profile}
    (f : FactorwiseAdditiveInjection p q)
    {D E : State p} (path : MovePath (@Move p) D E) (Y : State q) :
    PathVertex (mapPath f path) Y ↔
      ∃ X, PathVertex path X ∧ mapState f X = Y := by
  simp only [PathVertex, mapPath_vertices, List.mem_map]

/-- Every source path vertex supplies the corresponding mapped target
`PathVertex` witness. -/
theorem mapPath_pathVertex {p q : Profile}
    (f : FactorwiseAdditiveInjection p q)
    {D E X : State p} {path : MovePath (@Move p) D E}
    (hX : PathVertex path X) : PathVertex (mapPath f path) (mapState f X) := by
  rw [PathVertex, mapPath_vertices]
  exact List.mem_map.mpr ⟨X, hX, rfl⟩

/-- If every source vertex is contained in a boundary, then every target
vertex is contained in the image of that same boundary. -/
theorem mapPath_confined {p q : Profile}
    (f : FactorwiseAdditiveInjection p q)
    {D E boundary : State p} (path : MovePath (@Move p) D E)
    (hconfined : ∀ X, PathVertex path X → X ⊆ boundary) :
    ∀ Y, PathVertex (mapPath f path) Y → Y ⊆ mapState f boundary := by
  intro Y hY
  obtain ⟨X, hX, hXY⟩ := (mapPath_pathVertex_iff f path Y).mp hY
  rw [← hXY]
  exact Finset.image_mono (mapTerm f) (hconfined X hX)

/-- The designated forward profile-221 replay mapped to an arbitrary target
profile by ordered factorwise injection, as actual target `MovePath` data. -/
def mapForwardPath {q : Profile} (f : FactorwiseAdditiveInjection profile221 q) :
    MovePath (@Move q) (mapState f S0) (mapState f S2) :=
  mapPath f forwardPath

example {q : Profile} (f : FactorwiseAdditiveInjection profile221 q) :
    mapForwardPath f = mapPath f forwardPath := rfl

/-- The designated reverse profile-221 replay mapped to an arbitrary target
profile by ordered factorwise injection, as actual target `MovePath` data. -/
def mapReversePath {q : Profile} (f : FactorwiseAdditiveInjection profile221 q) :
    MovePath (@Move q) (mapState f S2) (mapState f S0) :=
  mapPath f reversePath

example {q : Profile} (f : FactorwiseAdditiveInjection profile221 q) :
    mapReversePath f = mapPath f reversePath := rfl

/-- The generalized target move-preservation theorem gives exact endpoint
evaluation equality for every mapped dependent path. -/
theorem mapPath_preserves_evaluation {p q : Profile}
    (f : FactorwiseAdditiveInjection p q)
    {D E : State p} (path : MovePath (@Move p) D E) :
    stateEvaluation (mapState f E) = stateEvaluation (mapState f D) := by
  exact movePath_preserves_evaluation (mapPath f path)

#check @FactorwiseAdditiveInjection
#check @mapNonzeroVector
#check @mapTerm
#check @mapState
#check @mapTerm_injective
#check @mapPath
#check @mapForwardPath
#check @mapReversePath

#print axioms mapTerm_injective
#print axioms transportMove
#print axioms mapPath_vertices
#print axioms mapPath_preserves_evaluation

end BilinearComplexity.NormalizedBinaryMoveTransport
