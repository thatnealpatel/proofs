import BilinearComplexity.NormalizedBinaryAllModeMove
import BilinearComplexity.NormalizedBinaryMoveTransport

set_option autoImplicit false

/-!
# Factorwise transport of fixed-profile all-mode moves

This module transports `AllModeMove` edges and mixed-orientation paths along
ordered factorwise additive injections.  For each edge, its orientation is
used to reorder the three component maps before transporting the underlying
ordered move.  The same orientation and operation tag/direction are then
reintroduced as proof-level existential witnesses.

The component reordering is a semiconjugacy construction.  It uses no inverse
linear maps, proves no reflection result for injections, and does not make the
existential labels computationally extractable.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.NormalizedBinaryAllModeMoveTransport

open BinaryCircuit
open NormalizedBinaryCarrier
open NormalizedBinaryReplay221
open NormalizedBinaryModePermutation
open NormalizedBinaryMoveTransport
open NormalizedBinaryAllModeMove
open Scheme.Action

/-- Reorder a target profile back through an orientation.  This only inverts
the six mode positions; it does not contain or induce inverse linear maps. -/
def inversePermProfile (o : Orientation) (r : Profile) : Profile :=
  match o with
  | .abc => ⟨r.first, r.second, r.third⟩
  | .bca => ⟨r.third, r.first, r.second⟩
  | .cab => ⟨r.second, r.third, r.first⟩
  | .acb => ⟨r.first, r.third, r.second⟩
  | .cba => ⟨r.third, r.second, r.first⟩
  | .bac => ⟨r.second, r.first, r.third⟩

example : inversePermProfile .bca ⟨2, 3, 5⟩ = ⟨5, 2, 3⟩ := rfl

/-- Applying an orientation after reordering its target profile recovers the
original target profile. -/
theorem permProfile_inversePermProfile (o : Orientation) (r : Profile) :
    permProfile o (inversePermProfile o r) = r := by
  cases o <;> cases r <;> rfl

/-- Reorder the three component maps of a factorwise additive injection through
an orientation.  This is the injection part of a semiconjugacy: it selects the
reviewed source-mode component for each slot and reuses its injectivity proof.
It does not construct or assume inverse linear maps. -/
def reorderFactorwiseAdditiveInjection {p r : Profile} (o : Orientation)
    (f : FactorwiseAdditiveInjection (permProfile o p) r) :
    FactorwiseAdditiveInjection p (inversePermProfile o r) :=
  match o with
  | .abc =>
      { first := f.first
        second := f.second
        third := f.third
        first_injective := f.first_injective
        second_injective := f.second_injective
        third_injective := f.third_injective }
  | .bca =>
      { first := f.third
        second := f.first
        third := f.second
        first_injective := f.third_injective
        second_injective := f.first_injective
        third_injective := f.second_injective }
  | .cab =>
      { first := f.second
        second := f.third
        third := f.first
        first_injective := f.second_injective
        second_injective := f.third_injective
        third_injective := f.first_injective }
  | .acb =>
      { first := f.first
        second := f.third
        third := f.second
        first_injective := f.first_injective
        second_injective := f.third_injective
        third_injective := f.second_injective }
  | .cba =>
      { first := f.third
        second := f.second
        third := f.first
        first_injective := f.third_injective
        second_injective := f.second_injective
        third_injective := f.first_injective }
  | .bac =>
      { first := f.second
        second := f.first
        third := f.third
        first_injective := f.second_injective
        second_injective := f.first_injective
        third_injective := f.third_injective }

example {p r : Profile}
    (f : FactorwiseAdditiveInjection (permProfile .bca p) r) :
    (reorderFactorwiseAdditiveInjection .bca f).first = f.third := rfl

/-- Mapping a term after orienting it is heterogeneously equal to orienting the
term mapped by the reordered factorwise injection.  The heterogeneous equality
is the canonical cast-free term-level semiconjugacy statement. -/
theorem mapTerm_permuteTerm_reorderFactorwiseAdditiveInjection
    {p r : Profile} (o : Orientation)
    (f : FactorwiseAdditiveInjection (permProfile o p) r) (t : Carrier p) :
    mapTerm f (permuteTerm o t) ≍
      permuteTerm o (mapTerm (reorderFactorwiseAdditiveInjection o f) t) := by
  cases o <;> cases p <;> cases r <;> rfl

/-- Pulling a mapped oriented state back along the recovered-profile equality
is exactly the oriented state mapped by the reordered injection.  Its cast
direction matches the endpoint casts in `AllModeMove`. -/
theorem cast_mapState_permute_reorderFactorwiseAdditiveInjection
    {p r : Profile} (o : Orientation)
    (f : FactorwiseAdditiveInjection (permProfile o p) r) (D : State p) :
    cast (congrArg State (permProfile_inversePermProfile o r).symm)
        (mapState f (permuteState o D)) =
      permuteState o
        (mapState (reorderFactorwiseAdditiveInjection o f) D) := by
  cases o <;> cases p <;> cases r <;>
    simp only [permuteState, mapState, Finset.image_image]
  all_goals
    apply Finset.image_congr
    intro t _
    rfl

example :
    ∃ _f : FactorwiseAdditiveInjection profile221 profile221,
      @AllModeMove profile221 S0 S1 := by
  refine ⟨{
    first := AddMonoidHom.id (CoordinateVector profile221.first)
    second := AddMonoidHom.id (CoordinateVector profile221.second)
    third := AddMonoidHom.id (CoordinateVector profile221.third)
    first_injective := fun _ _ hxy => hxy
    second_injective := fun _ _ hxy => hxy
    third_injective := fun _ _ hxy => hxy }, allModeMove_identity_nonempty⟩

/-- An ordered factorwise additive injection transports an all-mode edge while
reusing its exact orientation and corresponding operation tag/direction as
proof-level existential witnesses. -/
theorem transportAllModeMove {q r : Profile}
    (f : FactorwiseAdditiveInjection q r) {D E : State q}
    (h : @AllModeMove q D E) :
    @AllModeMove r (mapState f D) (mapState f E) := by
  rcases h with ⟨p, o, rfl, hmove⟩
  have hmove' : @OrientationMove p o D E := by
    simpa using hmove
  obtain ⟨D₀, E₀, hold, hD, hE⟩ := hmove'.provenance
  let p' := inversePermProfile o r
  let g : FactorwiseAdditiveInjection p p' :=
    reorderFactorwiseAdditiveInjection o f
  let hp' : permProfile o p' = r := permProfile_inversePermProfile o r
  refine ⟨p', o, hp', ?_⟩
  have htransport : @Move p' (mapState g D₀) (mapState g E₀) :=
    NormalizedBinaryMoveTransport.transportMove g hold
  have horiented := permuteMove o htransport
  rw [hD, hE]
  change @OrientationMove p' o
    (cast (congrArg State hp'.symm) (mapState f (permuteState o D₀)))
    (cast (congrArg State hp'.symm) (mapState f (permuteState o E₀)))
  rw [cast_mapState_permute_reorderFactorwiseAdditiveInjection,
    cast_mapState_permute_reorderFactorwiseAdditiveInjection]
  exact horiented

/-- Map a concrete mixed-orientation all-mode path by transporting each edge
independently along the same ordered factorwise additive injection. -/
def mapAllModePath {q r : Profile} (f : FactorwiseAdditiveInjection q r) :
    {D E : State q} → MovePath (@AllModeMove q) D E →
      MovePath (@AllModeMove r) (mapState f D) (mapState f E)
  | _, _, .singleton D => .singleton (mapState f D)
  | _, _, .snoc path h =>
      .snoc (mapAllModePath f path) (transportAllModeMove f h)

example {q r : Profile} (f : FactorwiseAdditiveInjection q r) (D : State q) :
    mapAllModePath f (.singleton D : MovePath (@AllModeMove q) D D) =
      (.singleton (mapState f D) :
        MovePath (@AllModeMove r) (mapState f D) (mapState f D)) := by
  simp only [mapAllModePath]

/-- Mapping a mixed all-mode path maps its ordered vertex list pointwise by the
induced state map. -/
theorem mapAllModePath_vertices {q r : Profile}
    (f : FactorwiseAdditiveInjection q r) {D E : State q}
    (path : MovePath (@AllModeMove q) D E) :
    (mapAllModePath f path).vertices = path.vertices.map (mapState f) := by
  induction path with
  | singleton =>
      simp only [mapAllModePath, MovePath.vertices, List.map_singleton]
  | snoc path _ ih =>
      simp only [mapAllModePath, MovePath.vertices, ih, List.map_append,
        List.map_singleton]

/-- Mapping a mixed all-mode path preserves its exact number of edges. -/
@[simp] theorem mapAllModePath_length {q r : Profile}
    (f : FactorwiseAdditiveInjection q r) {D E : State q}
    (path : MovePath (@AllModeMove q) D E) :
    (mapAllModePath f path).length = path.length := by
  induction path with
  | singleton => simp only [mapAllModePath, MovePath.length]
  | snoc path _ ih => simp only [mapAllModePath, MovePath.length, ih]

/-- Mapping a mixed all-mode path preserves its exact altitude because every
mapped finite-set vertex has the same cardinality as its source. -/
@[simp] theorem mapAllModePath_altitude {q r : Profile}
    (f : FactorwiseAdditiveInjection q r) {D E : State q}
    (path : MovePath (@AllModeMove q) D E) :
    (mapAllModePath f path).altitude = path.altitude := by
  induction path with
  | singleton =>
      simp only [mapAllModePath, MovePath.altitude, mapState_card]
  | snoc path _ ih =>
      simp only [mapAllModePath, MovePath.altitude, ih, mapState_card]

/-- A target state is a mapped mixed-path vertex exactly when it is the image
of an actual source path vertex. -/
theorem mapAllModePath_pathVertex_iff {q r : Profile}
    (f : FactorwiseAdditiveInjection q r) {D E : State q}
    (path : MovePath (@AllModeMove q) D E) (Y : State r) :
    PathVertex (mapAllModePath f path) Y ↔
      ∃ X, PathVertex path X ∧ mapState f X = Y := by
  simp only [PathVertex, mapAllModePath_vertices, List.mem_map]

/-- Image-boundary confinement is preserved when a mixed all-mode path is
mapped by a factorwise additive injection. -/
theorem mapAllModePath_confined {q r : Profile}
    (f : FactorwiseAdditiveInjection q r) {D E B : State q}
    (path : MovePath (@AllModeMove q) D E)
    (hconfined : ∀ X, PathVertex path X → X ⊆ B) :
    ∀ Y, PathVertex (mapAllModePath f path) Y → Y ⊆ mapState f B := by
  intro Y hY
  obtain ⟨X, hX, hXY⟩ := (mapAllModePath_pathVertex_iff f path Y).mp hY
  rw [← hXY]
  exact Finset.image_mono (mapTerm f) (hconfined X hX)

/-- A mapped mixed all-mode path proves evaluation equality between its mapped
target-profile endpoints.  No cross-profile tensor map is introduced. -/
theorem mapAllModePath_preserves_evaluation {q r : Profile}
    (f : FactorwiseAdditiveInjection q r) {D E : State q}
    (path : MovePath (@AllModeMove q) D E) :
    stateEvaluation (mapState f E) = stateEvaluation (mapState f D) := by
  exact allModeMovePath_preserves_evaluation (mapAllModePath f path)

example :
    ∃ f : FactorwiseAdditiveInjection
        (permProfile .bca profile221) (permProfile .bca profile221),
      (mapAllModePath f (allModeForwardPath .bca)).length = 2 := by
  let f : FactorwiseAdditiveInjection
      (permProfile .bca profile221) (permProfile .bca profile221) :=
    { first := AddMonoidHom.id _
      second := AddMonoidHom.id _
      third := AddMonoidHom.id _
      first_injective := fun _ _ hxy => hxy
      second_injective := fun _ _ hxy => hxy
      third_injective := fun _ _ hxy => hxy }
  refine ⟨f, ?_⟩
  rw [mapAllModePath_length]
  exact (allMode_path_metrics .bca).1

end BilinearComplexity.NormalizedBinaryAllModeMoveTransport
