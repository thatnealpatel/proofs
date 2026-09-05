import BilinearComplexity.NormalizedBinaryOrbitClassification

set_option autoImplicit false

/-!
# Context pullback and orbit-action transport for normalized binary circuits

This module makes the checked action selected by `compileClassified` usable by
future contextual row certificates.  A target context is pulled back by a
finite scan of the normalized carrier, so the executable definition uses no
inverse chosen from an existential proof.  Concrete `AllModeMove` paths are
then mapped through exactly the factor maps, mode permutation, and profile cast
stored in the endpoint `ActionWitness`.

The transport preserves the complete vertex list up to pointwise action and
therefore preserves exact path length, every vertex cardinality, and altitude.
It does not construct the thirteen contextual row paths, prove guard coverage,
or assert contextual distance optimality; those remain downstream inputs.
-/

namespace BilinearComplexity.BinaryContextualOrbitTransport

open BinaryCircuit
open NormalizedBinaryCarrier
open NormalizedBinaryMoveTransport
open NormalizedBinaryAllModeMove
open NormalizedBinaryAllModeMoveTransport
open NormalizedBinaryAllModePermutation
open NormalizedBinaryFiniteAction
open NormalizedBinaryOrbitClassification
open NormalizedBinaryCoverage
open NormalizedBinaryRelationEnumeration

/-- Executable finite preimage of a normalized state under an action. -/
def pullbackState {p : Profile} (action : ProfileAction p) (K : State p) : State p := by
  letI : DecidableEq (Carrier p) := inferInstance
  exact Finset.filter (fun t => ProfileAction.actTerm action t ∈ K) Finset.univ

/-- Membership in the executable pullback is tested by forward action. -/
@[simp] theorem mem_pullbackState {p : Profile} (action : ProfileAction p)
    {K : State p} {t : Carrier p} :
    t ∈ pullbackState action K ↔ ProfileAction.actTerm action t ∈ K := by
  simp [pullbackState]

/-- The term action is surjective because it is an injective self-map of a finite carrier. -/
theorem actTerm_surjective {p : Profile} (action : ProfileAction p) :
    Function.Surjective (ProfileAction.actTerm action) := by
  exact Finite.surjective_of_injective (ProfileAction.actTerm_injective action)

/-- Acting on the executable pullback recovers the requested state. -/
@[simp] theorem actState_pullbackState {p : Profile} (action : ProfileAction p)
    (K : State p) : ProfileAction.actState action (pullbackState action K) = K := by
  rw [ProfileAction.actState_eq_image]
  ext t
  constructor
  · intro ht
    obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp ht
    rw [← hst]
    exact (mem_pullbackState action).mp hs
  · intro ht
    obtain ⟨s, hst⟩ := actTerm_surjective action t
    apply Finset.mem_image.mpr
    refine ⟨s, ?_, hst⟩
    apply (mem_pullbackState action).mpr
    rw [hst]
    exact ht

/-- Pulling an acted state back recovers the source state. -/
@[simp] theorem pullbackState_actState {p : Profile} (action : ProfileAction p)
    (D : State p) : pullbackState action (ProfileAction.actState action D) = D := by
  ext t
  rw [mem_pullbackState, ProfileAction.actState_eq_image]
  constructor
  · intro ht
    obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp ht
    have hse : s = t := ProfileAction.actTerm_injective action hst
    simpa only [hse] using hs
  · intro ht
    exact Finset.mem_image.mpr ⟨t, ht, rfl⟩

/-- Executable pullback commutes with finite-state union. -/
@[simp] theorem pullbackState_union {p : Profile} (action : ProfileAction p)
    (K L : State p) :
    pullbackState action (K ∪ L) = pullbackState action K ∪ pullbackState action L := by
  ext t
  simp only [mem_pullbackState, Finset.mem_union]

/-- Executable pullback reflects and preserves finite-state disjointness. -/
theorem pullbackState_disjoint {p : Profile} (action : ProfileAction p)
    (K L : State p) :
    Disjoint (pullbackState action K) (pullbackState action L) ↔
      Disjoint K L := by
  simp only [Finset.disjoint_left]
  constructor
  · intro h t htK htL
    obtain ⟨s, hst⟩ := actTerm_surjective action t
    rw [← hst] at htK htL
    exact h ((mem_pullbackState action).mpr htK)
      ((mem_pullbackState action).mpr htL)
  · intro h t htK htL
    exact h ((mem_pullbackState action).mp htK)
      ((mem_pullbackState action).mp htL)

/-- Executable pullback preserves exact state cardinality. -/
@[simp] theorem pullbackState_card {p : Profile} (action : ProfileAction p)
    (K : State p) : (pullbackState action K).card = K.card := by
  rw [← ProfileAction.actState_card action (pullbackState action K), actState_pullbackState]

/-- State action commutes with finite-state union. -/
@[simp] theorem actState_union {p : Profile} (action : ProfileAction p)
    (D E : State p) : ProfileAction.actState action (D ∪ E) =
      ProfileAction.actState action D ∪ ProfileAction.actState action E := by
  simp only [ProfileAction.actState_eq_image, Finset.image_union]

/-- Reindex one all-mode edge along a profile equality. -/
theorem castAllModeMoveProfile {p q : Profile} (h : p = q) {D E : State p}
    (move : @AllModeMove p D E) :
    @AllModeMove q (cast (congrArg State h) D) (cast (congrArg State h) E) := by
  subst q
  exact move

/-- A checked profile action transports one actual all-mode edge. -/
theorem transportActionAllModeMove {p : Profile} (action : ProfileAction p)
    {D E : State p} (move : @AllModeMove p D E) :
    @AllModeMove p (ProfileAction.actState action D)
      (ProfileAction.actState action E) :=
  castAllModeMoveProfile action.profile_eq
    (permuteAllModeMove action.orientation
      (NormalizedBinaryAllModeMoveTransport.transportAllModeMove
        action.factorwiseInjection move))

/-- Apply a checked profile action to every vertex and edge of an actual path. -/
def actPath {p : Profile} (action : ProfileAction p) :
    {D E : State p} → MovePath (@AllModeMove p) D E →
      MovePath (@AllModeMove p) (ProfileAction.actState action D)
        (ProfileAction.actState action E)
  | _, _, .singleton D => .singleton (ProfileAction.actState action D)
  | _, _, .snoc path move =>
      .snoc (actPath action path) (transportActionAllModeMove action move)
/-- Acting on a path preserves its exact edge count. -/
@[simp] theorem actPath_length {p : Profile} (action : ProfileAction p)
    {D E : State p} (path : MovePath (@AllModeMove p) D E) :
    (actPath action path).length = path.length := by
  induction path with
  | singleton => simp only [actPath, MovePath.length]
  | snoc path move ih => simp only [actPath, MovePath.length, ih]

/-- Acting on a path preserves its exact altitude. -/
@[simp] theorem actPath_altitude {p : Profile} (action : ProfileAction p)
    {D E : State p} (path : MovePath (@AllModeMove p) D E) :
    (actPath action path).altitude = path.altitude := by
  induction path with
  | singleton =>
      simp only [actPath, MovePath.altitude, ProfileAction.actState_card]
  | snoc path move ih =>
      simp only [actPath, MovePath.altitude, ih, ProfileAction.actState_card]

/-- Acting on a path maps its ordered vertex list pointwise by the same state action. -/
theorem actPath_vertices {p : Profile} (action : ProfileAction p)
    {D E : State p} (path : MovePath (@AllModeMove p) D E) :
    (actPath action path).vertices =
      path.vertices.map (ProfileAction.actState action) := by
  induction path with
  | singleton =>
      simp only [actPath, MovePath.vertices, List.map_singleton]
  | snoc path move ih =>
      simp only [actPath, MovePath.vertices, ih, List.map_append,
        List.map_singleton]

/-- Target vertices of an acted path are exactly acted source vertices. -/
theorem actPath_pathVertex_iff {p : Profile} (action : ProfileAction p)
    {D E : State p} (path : MovePath (@AllModeMove p) D E) (Y : State p) :
    PathVertex (actPath action path) Y ↔
      ∃ X, PathVertex path X ∧ ProfileAction.actState action X = Y := by
  simp only [PathVertex, actPath_vertices, List.mem_map]

/-- Every acted path vertex has exactly the cardinality of its source vertex. -/
theorem actPath_vertex_card {p : Profile} (action : ProfileAction p)
    {D E : State p} (path : MovePath (@AllModeMove p) D E) {Y : State p}
    (hY : PathVertex (actPath action path) Y) :
    ∃ X, PathVertex path X ∧ X.card = Y.card := by
  obtain ⟨X, hX, hXY⟩ := (actPath_pathVertex_iff action path Y).mp hY
  refine ⟨X, hX, ?_⟩
  rw [← hXY, ProfileAction.actState_card]

/-- Cast only the endpoint indices of a path, retaining its concrete data. -/
def castPathEndpoints {p : Profile} {D E D' E' : State p}
    (hD : D = D') (hE : E = E')
    (path : MovePath (@AllModeMove p) D E) :
    MovePath (@AllModeMove p) D' E' := by
  subst D'
  subst E'
  exact path

/-- Casting path endpoint indices preserves exact edge count. -/
@[simp] theorem castPathEndpoints_length {p : Profile}
    {D E D' E' : State p} (hD : D = D') (hE : E = E')
    (path : MovePath (@AllModeMove p) D E) :
    (castPathEndpoints hD hE path).length = path.length := by
  subst D'
  subst E'
  rfl

/-- Casting path endpoint indices preserves the concrete vertex list. -/
@[simp] theorem castPathEndpoints_vertices {p : Profile}
    {D E D' E' : State p} (hD : D = D') (hE : E = E')
    (path : MovePath (@AllModeMove p) D E) :
    (castPathEndpoints hD hE path).vertices = path.vertices := by
  subst D'
  subst E'
  rfl

/-- Casting path endpoint indices preserves exact altitude. -/
@[simp] theorem castPathEndpoints_altitude {p : Profile}
    {D E D' E' : State p} (hD : D = D') (hE : E = E')
    (path : MovePath (@AllModeMove p) D E) :
    (castPathEndpoints hD hE path).altitude = path.altitude := by
  subst D'
  subst E'
  rfl

/-- Pull an arbitrary target context back through the exact action used by an endpoint witness. -/
def contextPullback {p : Profile} {source target : RelationEndpoints p}
    (witness : ActionWitness source target) (K : State p) : State p :=
  pullbackState witness.action K

/-- Endpoint-witness context pullback preserves exact cardinality. -/
@[simp] theorem contextPullback_card {p : Profile}
    {source target : RelationEndpoints p} (witness : ActionWitness source target)
    (K : State p) : (contextPullback witness K).card = K.card := by
  exact pullbackState_card witness.action K

/-- A target context disjoint from both target endpoints pulls back to a selected-row context disjoint from both source endpoints. -/
theorem contextPullback_disjoint_sourceUnion {p : Profile}
    {source target : RelationEndpoints p} (witness : ActionWitness source target)
    {K : State p} (hK : Disjoint K (target.left ∪ target.right)) :
    Disjoint (contextPullback witness K) (source.left ∪ source.right) := by
  rw [Finset.disjoint_left]
  intro t htK htSource
  have hImageK : ProfileAction.actTerm witness.action t ∈ K :=
    (mem_pullbackState witness.action).mp htK
  have hImageEndpoint : ProfileAction.actTerm witness.action t ∈
      target.left ∪ target.right := by
    rw [Finset.mem_union] at htSource ⊢
    rcases htSource with htLeft | htRight
    · left
      rw [← witness.left_image, ProfileAction.actState_eq_image]
      exact Finset.mem_image.mpr ⟨t, htLeft, rfl⟩
    · right
      rw [← witness.right_image, ProfileAction.actState_eq_image]
      exact Finset.mem_image.mpr ⟨t, htRight, rfl⟩
  exact (Finset.disjoint_left.mp hK) hImageK hImageEndpoint

/-- Acting on the pulled-back context united with the selected left endpoint gives the requested contextual left endpoint. -/
theorem contextPullback_left_union_image {p : Profile}
    {source target : RelationEndpoints p} (witness : ActionWitness source target)
    (K : State p) :
    ProfileAction.actState witness.action
        (contextPullback witness K ∪ source.left) = K ∪ target.left := by
  rw [actState_union, contextPullback, actState_pullbackState,
    witness.left_image]

/-- Acting on the pulled-back context united with the selected right endpoint gives the requested contextual right endpoint. -/
theorem contextPullback_right_union_image {p : Profile}
    {source target : RelationEndpoints p} (witness : ActionWitness source target)
    (K : State p) :
    ProfileAction.actState witness.action
        (contextPullback witness K ∪ source.right) = K ∪ target.right := by
  rw [actState_union, contextPullback, actState_pullbackState,
    witness.right_image]

/-- The pulled-back contextual left endpoint has exactly the cardinality of the target contextual left endpoint. -/
theorem contextPullback_left_union_card {p : Profile}
    {source target : RelationEndpoints p} (witness : ActionWitness source target)
    (K : State p) :
    (contextPullback witness K ∪ source.left).card =
      (K ∪ target.left).card := by
  rw [← contextPullback_left_union_image witness K,
    ProfileAction.actState_card]

/-- The pulled-back contextual right endpoint has exactly the cardinality of the target contextual right endpoint. -/
theorem contextPullback_right_union_card {p : Profile}
    {source target : RelationEndpoints p} (witness : ActionWitness source target)
    (K : State p) :
    (contextPullback witness K ∪ source.right).card =
      (K ∪ target.right).card := by
  rw [← contextPullback_right_union_image witness K,
    ProfileAction.actState_card]

/-- Transport an actual contextual selected-row path to the arbitrary target context and endpoints. -/
def transportContextPath {p : Profile} {source target : RelationEndpoints p}
    (witness : ActionWitness source target) (K : State p)
    (path : MovePath (@AllModeMove p)
      (contextPullback witness K ∪ source.left)
      (contextPullback witness K ∪ source.right)) :
    MovePath (@AllModeMove p) (K ∪ target.left) (K ∪ target.right) :=
  castPathEndpoints (contextPullback_left_union_image witness K)
    (contextPullback_right_union_image witness K)
    (actPath witness.action path)

/-- Contextual action transport preserves the exact number of edges. -/
@[simp] theorem transportContextPath_length {p : Profile}
    {source target : RelationEndpoints p} (witness : ActionWitness source target)
    (K : State p)
    (path : MovePath (@AllModeMove p)
      (contextPullback witness K ∪ source.left)
      (contextPullback witness K ∪ source.right)) :
    (transportContextPath witness K path).length = path.length := by
  simp only [transportContextPath, castPathEndpoints_length, actPath_length]

/-- Contextual action transport maps every vertex by the selected endpoint action. -/
theorem transportContextPath_vertices {p : Profile}
    {source target : RelationEndpoints p} (witness : ActionWitness source target)
    (K : State p)
    (path : MovePath (@AllModeMove p)
      (contextPullback witness K ∪ source.left)
      (contextPullback witness K ∪ source.right)) :
    (transportContextPath witness K path).vertices =
      path.vertices.map (ProfileAction.actState witness.action) := by
  simp only [transportContextPath, castPathEndpoints_vertices, actPath_vertices]

/-- Contextual action transport preserves exact altitude. -/
@[simp] theorem transportContextPath_altitude {p : Profile}
    {source target : RelationEndpoints p} (witness : ActionWitness source target)
    (K : State p)
    (path : MovePath (@AllModeMove p)
      (contextPullback witness K ∪ source.left)
      (contextPullback witness K ∪ source.right)) :
    (transportContextPath witness K path).altitude = path.altitude := by
  simp only [transportContextPath, castPathEndpoints_altitude, actPath_altitude]

/-- Transported contextual vertices are exactly action images of source vertices. -/
theorem transportContextPath_pathVertex_iff {p : Profile}
    {source target : RelationEndpoints p} (witness : ActionWitness source target)
    (K : State p)
    (path : MovePath (@AllModeMove p)
      (contextPullback witness K ∪ source.left)
      (contextPullback witness K ∪ source.right)) (Y : State p) :
    PathVertex (transportContextPath witness K path) Y ↔
      ∃ X, PathVertex path X ∧
        ProfileAction.actState witness.action X = Y := by
  simp only [PathVertex, transportContextPath_vertices, List.mem_map]

/-- Every transported contextual vertex has exactly its source vertex's cardinality. -/
theorem transportContextPath_vertex_card {p : Profile}
    {source target : RelationEndpoints p} (witness : ActionWitness source target)
    (K : State p)
    (path : MovePath (@AllModeMove p)
      (contextPullback witness K ∪ source.left)
      (contextPullback witness K ∪ source.right)) {Y : State p}
    (hY : PathVertex (transportContextPath witness K path) Y) :
    ∃ X, PathVertex path X ∧ X.card = Y.card := by
  obtain ⟨X, hX, hXY⟩ :=
    (transportContextPath_pathVertex_iff witness K path Y).mp hY
  refine ⟨X, hX, ?_⟩
  rw [← hXY, ProfileAction.actState_card]

/-- The exact selected-row action witness retained by a classified compilation. -/
def selectedActionWitness {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target) :
    ActionWitness compiled.label.selectedEndpoints
      compiled.compilation.oriented.1 :=
  compiled.compilation.witness

/-- Pull a context on the oriented target relation back to the selected row chosen by the classified compiler. -/
def selectedContextPullback {p : Profile}
    {target : ExactRelation p} (compiled : ClassifiedCompilation target)
    (K : State compiled.compilation.choice.family.profile) :
    State compiled.compilation.choice.family.profile :=
  contextPullback (selectedActionWitness compiled) K

/-- Compiler-selected context pullback preserves exact cardinality. -/
@[simp] theorem selectedContextPullback_card
    {p : Profile} {target : ExactRelation p}
    (compiled : ClassifiedCompilation target)
    (K : State compiled.compilation.choice.family.profile) :
    (selectedContextPullback compiled K).card = K.card := by
  exact contextPullback_card (selectedActionWitness compiled) K

/-- Disjointness from the oriented target endpoints reflects to disjointness from the compiler-selected row endpoints. -/
theorem selectedContextPullback_disjoint
    {p : Profile} {target : ExactRelation p}
    (compiled : ClassifiedCompilation target)
    {K : State compiled.compilation.choice.family.profile}
    (hK : Disjoint K
      (compiled.compilation.oriented.1.left ∪
        compiled.compilation.oriented.1.right)) :
    Disjoint (selectedContextPullback compiled K)
      (compiled.label.selectedEndpoints.left ∪
        compiled.label.selectedEndpoints.right) := by
  exact contextPullback_disjoint_sourceUnion
    (selectedActionWitness compiled) hK

/-- The selected action maps the pulled-back context and selected left endpoint to the requested oriented contextual endpoint. -/
theorem selectedContextPullback_left_union_image
    {p : Profile} {target : ExactRelation p}
    (compiled : ClassifiedCompilation target)
    (K : State compiled.compilation.choice.family.profile) :
    ProfileAction.actState (selectedActionWitness compiled).action
      (selectedContextPullback compiled K ∪
        compiled.label.selectedEndpoints.left) =
      K ∪ compiled.compilation.oriented.1.left := by
  exact contextPullback_left_union_image (selectedActionWitness compiled) K

/-- The selected action maps the pulled-back context and selected right endpoint to the requested oriented contextual endpoint. -/
theorem selectedContextPullback_right_union_image
    {p : Profile} {target : ExactRelation p}
    (compiled : ClassifiedCompilation target)
    (K : State compiled.compilation.choice.family.profile) :
    ProfileAction.actState (selectedActionWitness compiled).action
      (selectedContextPullback compiled K ∪
        compiled.label.selectedEndpoints.right) =
      K ∪ compiled.compilation.oriented.1.right := by
  exact contextPullback_right_union_image (selectedActionWitness compiled) K

/-- The compiler-selected pulled-back left endpoint union preserves exact cardinality. -/
theorem selectedContextPullback_left_union_card
    {p : Profile} {target : ExactRelation p}
    (compiled : ClassifiedCompilation target)
    (K : State compiled.compilation.choice.family.profile) :
    (selectedContextPullback compiled K ∪
      compiled.label.selectedEndpoints.left).card =
      (K ∪ compiled.compilation.oriented.1.left).card := by
  exact contextPullback_left_union_card (selectedActionWitness compiled) K

/-- The compiler-selected pulled-back right endpoint union preserves exact cardinality. -/
theorem selectedContextPullback_right_union_card
    {p : Profile} {target : ExactRelation p}
    (compiled : ClassifiedCompilation target)
    (K : State compiled.compilation.choice.family.profile) :
    (selectedContextPullback compiled K ∪
      compiled.label.selectedEndpoints.right).card =
      (K ∪ compiled.compilation.oriented.1.right).card := by
  exact contextPullback_right_union_card (selectedActionWitness compiled) K

/-- Transport an actual contextual path supplied for the compiler-selected row to the oriented target relation. -/
def transportSelectedContextPath
    {p : Profile} {target : ExactRelation p}
    (compiled : ClassifiedCompilation target)
    (K : State compiled.compilation.choice.family.profile)
    (path : MovePath
      (@AllModeMove compiled.compilation.choice.family.profile)
      (selectedContextPullback compiled K ∪
        compiled.label.selectedEndpoints.left)
      (selectedContextPullback compiled K ∪
        compiled.label.selectedEndpoints.right)) :
    MovePath (@AllModeMove compiled.compilation.choice.family.profile)
      (K ∪ compiled.compilation.oriented.1.left)
      (K ∪ compiled.compilation.oriented.1.right) :=
  transportContextPath (selectedActionWitness compiled) K path

/-- Compiler-selected contextual transport preserves exact edge count. -/
@[simp] theorem transportSelectedContextPath_length
    {p : Profile} {target : ExactRelation p}
    (compiled : ClassifiedCompilation target)
    (K : State compiled.compilation.choice.family.profile)
    (path : MovePath
      (@AllModeMove compiled.compilation.choice.family.profile)
      (selectedContextPullback compiled K ∪
        compiled.label.selectedEndpoints.left)
      (selectedContextPullback compiled K ∪
        compiled.label.selectedEndpoints.right)) :
    (transportSelectedContextPath compiled K path).length = path.length := by
  exact transportContextPath_length (selectedActionWitness compiled) K path

/-- Compiler-selected contextual transport preserves exact altitude. -/
@[simp] theorem transportSelectedContextPath_altitude
    {p : Profile} {target : ExactRelation p}
    (compiled : ClassifiedCompilation target)
    (K : State compiled.compilation.choice.family.profile)
    (path : MovePath
      (@AllModeMove compiled.compilation.choice.family.profile)
      (selectedContextPullback compiled K ∪
        compiled.label.selectedEndpoints.left)
      (selectedContextPullback compiled K ∪
        compiled.label.selectedEndpoints.right)) :
    (transportSelectedContextPath compiled K path).altitude = path.altitude := by
  exact transportContextPath_altitude (selectedActionWitness compiled) K path

/-- Selected-row contextual transport maps its concrete vertex list pointwise by the compiler's action. -/
theorem transportSelectedContextPath_vertices
    {p : Profile} {target : ExactRelation p}
    (compiled : ClassifiedCompilation target)
    (K : State compiled.compilation.choice.family.profile)
    (path : MovePath
      (@AllModeMove compiled.compilation.choice.family.profile)
      (selectedContextPullback compiled K ∪
        compiled.label.selectedEndpoints.left)
      (selectedContextPullback compiled K ∪
        compiled.label.selectedEndpoints.right)) :
    (transportSelectedContextPath compiled K path).vertices =
      path.vertices.map
        (ProfileAction.actState (selectedActionWitness compiled).action) := by
  exact transportContextPath_vertices (selectedActionWitness compiled) K path

/-- Every selected-row transported vertex has exactly the cardinality of a concrete source-path vertex. -/
theorem transportSelectedContextPath_vertex_card
    {p : Profile} {target : ExactRelation p}
    (compiled : ClassifiedCompilation target)
    (K : State compiled.compilation.choice.family.profile)
    (path : MovePath
      (@AllModeMove compiled.compilation.choice.family.profile)
      (selectedContextPullback compiled K ∪
        compiled.label.selectedEndpoints.left)
      (selectedContextPullback compiled K ∪
        compiled.label.selectedEndpoints.right))
    {Y : State compiled.compilation.choice.family.profile}
    (hY : PathVertex (transportSelectedContextPath compiled K path) Y) :
    ∃ X, PathVertex path X ∧ X.card = Y.card := by
  exact transportContextPath_vertex_card
    (selectedActionWitness compiled) K path hY

end BilinearComplexity.BinaryContextualOrbitTransport

#print axioms BilinearComplexity.BinaryContextualOrbitTransport.actState_pullbackState
#print axioms BilinearComplexity.BinaryContextualOrbitTransport.transportSelectedContextPath_vertex_card
