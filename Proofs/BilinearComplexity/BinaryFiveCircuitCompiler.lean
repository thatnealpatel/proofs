import BilinearComplexity.BinaryAmbientNormalization
import BilinearComplexity.BinaryAmbientMoveTransport
import BilinearComplexity.BinaryAmbientOrbitCoordinates

set_option autoImplicit false

/-!
# Executable ambient binary five-circuit compiler

This module transports the closed normalized five-circuit compiler through an
explicit exact-span coordinate presentation.  The executable boundary takes
all coordinate data as input: basis selection remains confined to separate
proof-side existence theorems.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.BinaryFiveCircuitCompiler

open BinaryCircuit
open BinaryAmbientCarrier
open BinaryAmbientMoves
open BinaryAmbientMoveTransport
open BinaryAmbientNormalization
open BinaryAmbientTensorCoordinates
open NormalizedBinaryCarrier
open NormalizedBinaryFiniteAction
open NormalizedBinaryFiveCircuitCertificate
open NormalizedBinaryOrbitClassification
open NormalizedBinaryRelationEnumeration

universe u v w

variable {U : Type u} {V : Type v} {W : Type w}
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [Module F2 U] [Module F2 V] [Module F2 W]
variable [DecidableEq U] [DecidableEq V] [DecidableEq W]

/-- Embed supplied exact-span coordinates into the three ambient factors. -/
def exactSpanCoordinateEmbedding {A B : State U V W}
    (P : ExactSpanPresentation A B) :
    CoordinateEmbedding P.profile U V W where
  first := (firstSpan (A ∪ B)).subtype.comp P.firstCoordinates.toLinearMap
  second := (secondSpan (A ∪ B)).subtype.comp P.secondCoordinates.toLinearMap
  third := (thirdSpan (A ∪ B)).subtype.comp P.thirdCoordinates.toLinearMap
  first_injective := by
    intro x y hxy
    apply P.firstCoordinates.injective
    apply Subtype.ext
    exact hxy
  second_injective := by
    intro x y hxy
    apply P.secondCoordinates.injective
    apply Subtype.ext
    exact hxy
  third_injective := by
    intro x y hxy
    apply P.thirdCoordinates.injective
    apply Subtype.ext
    exact hxy

example {A B : State U V W} (P : ExactSpanPresentation A B) :
    (exactSpanCoordinateEmbedding P).first =
      (firstSpan (A ∪ B)).subtype.comp P.firstCoordinates.toLinearMap := rfl

private theorem mapTerm_exactSpanCoordinateEmbedding
    {A B : State U V W} (P : ExactSpanPresentation A B)
    (t : NormalizedBinaryCarrier.Carrier P.profile) :
    BinaryAmbientMoveTransport.mapTerm (exactSpanCoordinateEmbedding P) t =
      includeTerm (A ∪ B)
        (denormalizeTerm P.firstCoordinates P.secondCoordinates
          P.thirdCoordinates t) := by
  rfl

/-- Mapping a normalized state through the exact-span embedding agrees with
denormalization followed by inclusion into the original ambient factors. -/
theorem mapState_exactSpanCoordinateEmbedding
    {A B : State U V W} (P : ExactSpanPresentation A B) :
    ∀ D : NormalizedBinaryCarrier.State P.profile,
      BinaryAmbientMoveTransport.mapState (exactSpanCoordinateEmbedding P) D =
        includeState (A ∪ B)
          (denormalizeState P.firstCoordinates P.secondCoordinates
            P.thirdCoordinates D) := by
  rcases P with ⟨profile, eU, eV, eW⟩
  rcases profile with ⟨a, b, c⟩
  intro D
  dsimp only [ExactSpanPresentation.profile, ExactSpanPresentation.firstCoordinates,
    ExactSpanPresentation.secondCoordinates, ExactSpanPresentation.thirdCoordinates,
    Profile.first, Profile.second, Profile.third] at D ⊢
  change NormalizedBinaryCarrier.State (coordinateProfile a b c) at D
  unfold BinaryAmbientMoveTransport.mapState includeState denormalizeState
  rw [Finset.map_map, Finset.map_eq_image]
  apply Finset.image_congr
  intro t _ht
  exact mapTerm_exactSpanCoordinateEmbedding
    ⟨⟨a, b, c⟩, eU, eV, eW⟩ t

/-- The exact-span embedding maps the normalized left endpoint back to the
original ambient left endpoint. -/
theorem mapState_normalizedLeft {A B : State U V W}
    (P : ExactSpanPresentation A B) :
    BinaryAmbientMoveTransport.mapState (exactSpanCoordinateEmbedding P)
      (normalizedLeft P) = A := by
  rw [mapState_exactSpanCoordinateEmbedding]
  exact normalizedLeft_reconstruction P

/-- The exact-span embedding maps the normalized right endpoint back to the
original ambient right endpoint. -/
theorem mapState_normalizedRight {A B : State U V W}
    (P : ExactSpanPresentation A B) :
    BinaryAmbientMoveTransport.mapState (exactSpanCoordinateEmbedding P)
      (normalizedRight P) = B := by
  rw [mapState_exactSpanCoordinateEmbedding]
  exact normalizedRight_reconstruction P

/-- Reindex both endpoints of a concrete path along supplied equalities. -/
def castMovePathEndpoints {α : Type*}
    {R : BinaryCircuit.Scheme α → BinaryCircuit.Scheme α → Prop}
    {D E D' E' : BinaryCircuit.Scheme α} (path : MovePath R D E)
    (hD : D = D') (hE : E = E') : MovePath R D' E' := by
  subst D'
  subst E'
  exact path

example {α : Type*} {R : BinaryCircuit.Scheme α → BinaryCircuit.Scheme α → Prop}
    {D E : BinaryCircuit.Scheme α} (path : MovePath R D E) :
    castMovePathEndpoints path rfl rfl = path := rfl

/-- Endpoint reindexing preserves exact path length. -/
@[simp] theorem castMovePathEndpoints_length {α : Type*}
    {R : BinaryCircuit.Scheme α → BinaryCircuit.Scheme α → Prop}
    {D E D' E' : BinaryCircuit.Scheme α} (path : MovePath R D E)
    (hD : D = D') (hE : E = E') :
    (castMovePathEndpoints path hD hE).length = path.length := by
  subst D'
  subst E'
  rfl

/-- Endpoint reindexing preserves exact path altitude. -/
@[simp] theorem castMovePathEndpoints_altitude {α : Type*}
    {R : BinaryCircuit.Scheme α → BinaryCircuit.Scheme α → Prop}
    {D E D' E' : BinaryCircuit.Scheme α} (path : MovePath R D E)
    (hD : D = D') (hE : E = E') :
    (castMovePathEndpoints path hD hE).altitude = path.altitude := by
  subst D'
  subst E'
  rfl

/-- Endpoint reindexing preserves the exact ordered vertex list. -/
@[simp] theorem castMovePathEndpoints_vertices {α : Type*}
    {R : BinaryCircuit.Scheme α → BinaryCircuit.Scheme α → Prop}
    {D E D' E' : BinaryCircuit.Scheme α} (path : MovePath R D E)
    (hD : D = D') (hE : E = E') :
    (castMovePathEndpoints path hD hE).vertices = path.vertices := by
  subst D'
  subst E'
  rfl

/-- An ambient state is confined by `K` when each of its three projected
factor spans is contained in the corresponding factor span of `K`. -/
def AmbientFactorSpanConfined (K X : State U V W) : Prop :=
  firstSpan X ≤ firstSpan K ∧
    secondSpan X ≤ secondSpan K ∧
    thirdSpan X ≤ thirdSpan K

example (D : State U V W) : AmbientFactorSpanConfined D D :=
  ⟨le_rfl, le_rfl, le_rfl⟩

/-- An ambient path is factor-span confined when every actual path vertex is
confined by the designated ambient state. -/
def AmbientPathFactorSpanConfined
    {R : State U V W → State U V W → Prop} {D E : State U V W}
    (path : MovePath R D E) (K : State U V W) : Prop :=
  ∀ X, PathVertex path X → AmbientFactorSpanConfined K X

example (D : State U V W) :
    AmbientPathFactorSpanConfined
      (.singleton D : MovePath (BinaryAmbientMoves.AllModeMove
        (U := U) (V := V) (W := W)) D D) D := by
  intro X hX
  have hXD : X = D := by
    simpa only [PathVertex, MovePath.vertices, List.mem_singleton] using hX
  rw [hXD]
  exact ⟨le_rfl, le_rfl, le_rfl⟩

/-- Every coordinate state mapped through an exact-span embedding is confined
to the factor spans generated by the original two ambient endpoints. -/
theorem mapState_exactSpanCoordinateEmbedding_confined
    {A B : State U V W} (P : ExactSpanPresentation A B)
    (D : NormalizedBinaryCarrier.State P.profile) :
    AmbientFactorSpanConfined (A ∪ B)
      (BinaryAmbientMoveTransport.mapState
        (exactSpanCoordinateEmbedding P) D) := by
  constructor
  · apply Submodule.span_le.mpr
    rintro x ⟨t, ht, rfl⟩
    obtain ⟨s, _hs, rfl⟩ := Finset.mem_image.mp ht
    exact (P.firstCoordinates s.1.1).property
  · constructor
    · apply Submodule.span_le.mpr
      rintro x ⟨t, ht, rfl⟩
      obtain ⟨s, _hs, rfl⟩ := Finset.mem_image.mp ht
      exact (P.secondCoordinates s.2.1.1).property
    · apply Submodule.span_le.mpr
      rintro x ⟨t, ht, rfl⟩
      obtain ⟨s, _hs, rfl⟩ := Finset.mem_image.mp ht
      exact (P.thirdCoordinates s.2.2.1).property

/-- Transporting any normalized path through an exact-span embedding confines
all resulting ambient vertices to the endpoint-generated factor spans. -/
theorem mapPath_exactSpanCoordinateEmbedding_confined
    {A B : State U V W} (P : ExactSpanPresentation A B)
    {D E : NormalizedBinaryCarrier.State P.profile}
    (path : MovePath (@NormalizedBinaryAllModeMove.AllModeMove P.profile) D E) :
    AmbientPathFactorSpanConfined
      (BinaryAmbientMoveTransport.mapPath (exactSpanCoordinateEmbedding P) path)
      (A ∪ B) := by
  intro Y hY
  obtain ⟨X, _hX, hXY⟩ :=
    (BinaryAmbientMoveTransport.mapPath_pathVertex_iff
      (exactSpanCoordinateEmbedding P) path Y).mp hY
  rw [← hXY]
  exact mapState_exactSpanCoordinateEmbedding_confined P X

/-- The minimal stored result of ambient compilation: exactly the classified
compilation of the normalized relation determined by the supplied presentation
and the four ambient hypotheses. -/
structure BinaryFiveCircuitCompilation
    {A B : State U V W} (P : ExactSpanPresentation A B)
    (hA : A.card = 2) (hB : B.card = 3) (hDisjoint : Disjoint A B)
    (hEvaluation : stateEvaluation A = stateEvaluation B) : Type where
  /-- The unchanged normalized classified compilation, including its selected
action witness and both concrete normalized certificate paths. -/
  classified : ClassifiedCompilation
    (normalizedExactRelation P hA hB hDisjoint hEvaluation)

/-- Run the closed normalized compiler on exactly the relation obtained from
the supplied ambient endpoints and exact-span coordinates. -/
def compileBinaryFiveCircuit
    {A B : State U V W} (P : ExactSpanPresentation A B)
    (hA : A.card = 2) (hB : B.card = 3) (hDisjoint : Disjoint A B)
    (hEvaluation : stateEvaluation A = stateEvaluation B) :
    BinaryFiveCircuitCompilation P hA hB hDisjoint hEvaluation :=
  ⟨compileClassified (normalizedExactRelation P hA hB hDisjoint hEvaluation)⟩

example {A B : State U V W} (P : ExactSpanPresentation A B)
    (hA : A.card = 2) (hB : B.card = 3) (hDisjoint : Disjoint A B)
    (hEvaluation : stateEvaluation A = stateEvaluation B) :
    (compileBinaryFiveCircuit P hA hB hDisjoint hEvaluation).classified =
      compileClassified (normalizedExactRelation P hA hB hDisjoint hEvaluation) := rfl

/-- The observable orbit label of an ambient compilation. -/
def BinaryFiveCircuitCompilation.label
    {A B : State U V W} {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hDisjoint : Disjoint A B}
    {hEvaluation : stateEvaluation A = stateEvaluation B}
    (result : BinaryFiveCircuitCompilation P hA hB hDisjoint hEvaluation) :
    OrbitLabel :=
  result.classified.label

example {A B : State U V W} (P : ExactSpanPresentation A B)
    (hA : A.card = 2) (hB : B.card = 3) (hDisjoint : Disjoint A B)
    (hEvaluation : stateEvaluation A = stateEvaluation B) :
    (compileBinaryFiveCircuit P hA hB hDisjoint hEvaluation).label =
      (compileClassified
        (normalizedExactRelation P hA hB hDisjoint hEvaluation)).label := rfl

/-- The selected normalized certificate, exposed at the normalized endpoint
type fixed by the presentation. -/
def BinaryFiveCircuitCompilation.certificate
    {A B : State U V W} {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hDisjoint : Disjoint A B}
    {hEvaluation : stateEvaluation A = stateEvaluation B}
    (result : BinaryFiveCircuitCompilation P hA hB hDisjoint hEvaluation) :
    FiveCircuitCertificate P.profile (normalizedLeft P) (normalizedRight P) :=
  result.classified.certificate

example {A B : State U V W} (P : ExactSpanPresentation A B)
    (hA : A.card = 2) (hB : B.card = 3) (hDisjoint : Disjoint A B)
    (hEvaluation : stateEvaluation A = stateEvaluation B) :
    (compileBinaryFiveCircuit P hA hB hDisjoint hEvaluation).certificate =
      (compileClassified
        (normalizedExactRelation P hA hB hDisjoint hEvaluation)).certificate := rfl

/-- The forward ambient path obtained by mapping the actual selected normalized
certificate path and reindexing only its two endpoints. -/
def BinaryFiveCircuitCompilation.forward
    {A B : State U V W} {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hDisjoint : Disjoint A B}
    {hEvaluation : stateEvaluation A = stateEvaluation B}
    (result : BinaryFiveCircuitCompilation P hA hB hDisjoint hEvaluation) :
    MovePath (BinaryAmbientMoves.AllModeMove (U := U) (V := V) (W := W)) A B :=
  castMovePathEndpoints
    (BinaryAmbientMoveTransport.mapPath (exactSpanCoordinateEmbedding P)
      result.certificate.forward)
    (mapState_normalizedLeft P) (mapState_normalizedRight P)

/-- The reverse ambient path obtained from the same selected certificate. -/
def BinaryFiveCircuitCompilation.reverse
    {A B : State U V W} {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hDisjoint : Disjoint A B}
    {hEvaluation : stateEvaluation A = stateEvaluation B}
    (result : BinaryFiveCircuitCompilation P hA hB hDisjoint hEvaluation) :
    MovePath (BinaryAmbientMoves.AllModeMove (U := U) (V := V) (W := W)) B A :=
  castMovePathEndpoints
    (BinaryAmbientMoveTransport.mapPath (exactSpanCoordinateEmbedding P)
      result.certificate.reverse)
    (mapState_normalizedRight P) (mapState_normalizedLeft P)

/-- The ambient forward path retains the selected certificate's exact length. -/
@[simp] theorem BinaryFiveCircuitCompilation.forward_length
    {A B : State U V W} {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hDisjoint : Disjoint A B}
    {hEvaluation : stateEvaluation A = stateEvaluation B}
    (result : BinaryFiveCircuitCompilation P hA hB hDisjoint hEvaluation) :
    result.forward.length = result.certificate.forward.length := by
  unfold BinaryFiveCircuitCompilation.forward
  rw [castMovePathEndpoints_length,
    BinaryAmbientMoveTransport.mapPath_length]

/-- The ambient reverse path retains the selected certificate's exact length. -/
@[simp] theorem BinaryFiveCircuitCompilation.reverse_length
    {A B : State U V W} {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hDisjoint : Disjoint A B}
    {hEvaluation : stateEvaluation A = stateEvaluation B}
    (result : BinaryFiveCircuitCompilation P hA hB hDisjoint hEvaluation) :
    result.reverse.length = result.certificate.reverse.length := by
  unfold BinaryFiveCircuitCompilation.reverse
  rw [castMovePathEndpoints_length,
    BinaryAmbientMoveTransport.mapPath_length]

/-- The ambient forward path retains the selected certificate's exact altitude. -/
@[simp] theorem BinaryFiveCircuitCompilation.forward_altitude
    {A B : State U V W} {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hDisjoint : Disjoint A B}
    {hEvaluation : stateEvaluation A = stateEvaluation B}
    (result : BinaryFiveCircuitCompilation P hA hB hDisjoint hEvaluation) :
    result.forward.altitude = result.certificate.forward.altitude := by
  unfold BinaryFiveCircuitCompilation.forward
  rw [castMovePathEndpoints_altitude,
    BinaryAmbientMoveTransport.mapPath_altitude]

/-- The ambient reverse path retains the selected certificate's exact altitude. -/
@[simp] theorem BinaryFiveCircuitCompilation.reverse_altitude
    {A B : State U V W} {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hDisjoint : Disjoint A B}
    {hEvaluation : stateEvaluation A = stateEvaluation B}
    (result : BinaryFiveCircuitCompilation P hA hB hDisjoint hEvaluation) :
    result.reverse.altitude = result.certificate.reverse.altitude := by
  unfold BinaryFiveCircuitCompilation.reverse
  rw [castMovePathEndpoints_altitude,
    BinaryAmbientMoveTransport.mapPath_altitude]

/-- The compiled ambient forward path uses at most three moves. -/
theorem BinaryFiveCircuitCompilation.forward_length_le
    {A B : State U V W} {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hDisjoint : Disjoint A B}
    {hEvaluation : stateEvaluation A = stateEvaluation B}
    (result : BinaryFiveCircuitCompilation P hA hB hDisjoint hEvaluation) :
    result.forward.length ≤ 3 := by
  rw [result.forward_length]
  exact result.certificate.forward_length_le

/-- The compiled ambient reverse path uses at most three moves. -/
theorem BinaryFiveCircuitCompilation.reverse_length_le
    {A B : State U V W} {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hDisjoint : Disjoint A B}
    {hEvaluation : stateEvaluation A = stateEvaluation B}
    (result : BinaryFiveCircuitCompilation P hA hB hDisjoint hEvaluation) :
    result.reverse.length ≤ 3 := by
  rw [result.reverse_length]
  exact result.certificate.reverse_length_le

/-- Every compiled ambient forward vertex has at most four terms. -/
theorem BinaryFiveCircuitCompilation.forward_altitude_le
    {A B : State U V W} {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hDisjoint : Disjoint A B}
    {hEvaluation : stateEvaluation A = stateEvaluation B}
    (result : BinaryFiveCircuitCompilation P hA hB hDisjoint hEvaluation) :
    result.forward.altitude ≤ 4 := by
  rw [result.forward_altitude]
  exact result.certificate.forward_altitude_le

/-- Every compiled ambient reverse vertex has at most four terms. -/
theorem BinaryFiveCircuitCompilation.reverse_altitude_le
    {A B : State U V W} {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hDisjoint : Disjoint A B}
    {hEvaluation : stateEvaluation A = stateEvaluation B}
    (result : BinaryFiveCircuitCompilation P hA hB hDisjoint hEvaluation) :
    result.reverse.altitude ≤ 4 := by
  rw [result.reverse_altitude]
  exact result.certificate.reverse_altitude_le

/-- Every vertex of the actual compiled ambient forward path is confined to
the exact factor spans generated by the two endpoints. -/
theorem BinaryFiveCircuitCompilation.forward_confined
    {A B : State U V W} {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hDisjoint : Disjoint A B}
    {hEvaluation : stateEvaluation A = stateEvaluation B}
    (result : BinaryFiveCircuitCompilation P hA hB hDisjoint hEvaluation) :
    AmbientPathFactorSpanConfined result.forward (A ∪ B) := by
  intro X hX
  apply mapPath_exactSpanCoordinateEmbedding_confined P
    result.certificate.forward X
  rw [PathVertex] at hX ⊢
  unfold BinaryFiveCircuitCompilation.forward at hX
  rw [castMovePathEndpoints_vertices] at hX
  exact hX

/-- Every vertex of the actual compiled ambient reverse path is confined to
the exact factor spans generated by the two endpoints. -/
theorem BinaryFiveCircuitCompilation.reverse_confined
    {A B : State U V W} {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hDisjoint : Disjoint A B}
    {hEvaluation : stateEvaluation A = stateEvaluation B}
    (result : BinaryFiveCircuitCompilation P hA hB hDisjoint hEvaluation) :
    AmbientPathFactorSpanConfined result.reverse (A ∪ B) := by
  intro X hX
  apply mapPath_exactSpanCoordinateEmbedding_confined P
    result.certificate.reverse X
  rw [PathVertex] at hX ⊢
  unfold BinaryFiveCircuitCompilation.reverse at hX
  rw [castMovePathEndpoints_vertices] at hX
  exact hX

/-- Coordinate-free semantic membership of an ordered ambient endpoint pair in
one of the thirteen normalized orbits.  This definition quantifies over
supplied exact-span presentations and is independent of compiler tables. -/
def AmbientInOrbit (label : OrbitLabel) (A B : State U V W) : Prop :=
  ∃ P : ExactSpanPresentation A B, InOrbit label (normalizedEndpoints P)

example (label : OrbitLabel) (A B : State U V W) :
    AmbientInOrbit label A B ↔
      ∃ P : ExactSpanPresentation A B, InOrbit label (normalizedEndpoints P) :=
  Iff.rfl

/-- The observable label returned by ambient compilation semantically contains
the supplied ambient endpoint pair. -/
theorem BinaryFiveCircuitCompilation.ambient_membership
    {A B : State U V W} {P : ExactSpanPresentation A B}
    {hA : A.card = 2} {hB : B.card = 3} {hDisjoint : Disjoint A B}
    {hEvaluation : stateEvaluation A = stateEvaluation B}
    (result : BinaryFiveCircuitCompilation P hA hB hDisjoint hEvaluation) :
    AmbientInOrbit result.label A B := by
  refine ⟨P, ?_⟩
  exact result.classified.membership

/-- Semantic orbit labels of fixed ambient endpoints are unique across every
choice of exact-span presentation. -/
theorem ambientInOrbit_label_unique {A B : State U V W}
    {first second : OrbitLabel}
    (hfirst : AmbientInOrbit first A B)
    (hsecond : AmbientInOrbit second A B) : first = second := by
  rcases hfirst with ⟨P, hP⟩
  rcases hsecond with ⟨Q, hQ⟩
  letI := restrictedCarrierDecidableEq (A ∪ B)
  exact BinaryAmbientOrbitCoordinates.inOrbit_label_eq_of_normalizeState
    (U := firstSpan (A ∪ B)) (V := secondSpan (A ∪ B))
    (W := thirdSpan (A ∪ B))
    P.firstCoordinates P.secondCoordinates P.thirdCoordinates
    Q.firstCoordinates Q.secondCoordinates Q.thirdCoordinates
    (restrictState (A ∪ B) A Finset.subset_union_left)
    (restrictState (A ∪ B) B Finset.subset_union_right)
    first second hP hQ

/-- In particular, compilation with any two exact-span presentations returns
the same observable ambient orbit label. -/
theorem compileBinaryFiveCircuit_label_eq
    {A B : State U V W} (P Q : ExactSpanPresentation A B)
    (hA : A.card = 2) (hB : B.card = 3) (hDisjoint : Disjoint A B)
    (hEvaluation : stateEvaluation A = stateEvaluation B) :
    (compileBinaryFiveCircuit P hA hB hDisjoint hEvaluation).label =
      (compileBinaryFiveCircuit Q hA hB hDisjoint hEvaluation).label := by
  apply ambientInOrbit_label_unique (U := U) (V := V) (W := W)
  · exact (compileBinaryFiveCircuit P hA hB hDisjoint hEvaluation).ambient_membership
  · exact (compileBinaryFiveCircuit Q hA hB hDisjoint hEvaluation).ambient_membership

/-- The presentation-free conclusion delivered by ambient five-circuit
compilation: a unique semantic label and concrete bounded, exact-span-confined
paths in both directions. -/
def AmbientFiveCircuitConclusion (A B : State U V W) : Prop :=
  ∃ label : OrbitLabel,
    AmbientInOrbit label A B ∧
    ∃ forward : MovePath
        (BinaryAmbientMoves.AllModeMove (U := U) (V := V) (W := W)) A B,
      ∃ reverse : MovePath
          (BinaryAmbientMoves.AllModeMove (U := U) (V := V) (W := W)) B A,
        forward.length ≤ 3 ∧ reverse.length ≤ 3 ∧
        forward.altitude ≤ 4 ∧ reverse.altitude ≤ 4 ∧
        AmbientPathFactorSpanConfined forward (A ∪ B) ∧
        AmbientPathFactorSpanConfined reverse (A ∪ B)

example (A B : State U V W) : AmbientFiveCircuitConclusion A B ↔
    ∃ label : OrbitLabel,
      AmbientInOrbit label A B ∧
      ∃ forward : MovePath
          (BinaryAmbientMoves.AllModeMove (U := U) (V := V) (W := W)) A B,
        ∃ reverse : MovePath
            (BinaryAmbientMoves.AllModeMove (U := U) (V := V) (W := W)) B A,
          forward.length ≤ 3 ∧ reverse.length ≤ 3 ∧
          forward.altitude ≤ 4 ∧ reverse.altitude ≤ 4 ∧
          AmbientPathFactorSpanConfined forward (A ∪ B) ∧
          AmbientPathFactorSpanConfined reverse (A ∪ B) := Iff.rfl

/-- Proof-side universal finite-dimensional ambient five-circuit theorem.
Coordinates are obtained only under this existential theorem; the executable
compiler itself continues to require an explicit presentation. -/
theorem exists_ambientFiveCircuitConclusion
    [FiniteDimensional F2 U] [FiniteDimensional F2 V]
    [FiniteDimensional F2 W]
    {A B : State U V W}
    (hA : A.card = 2) (hB : B.card = 3) (hDisjoint : Disjoint A B)
    (hEvaluation : stateEvaluation A = stateEvaluation B) :
    AmbientFiveCircuitConclusion A B := by
  obtain ⟨P⟩ := exists_exactSpanPresentation A B
  let result := compileBinaryFiveCircuit P hA hB hDisjoint hEvaluation
  refine ⟨result.label, ?_⟩
  constructor
  · exact result.ambient_membership
  refine ⟨result.forward, ?_⟩
  refine ⟨result.reverse, ?_⟩
  constructor
  · exact result.forward_length_le
  constructor
  · exact result.reverse_length_le
  constructor
  · exact result.forward_altitude_le
  constructor
  · exact result.reverse_altitude_le
  constructor
  · exact result.forward_confined
  · exact result.reverse_confined

/-- The concrete nonempty `221-01` circuit jointly exercises presentation
existence, normalized classification, ambient path transport, and both bounds. -/
theorem row22101_ambientCompilation_regression :
    AmbientFiveCircuitConclusion
      NormalizedBinaryFiveCircuitRows.row22101Start
      NormalizedBinaryFiveCircuitRows.row22101Finish := by
  apply exists_ambientFiveCircuitConclusion
  · exact NormalizedBinaryFiveCircuitRows.row22101Certificate.card_left
  · exact NormalizedBinaryFiveCircuitRows.row22101Certificate.card_right
  · exact NormalizedBinaryFiveCircuitRows.row22101Certificate.disjoint
  · exact row22101_ambient_evaluation_eq

#check @exactSpanCoordinateEmbedding
#check @mapState_exactSpanCoordinateEmbedding
#check @compileBinaryFiveCircuit
#check @BinaryFiveCircuitCompilation.forward
#check @BinaryFiveCircuitCompilation.reverse
#check @BinaryFiveCircuitCompilation.forward_confined
#check @BinaryFiveCircuitCompilation.reverse_confined
#check @AmbientInOrbit
#check @ambientInOrbit_label_unique
#check @exists_ambientFiveCircuitConclusion

#print axioms compileBinaryFiveCircuit
#print axioms BinaryFiveCircuitCompilation.forward
#print axioms BinaryFiveCircuitCompilation.forward_confined
#print axioms ambientInOrbit_label_unique
#print axioms exists_ambientFiveCircuitConclusion
#print axioms row22101_ambientCompilation_regression

end BilinearComplexity.BinaryFiveCircuitCompiler
