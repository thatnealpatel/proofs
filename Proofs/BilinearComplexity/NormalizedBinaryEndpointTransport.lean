import BilinearComplexity.NormalizedBinaryMoveTransport

set_option autoImplicit false

/-!
# Ordered transport of the designated profile-221 endpoints

This module packages the two mapped endpoints of the designated normalized
binary profile-`221` replay.  The carrier map is applied as a `Finset.image`,
so all statements retain finite-set semantics.  Each projected factor span is
identified with the range of the corresponding `ZMod 2`-linear map.

All three factors remain in their given order.  Nothing here supplies a mode
permutation, an orbit action, orbit coverage, or a classification of circuits.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.NormalizedBinaryEndpointTransport

open NormalizedBinaryCarrier
open NormalizedBinaryReplay221
open NormalizedBinaryMoveTransport
open BinaryCircuit

example : Nonempty (FactorwiseAdditiveInjection profile221 profile221) := by
  refine ⟨{
    first := AddMonoidHom.id (CoordinateVector profile221.first)
    second := AddMonoidHom.id (CoordinateVector profile221.second)
    third := AddMonoidHom.id (CoordinateVector profile221.third)
    first_injective := ?_
    second_injective := ?_
    third_injective := ?_ }⟩
  all_goals
    intro u v huv
    exact huv

/-- The image of the designated source endpoint union is exactly the union of
the two mapped endpoints. -/
theorem mapped_endpoint_union {q : Profile}
    (f : FactorwiseAdditiveInjection profile221 q) :
    mapState f (S0 ∪ S2) = mapState f S0 ∪ mapState f S2 := by
  exact mapState_union f S0 S2

/-- The two mapped designated endpoints remain disjoint as finite sets. -/
theorem mapped_endpoints_disjoint {q : Profile}
    (f : FactorwiseAdditiveInjection profile221 q) :
    Disjoint (mapState f S0) (mapState f S2) := by
  exact (Finset.disjoint_image (mapTerm_injective f)).mpr
    designated_endpoint_exact_profile_221.1

/-- The mapped designated endpoints have exact cardinalities two and three. -/
theorem mapped_endpoint_cardinalities {q : Profile}
    (f : FactorwiseAdditiveInjection profile221 q) :
    (mapState f S0).card = 2 ∧ (mapState f S2).card = 3 := by
  exact ⟨(mapState_card f S0).trans state_cardinalities.1,
    (mapState_card f S2).trans state_cardinalities.2.2⟩

/-- The union of the mapped designated endpoints has exactly five terms. -/
theorem mapped_endpoint_union_card {q : Profile}
    (f : FactorwiseAdditiveInjection profile221 q) :
    (mapState f S0 ∪ mapState f S2).card = 5 := by
  calc
    (mapState f S0 ∪ mapState f S2).card =
        (mapState f (S0 ∪ S2)).card :=
      congrArg Finset.card (mapped_endpoint_union f).symm
    _ = (S0 ∪ S2).card := mapState_card f (S0 ∪ S2)
    _ = 5 := designated_endpoint_exact_profile_221.2.1

/-- The mapped forward and reverse paths give both orientations of the exact
target-profile endpoint evaluation equality. -/
theorem mapped_endpoint_evaluations {q : Profile}
    (f : FactorwiseAdditiveInjection profile221 q) :
    stateEvaluation (mapState f S2) = stateEvaluation (mapState f S0) ∧
      stateEvaluation (mapState f S0) = stateEvaluation (mapState f S2) := by
  exact ⟨mapPath_preserves_evaluation f forwardPath,
    mapPath_preserves_evaluation f reversePath⟩

/-- Every vertex of either mapped designated path remains in the image of the
explicit six-term source boundary. -/
theorem mapped_paths_confined {q : Profile}
    (f : FactorwiseAdditiveInjection profile221 q) :
    (∀ Y, PathVertex (mapForwardPath f) Y → Y ⊆ mapState f boundary) ∧
      (∀ Y, PathVertex (mapReversePath f) Y → Y ⊆ mapState f boundary) := by
  constructor
  · exact mapPath_confined f forwardPath paths_confined.1
  · exact mapPath_confined f reversePath paths_confined.2.1

/-- Projecting the mapped endpoint union to its first factor is the finite-set
image under the ordered first factor map of the source projection. -/
theorem mapped_endpoint_first_projection {q : Profile}
    (f : FactorwiseAdditiveInjection profile221 q) :
    ((mapState f S0 ∪ mapState f S2).image (fun t => t.1.1)) =
      ((S0 ∪ S2).image (fun t => t.1.1)).image f.first := by
  simp only [mapState, Finset.image_union, Finset.image_image]
  rfl

/-- Projecting the mapped endpoint union to its second factor is the finite-set
image under the ordered second factor map of the source projection. -/
theorem mapped_endpoint_second_projection {q : Profile}
    (f : FactorwiseAdditiveInjection profile221 q) :
    ((mapState f S0 ∪ mapState f S2).image (fun t => t.2.1.1)) =
      ((S0 ∪ S2).image (fun t => t.2.1.1)).image f.second := by
  simp only [mapState, Finset.image_union, Finset.image_image]
  rfl

/-- Projecting the mapped endpoint union to its third factor is the finite-set
image under the ordered third factor map of the source projection. -/
theorem mapped_endpoint_third_projection {q : Profile}
    (f : FactorwiseAdditiveInjection profile221 q) :
    ((mapState f S0 ∪ mapState f S2).image (fun t => t.2.2.1)) =
      ((S0 ∪ S2).image (fun t => t.2.2.1)).image f.third := by
  simp only [mapState, Finset.image_union, Finset.image_image]
  rfl

private theorem source_endpoint_first_span_eq_top :
    Submodule.span F2
      (((S0 ∪ S2).image (fun t => t.1.1) : Finset (CoordinateVector 2)) :
        Set (CoordinateVector 2)) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [designated_endpoint_exact_profile_221.2.2.2.1,
    Module.finrank_fin_fun]

private theorem source_endpoint_second_span_eq_top :
    Submodule.span F2
      (((S0 ∪ S2).image (fun t => t.2.1.1) : Finset (CoordinateVector 2)) :
        Set (CoordinateVector 2)) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [designated_endpoint_exact_profile_221.2.2.2.2.1,
    Module.finrank_fin_fun]

private theorem source_endpoint_third_span_eq_top :
    Submodule.span F2
      (((S0 ∪ S2).image (fun t => t.2.2.1) : Finset (CoordinateVector 1)) :
        Set (CoordinateVector 1)) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [designated_endpoint_exact_profile_221.2.2.2.2.2.1,
    Module.finrank_fin_fun]

private theorem span_image_eq_range {a b : ℕ}
    (g : CoordinateVector a →+ CoordinateVector b)
    (s : Finset (CoordinateVector a))
    (hspan : Submodule.span F2 (s : Set (CoordinateVector a)) = ⊤) :
    Submodule.span F2
      ((s.image g : Finset (CoordinateVector b)) : Set (CoordinateVector b)) =
      LinearMap.range (g.toZModLinearMap 2) := by
  rw [Finset.coe_image]
  change Submodule.span F2
      ((g.toZModLinearMap 2 : CoordinateVector a → CoordinateVector b) ''
        (s : Set (CoordinateVector a))) =
    LinearMap.range (g.toZModLinearMap 2)
  rw [← LinearMap.map_span, hspan, Submodule.map_top]

/-- The span of the mapped first-coordinate endpoint projection is exactly the
range of the ordered first factor's induced `ZMod 2`-linear map. -/
theorem mapped_endpoint_first_span_eq_range {q : Profile}
    (f : FactorwiseAdditiveInjection profile221 q) :
    Submodule.span F2
      (((mapState f S0 ∪ mapState f S2).image (fun t => t.1.1) :
        Finset (CoordinateVector q.first)) : Set (CoordinateVector q.first)) =
      LinearMap.range (f.first.toZModLinearMap 2) := by
  rw [mapped_endpoint_first_projection f]
  exact span_image_eq_range f.first _ source_endpoint_first_span_eq_top

/-- The span of the mapped second-coordinate endpoint projection is exactly the
range of the ordered second factor's induced `ZMod 2`-linear map. -/
theorem mapped_endpoint_second_span_eq_range {q : Profile}
    (f : FactorwiseAdditiveInjection profile221 q) :
    Submodule.span F2
      (((mapState f S0 ∪ mapState f S2).image (fun t => t.2.1.1) :
        Finset (CoordinateVector q.second)) : Set (CoordinateVector q.second)) =
      LinearMap.range (f.second.toZModLinearMap 2) := by
  rw [mapped_endpoint_second_projection f]
  exact span_image_eq_range f.second _ source_endpoint_second_span_eq_top

/-- The span of the mapped third-coordinate endpoint projection is exactly the
range of the ordered third factor's induced `ZMod 2`-linear map. -/
theorem mapped_endpoint_third_span_eq_range {q : Profile}
    (f : FactorwiseAdditiveInjection profile221 q) :
    Submodule.span F2
      (((mapState f S0 ∪ mapState f S2).image (fun t => t.2.2.1) :
        Finset (CoordinateVector q.third)) : Set (CoordinateVector q.third)) =
      LinearMap.range (f.third.toZModLinearMap 2) := by
  rw [mapped_endpoint_third_projection f]
  exact span_image_eq_range f.third _ source_endpoint_third_span_eq_top

/-- The mapped first-coordinate endpoint span has exact finrank two. -/
theorem mapped_endpoint_first_finrank {q : Profile}
    (f : FactorwiseAdditiveInjection profile221 q) :
    Module.finrank F2
      (Submodule.span F2
        (((mapState f S0 ∪ mapState f S2).image (fun t => t.1.1) :
          Finset (CoordinateVector q.first)) : Set (CoordinateVector q.first))) =
      2 := by
  rw [mapped_endpoint_first_span_eq_range f,
    LinearMap.finrank_range_of_inj]
  · exact Module.finrank_fin_fun F2
  · simpa only [AddMonoidHom.coe_toZModLinearMap] using f.first_injective

/-- The mapped second-coordinate endpoint span has exact finrank two. -/
theorem mapped_endpoint_second_finrank {q : Profile}
    (f : FactorwiseAdditiveInjection profile221 q) :
    Module.finrank F2
      (Submodule.span F2
        (((mapState f S0 ∪ mapState f S2).image (fun t => t.2.1.1) :
          Finset (CoordinateVector q.second)) : Set (CoordinateVector q.second))) =
      2 := by
  rw [mapped_endpoint_second_span_eq_range f,
    LinearMap.finrank_range_of_inj]
  · exact Module.finrank_fin_fun F2
  · simpa only [AddMonoidHom.coe_toZModLinearMap] using f.second_injective

/-- The mapped third-coordinate endpoint span has exact finrank one. -/
theorem mapped_endpoint_third_finrank {q : Profile}
    (f : FactorwiseAdditiveInjection profile221 q) :
    Module.finrank F2
      (Submodule.span F2
        (((mapState f S0 ∪ mapState f S2).image (fun t => t.2.2.1) :
          Finset (CoordinateVector q.third)) : Set (CoordinateVector q.third))) =
      1 := by
  rw [mapped_endpoint_third_span_eq_range f,
    LinearMap.finrank_range_of_inj]
  · exact Module.finrank_fin_fun F2
  · simpa only [AddMonoidHom.coe_toZModLinearMap] using f.third_injective

/-- The mapped designated endpoint union is a genuine target-profile circuit.
Its cycle equality comes from the mapped reverse path, not from a separately
defined tensor-functoriality construction or a coordinate computation. -/
theorem mapped_endpoint_circuit {q : Profile}
    (f : FactorwiseAdditiveInjection profile221 q) :
    Circuit (@tensorEvaluation q) (mapState f S0 ∪ mapState f S2) := by
  apply tensorEvaluation_circuit_union_of_disjoint_card_two_card_three
    (mapped_endpoints_disjoint f)
  · exact (mapped_endpoint_cardinalities f).1
  · exact (mapped_endpoint_cardinalities f).2
  · exact (mapped_endpoint_evaluations f).2

/-- Under any injection in the three corresponding ordered factors, the
mapped designated profile-`221` endpoints are disjoint two- and three-term
states whose five-term union is a circuit; mapping commutes with their union,
and their ordered projected spans are precisely the three linear-map ranges
with finranks `2`, `2`, and `1`.  This package makes no factor-mode
permutation, orbit-coverage, or circuit-classification claim. -/
theorem mapped_designated_endpoint_exact_profile_221 {q : Profile}
    (f : FactorwiseAdditiveInjection profile221 q) :
    (mapState f S0).card = 2 ∧
    (mapState f S2).card = 3 ∧
    Disjoint (mapState f S0) (mapState f S2) ∧
    mapState f (S0 ∪ S2) = mapState f S0 ∪ mapState f S2 ∧
    (mapState f S0 ∪ mapState f S2).card = 5 ∧
    Circuit (@tensorEvaluation q) (mapState f S0 ∪ mapState f S2) ∧
    Submodule.span F2
      (((mapState f S0 ∪ mapState f S2).image (fun t => t.1.1) :
        Finset (CoordinateVector q.first)) : Set (CoordinateVector q.first)) =
      LinearMap.range (f.first.toZModLinearMap 2) ∧
    Submodule.span F2
      (((mapState f S0 ∪ mapState f S2).image (fun t => t.2.1.1) :
        Finset (CoordinateVector q.second)) : Set (CoordinateVector q.second)) =
      LinearMap.range (f.second.toZModLinearMap 2) ∧
    Submodule.span F2
      (((mapState f S0 ∪ mapState f S2).image (fun t => t.2.2.1) :
        Finset (CoordinateVector q.third)) : Set (CoordinateVector q.third)) =
      LinearMap.range (f.third.toZModLinearMap 2) ∧
    Module.finrank F2
      (Submodule.span F2
        (((mapState f S0 ∪ mapState f S2).image (fun t => t.1.1) :
          Finset (CoordinateVector q.first)) : Set (CoordinateVector q.first))) =
      2 ∧
    Module.finrank F2
      (Submodule.span F2
        (((mapState f S0 ∪ mapState f S2).image (fun t => t.2.1.1) :
          Finset (CoordinateVector q.second)) : Set (CoordinateVector q.second))) =
      2 ∧
    Module.finrank F2
      (Submodule.span F2
        (((mapState f S0 ∪ mapState f S2).image (fun t => t.2.2.1) :
          Finset (CoordinateVector q.third)) : Set (CoordinateVector q.third))) =
      1 := by
  constructor
  · exact (mapped_endpoint_cardinalities f).1
  constructor
  · exact (mapped_endpoint_cardinalities f).2
  constructor
  · exact mapped_endpoints_disjoint f
  constructor
  · exact mapped_endpoint_union f
  constructor
  · exact mapped_endpoint_union_card f
  constructor
  · exact mapped_endpoint_circuit f
  constructor
  · exact mapped_endpoint_first_span_eq_range f
  constructor
  · exact mapped_endpoint_second_span_eq_range f
  constructor
  · exact mapped_endpoint_third_span_eq_range f
  constructor
  · exact mapped_endpoint_first_finrank f
  constructor
  · exact mapped_endpoint_second_finrank f
  · exact mapped_endpoint_third_finrank f

#check @mapState_union
#check @mapped_endpoint_circuit
#check @mapped_endpoint_first_span_eq_range
#check @mapped_endpoint_second_span_eq_range
#check @mapped_endpoint_third_span_eq_range
#check @mapped_designated_endpoint_exact_profile_221

#print axioms mapped_designated_endpoint_exact_profile_221

end BilinearComplexity.NormalizedBinaryEndpointTransport
