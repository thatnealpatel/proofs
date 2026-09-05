import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import BilinearComplexity.NormalizedBinaryFiveCircuitCertificate
import BilinearComplexity.NormalizedBinaryFiniteAction

set_option autoImplicit false

/-!
# Reflected enumeration of exact normalized binary supports

This module defines a small executable reflection of full coordinate span and
uses it to enumerate five-element normalized supports with zero tensor
evaluation and exact factor profile. The executable span test enumerates the
at most `2 ^ 5` coefficient functions on the projected factors of a candidate
support, rather than reducing equality of abstract submodules.

The public membership theorem identifies the finite support enumeration with
its table-independent semantic predicate. Concrete profile counts and action
tables are intentionally left to separate frozen computation modules.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.NormalizedBinaryRelationEnumeration

open NormalizedBinaryCarrier
open NormalizedBinaryFiveCircuitCertificate
open NormalizedBinaryFiniteAction
open scoped BigOperators

/-- All linear combinations of a finite set of binary coordinate vectors,
represented as an executable finite set. -/
def combinationSet {d : ℕ} (s : Finset (CoordinateVector d)) :
    Finset (CoordinateVector d) :=
  Finset.univ.image fun f : s → F2 =>
    ∑ x : s, f x • (x : CoordinateVector d)

/-- The reflected linear-combination set contains exactly the abstract span. -/
theorem mem_combinationSet_iff {d : ℕ} (s : Finset (CoordinateVector d))
    (y : CoordinateVector d) :
    y ∈ combinationSet s ↔
      y ∈ Submodule.span F2 (↑s : Set (CoordinateVector d)) := by
  constructor
  · intro hy
    rw [combinationSet, Finset.mem_image] at hy
    obtain ⟨f, _, rfl⟩ := hy
    exact Submodule.sum_mem _ fun x _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span x.property)
  · intro hy
    rw [Submodule.mem_span_finset] at hy
    obtain ⟨f, _, hf⟩ := hy
    rw [combinationSet, Finset.mem_image]
    refine ⟨fun x => f x, Finset.mem_univ _, ?_⟩
    rw [← hf]
    exact Finset.sum_attach s fun x => f x • x

/-- A Boolean full-span test obtained by comparing the reflected linear
combinations with the entire finite coordinate space. -/
def spansCheck {d : ℕ} (s : Finset (CoordinateVector d)) : Bool :=
  combinationSet s == Finset.univ

/-- The Boolean full-span test is equivalent to equality of the abstract span
with the full coordinate space. -/
theorem spansCheck_eq_true_iff {d : ℕ} (s : Finset (CoordinateVector d)) :
    spansCheck s = true ↔
      Submodule.span F2 (↑s : Set (CoordinateVector d)) = ⊤ := by
  rw [spansCheck, beq_iff_eq]
  constructor
  · intro h
    apply top_unique
    intro y _
    rw [← mem_combinationSet_iff, h]
    exact Finset.mem_univ y
  · intro h
    ext y
    simp only [Finset.mem_univ, iff_true]
    rw [mem_combinationSet_iff, h]
    exact Submodule.mem_top

/-- Executable reflection of exactness of all three projected factor spans. -/
def reflectedExactProfile {p : Profile} (K : State p) : Bool :=
  spansCheck (K.image fun t => t.1.1) &&
    spansCheck (K.image fun t => t.2.1.1) &&
    spansCheck (K.image fun t => t.2.2.1)

/-- The reflected three-factor test is equivalent to the existing semantic
exact-factor-profile predicate. -/
theorem reflectedExactProfile_eq_true_iff {p : Profile} (K : State p) :
    reflectedExactProfile K = true ↔ HasExactFactorProfile K := by
  simp only [reflectedExactProfile, Bool.and_eq_true, spansCheck_eq_true_iff,
    HasExactFactorProfile, firstFactorSpan, secondFactorSpan, thirdFactorSpan]
  constructor
  · rintro ⟨⟨hfirst, hsecond⟩, hthird⟩
    exact ⟨hfirst, hsecond, hthird⟩
  · rintro ⟨hfirst, hsecond, hthird⟩
    exact ⟨⟨hfirst, hsecond⟩, hthird⟩

/-- The semantic predicate for a normalized five-element exact support. -/
def IsExactSupport {p : Profile} (K : State p) : Prop :=
  K.card = 5 ∧ stateEvaluation K = 0 ∧ HasExactFactorProfile K

/-- All normalized five-element supports having zero tensor evaluation and
exact projected factor spans. -/
def allExactSupports (p : Profile) : Finset (State p) :=
  ((Finset.univ : Finset (Carrier p)).powersetCard 5).filter fun K =>
    stateEvaluation K = 0 ∧ reflectedExactProfile K = true

/-- Membership in the finite exact-support enumeration is equivalent to the
table-independent semantic exact-support predicate. -/
theorem mem_allExactSupports_iff {p : Profile} (K : State p) :
    K ∈ allExactSupports p ↔ IsExactSupport K := by
  rw [allExactSupports, Finset.mem_filter, Finset.mem_powersetCard]
  simp only [Finset.subset_univ, true_and, IsExactSupport]
  rw [reflectedExactProfile_eq_true_iff]

example : IsExactSupport
    (NormalizedBinaryReplay221.S0 ∪ NormalizedBinaryReplay221.S2) := by
  refine ⟨NormalizedBinaryReplay221.designated_endpoint_exact_profile_221.2.1,
    ?_, NormalizedBinaryFiveCircuitCertificate.designated_endpoint_hasExactFactorProfile⟩
  decide

/-- A semantic exact normalized relation has ordered sides of cardinalities two
and three, disjoint sides with equal evaluation, and full projected spans. -/
def IsExactRelation {p : Profile} (R : RelationEndpoints p) : Prop :=
  R.left.card = 2 ∧
    R.right.card = 3 ∧
    Disjoint R.left R.right ∧
    stateEvaluation R.left = stateEvaluation R.right ∧
    HasExactFactorProfile (R.left ∪ R.right)

/-- A proof-bearing exact normalized relation. -/
def ExactRelation (p : Profile) : Type :=
  {R : RelationEndpoints p // IsExactRelation R}

/-- The semantic exact-relation hypotheses imply that the endpoint union is a
normalized five-element circuit. -/
theorem IsExactRelation.circuit {p : Profile} {R : RelationEndpoints p}
    (hR : IsExactRelation R) :
    BinaryCircuit.Circuit (@tensorEvaluation p) (R.left ∪ R.right) := by
  exact tensorEvaluation_circuit_union_of_disjoint_card_two_card_three
    hR.2.2.1 hR.1 hR.2.1 hR.2.2.2.1

/-- Evaluation of a disjoint union is the sum of the endpoint evaluations. -/
theorem stateEvaluation_union {p : Profile} {A B : State p}
    (hAB : Disjoint A B) :
    stateEvaluation (A ∪ B) = stateEvaluation A + stateEvaluation B := by
  simp only [stateEvaluation, BinaryCircuit.evaluation]
  rw [Finset.sum_union hAB]

/-- For disjoint binary states, zero evaluation of the union is equivalent to
equality of the two endpoint evaluations. -/
theorem stateEvaluation_union_eq_zero_iff {p : Profile} {A B : State p}
    (hAB : Disjoint A B) :
    stateEvaluation (A ∪ B) = 0 ↔
      stateEvaluation A = stateEvaluation B := by
  rw [stateEvaluation_union hAB]
  constructor
  · intro hzero
    have hadd := congrArg (fun x => x + stateEvaluation B) hzero
    simpa only [add_assoc, ZModModule.add_self, add_zero, zero_add] using hadd
  · intro heq
    rw [heq]
    exact ZModModule.add_self _

/-- The ten ordered two-versus-three splits generated from a five-element
support, represented without exchanging the endpoint slots. -/
def relationsOnSupport {p : Profile} (K : State p) :
    Finset (RelationEndpoints p) :=
  (K.powersetCard 2).image fun A =>
    { left := A, right := K \ A }

/-- Membership in the splits of a support is exactly containment and
cardinality two of the left side together with the forced complement right
side. -/
theorem mem_relationsOnSupport_iff {p : Profile} (K : State p)
    (R : RelationEndpoints p) :
    R ∈ relationsOnSupport K ↔
      R.left ⊆ K ∧ R.left.card = 2 ∧ R.right = K \ R.left := by
  constructor
  · intro hR
    rw [relationsOnSupport, Finset.mem_image] at hR
    obtain ⟨A, hA, rfl⟩ := hR
    have hAK := Finset.mem_powersetCard.mp hA
    exact ⟨hAK.1, hAK.2, rfl⟩
  · rintro ⟨hsub, hcard, hright⟩
    rw [relationsOnSupport, Finset.mem_image]
    refine ⟨R.left, Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩, ?_⟩
    cases R with
    | mk left right =>
      dsimp only at hright ⊢
      rw [hright]

/-- Every exact support split into a two-element left side and its complement. -/
def allExactRelations (p : Profile) : Finset (RelationEndpoints p) :=
  (allExactSupports p).biUnion relationsOnSupport

/-- Membership in the finite relation enumeration is equivalent to the
independent semantic exact-relation predicate. -/
theorem mem_allExactRelations_iff {p : Profile} (R : RelationEndpoints p) :
    R ∈ allExactRelations p ↔ IsExactRelation R := by
  constructor
  · intro hR
    rw [allExactRelations, Finset.mem_biUnion] at hR
    obtain ⟨K, hKmem, hsplit⟩ := hR
    have hK : IsExactSupport K := (mem_allExactSupports_iff K).mp hKmem
    have hs := (mem_relationsOnSupport_iff K R).mp hsplit
    have hrightCard : R.right.card = 3 := by
      rw [hs.2.2, Finset.card_sdiff_of_subset hs.1, hK.1, hs.2.1]
    have hdisjoint : Disjoint R.left R.right := by
      rw [hs.2.2]
      exact Finset.disjoint_sdiff
    have hunion : R.left ∪ R.right = K := by
      rw [hs.2.2]
      exact Finset.union_sdiff_of_subset hs.1
    have hevaluation : stateEvaluation R.left = stateEvaluation R.right := by
      rw [← stateEvaluation_union_eq_zero_iff hdisjoint, hunion]
      exact hK.2.1
    exact ⟨hs.2.1, hrightCard, hdisjoint, hevaluation, hunion ▸ hK.2.2⟩
  · intro hR
    let K : State p := R.left ∪ R.right
    have hKCard : K.card = 5 := by
      dsimp only [K]
      rw [Finset.card_union_of_disjoint hR.2.2.1, hR.1, hR.2.1]
    have hKZero : stateEvaluation K = 0 := by
      dsimp only [K]
      rw [stateEvaluation_union_eq_zero_iff hR.2.2.1]
      exact hR.2.2.2.1
    have hKExact : HasExactFactorProfile K := by
      exact hR.2.2.2.2
    have hKmem : K ∈ allExactSupports p :=
      (mem_allExactSupports_iff K).mpr ⟨hKCard, hKZero, hKExact⟩
    rw [allExactRelations, Finset.mem_biUnion]
    refine ⟨K, hKmem, (mem_relationsOnSupport_iff K R).mpr ⟨?_, hR.1, ?_⟩⟩
    · intro x hx
      exact Finset.mem_union_left R.right hx
    · ext x
      simp only [K, Finset.mem_sdiff, Finset.mem_union]
      constructor
      · intro hxright
        refine ⟨Or.inr hxright, ?_⟩
        intro hxleft
        exact Finset.disjoint_left.mp hR.2.2.1 hxleft hxright
      · rintro ⟨hxunion, hnleft⟩
        rcases hxunion with hxleft | hxright
        · exact False.elim (hnleft hxleft)
        · exact hxright

example : ExactRelation profile221 :=
  ⟨{ left := NormalizedBinaryReplay221.S0,
      right := NormalizedBinaryReplay221.S2 },
    NormalizedBinaryReplay221.state_cardinalities.1,
    NormalizedBinaryReplay221.state_cardinalities.2.2,
    NormalizedBinaryReplay221.designated_endpoint_exact_profile_221.1,
    NormalizedBinaryReplay221.endpoint_evaluations.2,
    NormalizedBinaryFiveCircuitCertificate.designated_endpoint_hasExactFactorProfile⟩

#check @mem_combinationSet_iff
#check @spansCheck_eq_true_iff
#check @reflectedExactProfile_eq_true_iff
#check @mem_allExactSupports_iff
#check @IsExactRelation.circuit
#check @stateEvaluation_union
#check @stateEvaluation_union_eq_zero_iff
#check @mem_relationsOnSupport_iff
#check @mem_allExactRelations_iff
#print axioms stateEvaluation_union_eq_zero_iff
#print axioms mem_allExactSupports_iff
#print axioms mem_allExactRelations_iff
#print axioms IsExactRelation.circuit

end BilinearComplexity.NormalizedBinaryRelationEnumeration
