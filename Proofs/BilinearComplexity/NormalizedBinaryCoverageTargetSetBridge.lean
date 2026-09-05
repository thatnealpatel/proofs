import BilinearComplexity.NormalizedBinaryCoverageTargetData

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Generic bridge from primitive coverage targets to the semantic relation set

This module separates the inexpensive semantic argument from the four frozen
profile-specific primitive target computations. It shows that exact serialized
target coverage and exact decoded-support coverage suffice for equality with
the independently defined semantic relation enumeration.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.NormalizedBinaryCoverageTargetSetBridge

open NormalizedBinaryCarrier
open NormalizedBinaryCoverageData
open NormalizedBinaryCoverageTargetData
open NormalizedBinaryFiniteAction
open NormalizedBinaryRelationEnumeration
open NormalizedBinaryCompactEnumeration

/-- Decoding the literal targets of raw actions is the same as projecting their
serialized targets and decoding that serialized list. -/
theorem decodedTargets_eq_decodedSerializedTargets {p : Profile} {ι : Type*}
    (raws : List (RawCoverageAction p ι)) :
    RawCoverageAction.decodedTargets raws =
      decodedSerializedTargets p (raws.map (·.target)) := by
  induction raws with
  | nil => rfl
  | cons raw raws ih =>
      simp only [RawCoverageAction.decodedTargets, List.map_cons,
        decodedSerializedTargets, List.filterMap_cons,
        RawCoverageAction.decodedTarget?, ih]
      cases raw.target.decode? p <;> rfl

/-- A decoded target belongs to the decoding of a flattened serialized family
exactly when it belongs to the decoded family for one outer index. -/
theorem mem_decodedSerializedTargets_flatMap_iff {p : Profile} {α : Type*}
    (R : RelationEndpoints p) (xs : List α) (f : α → List SerializedEndpoints) :
    R ∈ decodedSerializedTargets p (xs.flatMap f) ↔
      ∃ x ∈ xs, R ∈ decodedSerializedTargets p (f x) := by
  simp only [decodedSerializedTargets, List.mem_filterMap, List.mem_flatMap]
  constructor
  · rintro ⟨s, ⟨x, hx, hs⟩, hdecode⟩
    exact ⟨x, hx, s, hs, hdecode⟩
  · rintro ⟨x, hx, s, hs, hdecode⟩
    exact ⟨s, ⟨x, hx, hs⟩, hdecode⟩

/-- If any one of a compact code's ten serialized splits decodes, then all five
serialized terms decode together as a support. This excludes extra targets from
malformed compact codes. -/
theorem decodedSupport?_isSome_of_mem_serializedTenSplits
    {p : Profile} {packed : PackedProfile} {q : FiveCode}
    {R : RelationEndpoints p}
    (hR : R ∈ decodedSerializedTargets p (serializedTenSplits packed q)) :
    ∃ K : State p, decodedSupport? p packed q = some K := by
  cases ha : (serializedTermOfIndex packed q.a).decode? p <;>
    cases hb : (serializedTermOfIndex packed q.b).decode? p <;>
    cases hc : (serializedTermOfIndex packed q.c).decode? p <;>
    cases hd : (serializedTermOfIndex packed q.d).decode? p <;>
    cases he : (serializedTermOfIndex packed q.e).decode? p <;>
    simp_all [decodedSerializedTargets, serializedTenSplits,
      SerializedEndpoints.decode?, SerializedEndpoints.decodeState?,
      decodedSupport?, serializedFiveTerms]

example :
    let p : Profile := ⟨0, 0, 0⟩
    let raws : List (RawCoverageAction p Unit) := []
    let codes : List FiveCode := []
    raws.map (·.target) = codes.flatMap (serializedTenSplits packed221) ∧
      ∀ K : State p,
        (∃ q ∈ codes, decodedSupport? p packed221 q = some K) ↔
          IsExactSupport K := by
  dsimp only
  constructor
  · rfl
  · intro K
    constructor
    · rintro ⟨q, hq, _⟩
      simp only [List.not_mem_nil] at hq
    · intro hK
      have hcardCarrier : Fintype.card (Carrier ⟨0, 0, 0⟩) = 0 := by
        decide
      have hle : K.card ≤ Fintype.card (Carrier ⟨0, 0, 0⟩) :=
        Finset.card_le_univ K
      rw [hcardCarrier] at hle
      exact False.elim (by
        have hcard : K.card = 5 := hK.1
        omega)

/-- Exact ordered coverage of primitive serialized targets, together with exact
coverage of decoded semantic supports, implies equality between the raw target
set and the independent enumeration of all exact relations. -/
theorem decodedTargetSet_eq_allExactRelations_of_rawTargets_eq
    {p : Profile} {ι : Type*} (raws : List (RawCoverageAction p ι))
    (packed : PackedProfile) (codes : List FiveCode)
    (htargets : raws.map (·.target) =
      codes.flatMap (serializedTenSplits packed))
    (hsupports : ∀ K : State p,
      (∃ q ∈ codes, decodedSupport? p packed q = some K) ↔
        IsExactSupport K) :
    RawCoverageAction.decodedTargetSet raws = allExactRelations p := by
  ext R
  constructor
  · intro hR
    have hraw : R ∈ RawCoverageAction.decodedTargets raws := by
      exact List.mem_toFinset.mp hR
    have hserialized : R ∈ decodedSerializedTargets p (raws.map (·.target)) := by
      rw [← decodedTargets_eq_decodedSerializedTargets raws]
      exact hraw
    have hcodes : R ∈ decodedSerializedTargets p
        (codes.flatMap (serializedTenSplits packed)) := by
      rw [← htargets]
      exact hserialized
    obtain ⟨q, hq, hqR⟩ :=
      (mem_decodedSerializedTargets_flatMap_iff R codes
        (serializedTenSplits packed)).mp hcodes
    obtain ⟨K, hqK⟩ :=
      decodedSupport?_isSome_of_mem_serializedTenSplits hqR
    have hKExact : IsExactSupport K :=
      (hsupports K).mp ⟨q, hq, hqK⟩
    have hlocal :
        (decodedSerializedTargets p (serializedTenSplits packed q)).toFinset =
          relationsOnSupport K :=
      decodedSerializedTargets_serializedTenSplits_toFinset hqK hKExact.1
    rw [allExactRelations, Finset.mem_biUnion]
    refine ⟨K, (mem_allExactSupports_iff K).mpr hKExact, ?_⟩
    rw [← hlocal, List.mem_toFinset]
    exact hqR
  · intro hR
    rw [allExactRelations, Finset.mem_biUnion] at hR
    obtain ⟨K, hKmem, hRK⟩ := hR
    have hKExact : IsExactSupport K :=
      (mem_allExactSupports_iff K).mp hKmem
    obtain ⟨q, hq, hqK⟩ := (hsupports K).mpr hKExact
    have hlocal :
        (decodedSerializedTargets p (serializedTenSplits packed q)).toFinset =
          relationsOnSupport K :=
      decodedSerializedTargets_serializedTenSplits_toFinset hqK hKExact.1
    have hqR : R ∈ decodedSerializedTargets p
        (serializedTenSplits packed q) := by
      rw [← List.mem_toFinset, hlocal]
      exact hRK
    have hcodes : R ∈ decodedSerializedTargets p
        (codes.flatMap (serializedTenSplits packed)) :=
      (mem_decodedSerializedTargets_flatMap_iff R codes
        (serializedTenSplits packed)).mpr ⟨q, hq, hqR⟩
    have hserialized : R ∈ decodedSerializedTargets p
        (raws.map (·.target)) := by
      rw [htargets]
      exact hcodes
    rw [RawCoverageAction.decodedTargetSet, List.mem_toFinset,
      decodedTargets_eq_decodedSerializedTargets]
    exact hserialized

#check @decodedTargets_eq_decodedSerializedTargets
#check @mem_decodedSerializedTargets_flatMap_iff
#check @decodedSupport?_isSome_of_mem_serializedTenSplits
#check @decodedTargetSet_eq_allExactRelations_of_rawTargets_eq
#print axioms decodedTargets_eq_decodedSerializedTargets
#print axioms mem_decodedSerializedTargets_flatMap_iff
#print axioms decodedSupport?_isSome_of_mem_serializedTenSplits
#print axioms decodedTargetSet_eq_allExactRelations_of_rawTargets_eq

end BilinearComplexity.NormalizedBinaryCoverageTargetSetBridge
