import BilinearComplexity.NormalizedBinaryCoverageData
import BilinearComplexity.NormalizedBinaryCompactEnumerationCore
import BilinearComplexity.NormalizedBinaryRelationEnumeration

set_option autoImplicit false

/-!
# Literal compact target data

This module serializes compact five-support codes into their ten ordered
two-versus-three endpoint splits. It proves generically that a successfully
decoded support of cardinality five produces exactly `relationsOnSupport`,
without depending on generated coverage tables or action checking.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.NormalizedBinaryCoverageTargetData

open NormalizedBinaryCarrier
open NormalizedBinaryCoverageData
open NormalizedBinaryFiniteAction
open NormalizedBinaryRelationEnumeration
open NormalizedBinaryCompactEnumeration

/-- Serialize the mixed-radix factor masks of one compact term index. -/
def serializedTermOfIndex (packed : PackedProfile) (i : Nat) : SerializedTermMasks :=
  let f := termFactors packed i
  ⟨f.1, f.2.1, f.2.2⟩

/-- Serialize the five compact term indices in their original order. -/
def serializedFiveTerms (packed : PackedProfile) (q : FiveCode) : List SerializedTermMasks :=
  [serializedTermOfIndex packed q.a, serializedTermOfIndex packed q.b,
    serializedTermOfIndex packed q.c, serializedTermOfIndex packed q.d,
    serializedTermOfIndex packed q.e]

/-- Serialize the ten ordered two-versus-three splits of a compact five-code. -/
def serializedTenSplits (packed : PackedProfile) (q : FiveCode) : List SerializedEndpoints :=
  let a := serializedTermOfIndex packed q.a
  let b := serializedTermOfIndex packed q.b
  let c := serializedTermOfIndex packed q.c
  let d := serializedTermOfIndex packed q.d
  let e := serializedTermOfIndex packed q.e
  [⟨[a,b], [c,d,e]⟩, ⟨[a,c], [b,d,e]⟩, ⟨[a,d], [b,c,e]⟩,
   ⟨[a,e], [b,c,d]⟩, ⟨[b,c], [a,d,e]⟩, ⟨[b,d], [a,c,e]⟩,
   ⟨[b,e], [a,c,d]⟩, ⟨[c,d], [a,b,e]⟩, ⟨[c,e], [a,b,d]⟩,
   ⟨[d,e], [a,b,c]⟩]

/-- Decode the five serialized compact terms as one typed normalized support. -/
def decodedSupport? (p : Profile) (packed : PackedProfile) (q : FiveCode) : Option (State p) :=
  SerializedEndpoints.decodeState? p (serializedFiveTerms packed q)

/-- Decode a list of serialized ordered endpoints, dropping malformed entries. -/
def decodedSerializedTargets (p : Profile) (xs : List SerializedEndpoints) : List (RelationEndpoints p) :=
  xs.filterMap (SerializedEndpoints.decode? p)

example : serializedTermOfIndex packed221 0 = ⟨1,1,1⟩ := by decide
example : (serializedFiveTerms packed221 ⟨0,1,3,4,8⟩).length = 5 := by decide
example : decodedSerializedTargets profile221 [] = [] := rfl

example : (serializedTenSplits packed221 ⟨0,1,3,4,8⟩).length = 10 := by decide


/-- The ten ordered two-versus-three endpoint splits of five typed terms. -/
def semanticTenSplits {p : Profile} (a b c d e : Carrier p) :
    List (RelationEndpoints p) :=
  [⟨{a,b}, {c,d,e}⟩, ⟨{a,c}, {b,d,e}⟩, ⟨{a,d}, {b,c,e}⟩,
   ⟨{a,e}, {b,c,d}⟩, ⟨{b,c}, {a,d,e}⟩, ⟨{b,d}, {a,c,e}⟩,
   ⟨{b,e}, {a,c,d}⟩, ⟨{c,d}, {a,b,e}⟩, ⟨{c,e}, {a,b,d}⟩,
   ⟨{d,e}, {a,b,c}⟩]

example :
    let t := NormalizedBinaryFiveCircuitRows.carrierOfMasks profile221
      1 1 1 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    (semanticTenSplits t t t t t).length = 10 := rfl

example : FiveCode.Valid packed221 ⟨0,1,3,4,8⟩ := by decide

example : ∃ K : State profile221,
    FiveCode.Valid packed221 ⟨0,1,3,4,8⟩ ∧
      decodedSupport? profile221 packed221 ⟨0,1,3,4,8⟩ = some K ∧
      K.card = 5 := by
  let t := NormalizedBinaryFiveCircuitRows.carrierOfMasks profile221
  refine ⟨{t 1 1 1 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    t 1 2 1 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    t 2 1 1 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    t 2 2 1 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    t 3 3 1 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)}, ?_, rfl, ?_⟩ <;> decide

/-- Successful decoding of the five terms decodes all ten serialized splits, preserving endpoint orientation. -/
theorem decodedSerializedTargets_serializedTenSplits {p : Profile} {packed : PackedProfile} {q : FiveCode}
    {a b c d e : Carrier p}
    (ha : (serializedTermOfIndex packed q.a).decode? p = some a)
    (hb : (serializedTermOfIndex packed q.b).decode? p = some b)
    (hc : (serializedTermOfIndex packed q.c).decode? p = some c)
    (hd : (serializedTermOfIndex packed q.d).decode? p = some d)
    (he : (serializedTermOfIndex packed q.e).decode? p = some e) :
    decodedSerializedTargets p (serializedTenSplits packed q) =
      semanticTenSplits a b c d e := by
  simp [decodedSerializedTargets, serializedTenSplits,
    SerializedEndpoints.decode?, SerializedEndpoints.decodeState?,
    ha, hb, hc, hd, he, semanticTenSplits]

set_option maxHeartbeats 2000000 in
/-- For five distinct terms, the explicit ten splits are exactly all relations on their support. -/
theorem semanticTenSplits_toFinset {p : Profile} {a b c d e : Carrier p}
    (hn : [a,b,c,d,e].Nodup) :
    (semanticTenSplits a b c d e).toFinset =
      relationsOnSupport ({a,b,c,d,e} : State p) := by
  classical
  let K : State p := {a,b,c,d,e}
  let P : Finset (State p) :=
    [{a,b}, {a,c}, {a,d}, {a,e}, {b,c}, {b,d}, {b,e}, {c,d}, {c,e}, {d,e}].toFinset
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_false_eq_true] at hn
  push Not at hn
  have ha : a ∉ ({b,c,d,e} : State p) := by simpa using hn.1
  have hb : b ∉ ({c,d,e} : State p) := by simpa using hn.2.1
  have hc : c ∉ ({d,e} : State p) := by simpa using hn.2.2.1
  have hd : d ∉ ({e} : State p) := by simpa using hn.2.2.2.1
  have hpow : K.powersetCard 2 = P := by
    have hemp : Finset.powersetCard 2 ({e} : State p) = ∅ :=
      Finset.powersetCard_eq_empty.mpr (by simp)
    dsimp only [K]
    rw [Finset.powersetCard_succ_insert ha 1,
      Finset.powersetCard_succ_insert hb 1,
      Finset.powersetCard_succ_insert hc 1,
      Finset.powersetCard_succ_insert hd 1, hemp]
    ext A
    simp only [Finset.powersetCard_one, P, Finset.map_singleton,
      Function.Embedding.coeFn_mk, Finset.image_singleton,
      Finset.pair_comm, Finset.empty_union, Finset.map_insert,
      Finset.image_insert, Finset.union_insert, Finset.singleton_union,
      Finset.insert_union, Finset.mem_insert, Finset.mem_singleton,
      List.toFinset_cons, List.toFinset_nil, insert_empty_eq]
    tauto
  have hab : K \ {a,b} = {c,d,e} := by
    rw [show K = {a,b} ∪ {c,d,e} by
      ext x
      simp only [K, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto]
    exact Finset.union_sdiff_cancel_left (by simp [Finset.disjoint_left, hn, ne_comm])
  have hac : K \ {a,c} = {b,d,e} := by
    rw [show K = {a,c} ∪ {b,d,e} by
      ext x
      simp only [K, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto]
    exact Finset.union_sdiff_cancel_left (by simp [Finset.disjoint_left, hn, ne_comm])
  have had : K \ {a,d} = {b,c,e} := by
    rw [show K = {a,d} ∪ {b,c,e} by
      ext x
      simp only [K, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto]
    exact Finset.union_sdiff_cancel_left (by simp [Finset.disjoint_left, hn, ne_comm])
  have hae : K \ {a,e} = {b,c,d} := by
    rw [show K = {a,e} ∪ {b,c,d} by
      ext x
      simp only [K, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto]
    exact Finset.union_sdiff_cancel_left (by simp [Finset.disjoint_left, hn, ne_comm])
  have hbc : K \ {b,c} = {a,d,e} := by
    rw [show K = {b,c} ∪ {a,d,e} by
      ext x
      simp only [K, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto]
    exact Finset.union_sdiff_cancel_left (by simp [Finset.disjoint_left, hn, ne_comm])
  have hbd : K \ {b,d} = {a,c,e} := by
    rw [show K = {b,d} ∪ {a,c,e} by
      ext x
      simp only [K, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto]
    exact Finset.union_sdiff_cancel_left (by simp [Finset.disjoint_left, hn, ne_comm])
  have hbe : K \ {b,e} = {a,c,d} := by
    rw [show K = {b,e} ∪ {a,c,d} by
      ext x
      simp only [K, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto]
    exact Finset.union_sdiff_cancel_left (by simp [Finset.disjoint_left, hn, ne_comm])
  have hcd : K \ {c,d} = {a,b,e} := by
    rw [show K = {c,d} ∪ {a,b,e} by
      ext x
      simp only [K, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto]
    exact Finset.union_sdiff_cancel_left (by simp [Finset.disjoint_left, hn, ne_comm])
  have hce : K \ {c,e} = {a,b,d} := by
    rw [show K = {c,e} ∪ {a,b,d} by
      ext x
      simp only [K, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto]
    exact Finset.union_sdiff_cancel_left (by simp [Finset.disjoint_left, hn, ne_comm])
  have hde : K \ {d,e} = {a,b,c} := by
    rw [show K = {d,e} ∪ {a,b,c} by
      ext x
      simp only [K, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto]
    exact Finset.union_sdiff_cancel_left (by simp [Finset.disjoint_left, hn, ne_comm])
  rw [relationsOnSupport, hpow]
  change (semanticTenSplits a b c d e).toFinset =
    P.image (fun A => ⟨A, K \ A⟩)
  simp only [semanticTenSplits, P, List.toFinset_cons, List.toFinset_nil,
    Finset.image_insert, Finset.image_empty, hab, hac, had, hae, hbc, hbd,
    hbe, hcd, hce, hde]

/-- A decoded compact support of cardinality five yields exactly all ten relations on that support. -/
theorem decodedSerializedTargets_serializedTenSplits_toFinset {p : Profile} {packed : PackedProfile} {q : FiveCode} {K : State p}
    (hdecode : decodedSupport? p packed q = some K) (hcard : K.card = 5) :
    (decodedSerializedTargets p (serializedTenSplits packed q)).toFinset =
      relationsOnSupport K := by
  cases ha : (serializedTermOfIndex packed q.a).decode? p with
  | none => simp [decodedSupport?, serializedFiveTerms,
      SerializedEndpoints.decodeState?, ha] at hdecode
  | some a =>
    cases hb : (serializedTermOfIndex packed q.b).decode? p with
    | none => simp [decodedSupport?, serializedFiveTerms,
        SerializedEndpoints.decodeState?, ha, hb] at hdecode
    | some b =>
      cases hc : (serializedTermOfIndex packed q.c).decode? p with
      | none => simp [decodedSupport?, serializedFiveTerms,
          SerializedEndpoints.decodeState?, ha, hb, hc] at hdecode
      | some c =>
        cases hd : (serializedTermOfIndex packed q.d).decode? p with
        | none => simp [decodedSupport?, serializedFiveTerms,
            SerializedEndpoints.decodeState?, ha, hb, hc, hd] at hdecode
        | some d =>
          cases he : (serializedTermOfIndex packed q.e).decode? p with
          | none => simp [decodedSupport?, serializedFiveTerms,
              SerializedEndpoints.decodeState?, ha, hb, hc, hd, he] at hdecode
          | some e =>
            have hK : ({a,b,c,d,e} : State p) = K := by
              simpa [decodedSupport?, serializedFiveTerms,
                SerializedEndpoints.decodeState?, ha, hb, hc, hd, he]
                using hdecode
            subst K
            have hn : [a,b,c,d,e].Nodup := by
              have hm : Multiset.Nodup
                  (Multiset.ofList [a,b,c,d,e]) := by
                apply Multiset.toFinset_card_eq_card_iff_nodup.mp
                simpa using hcard
              exact Multiset.coe_nodup.mp hm
            rw [show decodedSerializedTargets p (serializedTenSplits packed q) =
              semanticTenSplits a b c d e by
                simp [decodedSerializedTargets, serializedTenSplits,
                  SerializedEndpoints.decode?, SerializedEndpoints.decodeState?,
                  ha, hb, hc, hd, he, semanticTenSplits]]
            exact semanticTenSplits_toFinset hn

#check @decodedSerializedTargets_serializedTenSplits
#check @semanticTenSplits_toFinset
#check @decodedSerializedTargets_serializedTenSplits_toFinset
#print axioms decodedSerializedTargets_serializedTenSplits
#print axioms semanticTenSplits_toFinset
#print axioms decodedSerializedTargets_serializedTenSplits_toFinset

end BilinearComplexity.NormalizedBinaryCoverageTargetData
