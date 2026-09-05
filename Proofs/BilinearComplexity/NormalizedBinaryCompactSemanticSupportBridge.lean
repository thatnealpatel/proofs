import BilinearComplexity.NormalizedBinaryCompactSupportSemantics
import BilinearComplexity.NormalizedBinaryCoverageTargetData

set_option autoImplicit false

/-!
# Compact exact-support semantic bridge

This module identifies the four frozen compact-code tables with the semantic
exact supports for profiles `221`, `411`, `321`, and `222`. It proves canonical
decoder interoperability, constructs inverse sorted codes, and transfers the
reviewed exact-table checks through the generic support acceptance theorem.
-/

namespace BilinearComplexity.NormalizedBinaryCompactSemanticSupportBridge

open NormalizedBinaryCarrier
open NormalizedBinaryCompactEnumeration
open NormalizedBinaryCompactEnumerationBridge
open NormalizedBinaryCompactMaskSemantics
open NormalizedBinaryCompactSupportSemantics
open NormalizedBinaryFiveCircuitCertificate
open NormalizedBinaryRelationEnumeration
open NormalizedBinaryCoverageTargetData
open NormalizedBinaryCoverageData

/-- Decode a natural index through a nonempty finite canonical decoder, using index zero out of range. -/
def decodeNat {n : Nat} {α : Type*} (hn : 0 < n) (decoder : Fin n → α)
    (i : Nat) : α :=
  if hi : i < n then decoder ⟨i, hi⟩ else decoder ⟨0, hn⟩

example : decodeNat (n := 3) (by decide) (fun i : Fin 3 => i.val + 1) 2 = 3 := rfl

/-- Decode the five fields of a compact code as a finite semantic support. -/
def decodeFiveCodeWith {n : Nat} {α : Type*} [DecidableEq α] (hn : 0 < n)
    (decoder : Fin n → α) (q : FiveCode) : Finset α :=
  q.toList.toFinset.image (decodeNat hn decoder)

example : decodeFiveCodeWith (n := 5) (by decide) (fun i : Fin 5 => i.val)
    ⟨0, 1, 2, 3, 4⟩ = {0, 1, 2, 3, 4} := by
  ext i
  simp [decodeFiveCodeWith, decodeNat, FiveCode.toList]

/-- Every field of a valid five-code lies below its term-count bound. -/
theorem mem_toList_toFinset_lt {n : Nat} {q : FiveCode}
    (hq : q.a < q.b ∧ q.b < q.c ∧ q.c < q.d ∧ q.d < q.e ∧ q.e < n)
    {i : Nat} (hi : i ∈ q.toList.toFinset) : i < n := by
  simp only [FiveCode.toList, List.mem_toFinset, List.mem_cons,
    List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> omega

/-- The fields of a valid five-code contain no repetition. -/
theorem FiveCode.toList_nodup {n : Nat} {q : FiveCode}
    (hq : q.a < q.b ∧ q.b < q.c ∧ q.c < q.d ∧ q.d < q.e ∧ q.e < n) :
    q.toList.Nodup := by
  rcases hq with ⟨hab, hbc, hcd, hde, he⟩
  simp only [FiveCode.toList, List.nodup_cons, List.mem_cons,
    List.mem_nil_iff, or_false, not_or, not_false_eq_true]
  refine ⟨⟨by omega, by omega, by omega, by omega⟩,
    ⟨⟨by omega, by omega, by omega⟩,
      ⟨⟨by omega, by omega⟩, ⟨by omega, True.intro, List.nodup_nil⟩⟩⟩⟩

/-- Decoding a valid five-code through an injective decoder produces five terms. -/
theorem decodeFiveCodeWith_card {n : Nat} {α : Type*} [DecidableEq α]
    (hn : 0 < n)
    (decoder : Fin n → α)
    (hinjective : Function.Injective decoder) (q : FiveCode)
    (hq : q.a < q.b ∧ q.b < q.c ∧ q.c < q.d ∧ q.d < q.e ∧ q.e < n) :
    (decodeFiveCodeWith hn decoder q).card = 5 := by
  rw [decodeFiveCodeWith, Finset.card_image_iff.mpr]
  · rw [List.toFinset_card_of_nodup (FiveCode.toList_nodup hq)]
    rfl
  · intro i hi j hj hij
    have hiBound := mem_toList_toFinset_lt hq hi
    have hjBound := mem_toList_toFinset_lt hq hj
    simp only [decodeNat, hiBound, ↓reduceDIte, hjBound] at hij
    exact congrArg Fin.val (hinjective hij)

/-- Decoding the sorted code of five bounded indices recovers the decoder image of those indices. -/
theorem decodeFiveCodeWith_sorted {n : Nat} {α : Type*} [DecidableEq α]
    (hn : 0 < n)
    (decoder : Fin n → α)
    (s : Finset (Fin n)) (hcard : s.card = 5) :
    decodeFiveCodeWith hn decoder (sortedFiveCode s hcard) = s.image decoder := by
  rw [decodeFiveCodeWith, sortedFiveCode_toFinset, Finset.image_image]
  apply Finset.image_congr
  intro i hi
  simp only [Function.comp_apply, decodeNat, i.isLt, ↓reduceDIte]

private structure ProfileDecoderData (p : Profile) where
  packed : PackedProfile
  count_pos : 0 < packed.termCount
  decoder : Fin packed.termCount → Carrier p
  bijective : Function.Bijective decoder
  first_eq : packed.first = p.first
  second_eq : packed.second = p.second
  third_eq : packed.third = p.third
  first_spec : ∀ i : Fin packed.termCount, (decoder i).1.1 =
    NormalizedBinaryCompactMaskSemantics.maskVector p.first (termFactors packed i).1
  second_spec : ∀ i : Fin packed.termCount, (decoder i).2.1.1 =
    NormalizedBinaryCompactMaskSemantics.maskVector p.second (termFactors packed i).2.1
  third_spec : ∀ i : Fin packed.termCount, (decoder i).2.2.1 =
    NormalizedBinaryCompactMaskSemantics.maskVector p.third (termFactors packed i).2.2
  tensor_spec : ∀ i : Fin packed.termCount, tensorOfMask p (packed.tensorMask i) =
    tensorEvaluation (decoder i)
  first_bound : ∀ i : Fin packed.termCount, (termFactors packed i).1 < 2 ^ p.first
  second_bound : ∀ i : Fin packed.termCount, (termFactors packed i).2.1 < 2 ^ p.second
  third_bound : ∀ i : Fin packed.termCount, (termFactors packed i).2.2 < 2 ^ p.third
  tensor_bound : ∀ i : Fin packed.termCount, packed.tensorMask i <
    2 ^ ((p.first * p.second) * p.third)

private def data221 : ProfileDecoderData profile221 where
  packed := packed221
  count_pos := by decide
  decoder := decode221
  bijective := decode221_bijective
  first_eq := rfl
  second_eq := rfl
  third_eq := rfl
  first_spec := by
    intro i
    fin_cases i <;> rfl
  second_spec := by
    intro i
    fin_cases i <;> rfl
  third_spec := by
    intro i
    fin_cases i <;> rfl
  tensor_spec := tensorMask221_spec
  first_bound := by
    intro i
    fin_cases i <;> decide
  second_bound := by
    intro i
    fin_cases i <;> decide
  third_bound := by
    intro i
    fin_cases i <;> decide
  tensor_bound := by
    intro i
    fin_cases i <;> decide

private def data411 : ProfileDecoderData profile411 where
  packed := packed411
  count_pos := by decide
  decoder := decode411
  bijective := decode411_bijective
  first_eq := rfl
  second_eq := rfl
  third_eq := rfl
  first_spec := by intro i; fin_cases i <;> rfl
  second_spec := by intro i; fin_cases i <;> rfl
  third_spec := by intro i; fin_cases i <;> rfl
  tensor_spec := tensorMask411_spec
  first_bound := by intro i; fin_cases i <;> decide
  second_bound := by intro i; fin_cases i <;> decide
  third_bound := by intro i; fin_cases i <;> decide
  tensor_bound := by intro i; fin_cases i <;> decide

private def data321 : ProfileDecoderData profile321 where
  packed := packed321
  count_pos := by decide
  decoder := decode321
  bijective := decode321_bijective
  first_eq := rfl
  second_eq := rfl
  third_eq := rfl
  first_spec := by intro i; fin_cases i <;> rfl
  second_spec := by intro i; fin_cases i <;> rfl
  third_spec := by intro i; fin_cases i <;> rfl
  tensor_spec := tensorMask321_spec
  first_bound := by intro i; fin_cases i <;> decide
  second_bound := by intro i; fin_cases i <;> decide
  third_bound := by intro i; fin_cases i <;> decide
  tensor_bound := by intro i; fin_cases i <;> decide

private def data222 : ProfileDecoderData profile222 where
  packed := packed222
  count_pos := by decide
  decoder := decode222
  bijective := decode222_bijective
  first_eq := rfl
  second_eq := rfl
  third_eq := rfl
  first_spec := by intro i; fin_cases i <;> rfl
  second_spec := by intro i; fin_cases i <;> rfl
  third_spec := by intro i; fin_cases i <;> rfl
  tensor_spec := tensorMask222_spec
  first_bound := by intro i; fin_cases i <;> decide
  second_bound := by intro i; fin_cases i <;> decide
  third_bound := by intro i; fin_cases i <;> decide
  tensor_bound := by intro i; fin_cases i <;> decide

example : data221.packed = packed221 := rfl
example : data411.packed = packed411 := rfl
example : data321.packed = packed321 := rfl
example : data222.packed = packed222 := rfl


private def ProfileDecoderData.decodeCode {p : Profile} (B : ProfileDecoderData p)
    (q : FiveCode) : State p :=
  decodeFiveCodeWith B.count_pos B.decoder q

private theorem ProfileDecoderData.decodeCode_eq_insert {p : Profile}
    (B : ProfileDecoderData p) (q : FiveCode) :
    B.decodeCode q =
      {decodeNat B.count_pos B.decoder q.a,
        decodeNat B.count_pos B.decoder q.b,
        decodeNat B.count_pos B.decoder q.c,
        decodeNat B.count_pos B.decoder q.d,
        decodeNat B.count_pos B.decoder q.e} := by
  simp only [ProfileDecoderData.decodeCode, decodeFiveCodeWith, FiveCode.toList,
    List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty]
  rfl

private theorem coe_image_insert_five_eq_range {α β : Type*} [DecidableEq α]
    [DecidableEq β] (f : α → β) (a b c d e : α) :
    (↑(({a, b, c, d, e} : Finset α).image f) : Set β) =
      Set.range ![f a, f b, f c, f d, f e] := by
  ext y
  constructor
  · intro hy
    simp only [Finset.coe_image, Set.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx' : x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e := by simpa using hx
    rcases hx' with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · change f a ∈ ↑(({a, b, c, d, e} : Finset α).image f)
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨a, by simp, rfl⟩)
    · change f b ∈ ↑(({a, b, c, d, e} : Finset α).image f)
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨b, by simp, rfl⟩)
    · change f c ∈ ↑(({a, b, c, d, e} : Finset α).image f)
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨c, by simp, rfl⟩)
    · change f d ∈ ↑(({a, b, c, d, e} : Finset α).image f)
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨d, by simp, rfl⟩)
    · change f e ∈ ↑(({a, b, c, d, e} : Finset α).image f)
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨e, by simp, rfl⟩)

private theorem ProfileDecoderData.first_spans5_iff {p : Profile}
    (B : ProfileDecoderData p) (q : FiveCode) (hq : q.Valid B.packed) :
    spans5 B.packed.first (termFactors B.packed q.a).1
        (termFactors B.packed q.b).1 (termFactors B.packed q.c).1
        (termFactors B.packed q.d).1 (termFactors B.packed q.e).1 = true ↔
      firstFactorSpan (B.decodeCode q) = ⊤ := by
  rcases hq with ⟨hab, hbc, hcd, hde, he⟩
  have ha : q.a < B.packed.termCount := by omega
  have hb : q.b < B.packed.termCount := by omega
  have hc : q.c < B.packed.termCount := by omega
  have hd : q.d < B.packed.termCount := by omega
  let ia : Fin B.packed.termCount := ⟨q.a, ha⟩
  let ib : Fin B.packed.termCount := ⟨q.b, hb⟩
  let ic : Fin B.packed.termCount := ⟨q.c, hc⟩
  let id : Fin B.packed.termCount := ⟨q.d, hd⟩
  let ie : Fin B.packed.termCount := ⟨q.e, he⟩
  have hda : decodeNat B.count_pos B.decoder q.a = B.decoder ia := by
    simp only [decodeNat, ha, ↓reduceDIte, ia]
  have hdb : decodeNat B.count_pos B.decoder q.b = B.decoder ib := by
    simp only [decodeNat, hb, ↓reduceDIte, ib]
  have hdc : decodeNat B.count_pos B.decoder q.c = B.decoder ic := by
    simp only [decodeNat, hc, ↓reduceDIte, ic]
  have hdd : decodeNat B.count_pos B.decoder q.d = B.decoder id := by
    simp only [decodeNat, hd, ↓reduceDIte, id]
  have hde' : decodeNat B.count_pos B.decoder q.e = B.decoder ie := by
    simp only [decodeNat, he, ↓reduceDIte, ie]
  have hstate : B.decodeCode q =
      {B.decoder ia, B.decoder ib, B.decoder ic, B.decoder id, B.decoder ie} := by
    rw [B.decodeCode_eq_insert, hda, hdb, hdc, hdd, hde']
  have hset :
      (↑((B.decodeCode q).image (fun t => t.1.1)) : Set (CoordinateVector p.first)) =
        Set.range (fiveMaskVectors p.first
          (termFactors B.packed q.a).1 (termFactors B.packed q.b).1
          (termFactors B.packed q.c).1 (termFactors B.packed q.d).1
          (termFactors B.packed q.e).1) := by
    rw [hstate]
    have hrange := coe_image_insert_five_eq_range (fun t : Carrier p => t.1.1)
      (B.decoder ia) (B.decoder ib) (B.decoder ic) (B.decoder id) (B.decoder ie)
    simpa only [B.first_spec, ia, ib, ic, id, ie, fiveMaskVectors] using hrange
  rw [B.first_eq]
  rw [spans5_eq_true_iff_span_eq_top (B.first_bound ia) (B.first_bound ib)
    (B.first_bound ic) (B.first_bound id) (B.first_bound ie)]
  rw [firstFactorSpan, hset]

private theorem ProfileDecoderData.second_spans5_iff {p : Profile}
    (B : ProfileDecoderData p) (q : FiveCode) (hq : q.Valid B.packed) :
    spans5 B.packed.second (termFactors B.packed q.a).2.1
        (termFactors B.packed q.b).2.1 (termFactors B.packed q.c).2.1
        (termFactors B.packed q.d).2.1 (termFactors B.packed q.e).2.1 = true ↔
      secondFactorSpan (B.decodeCode q) = ⊤ := by
  rcases hq with ⟨hab, hbc, hcd, hde, he⟩
  have ha : q.a < B.packed.termCount := by omega
  have hb : q.b < B.packed.termCount := by omega
  have hc : q.c < B.packed.termCount := by omega
  have hd : q.d < B.packed.termCount := by omega
  let ia : Fin B.packed.termCount := ⟨q.a, ha⟩
  let ib : Fin B.packed.termCount := ⟨q.b, hb⟩
  let ic : Fin B.packed.termCount := ⟨q.c, hc⟩
  let id : Fin B.packed.termCount := ⟨q.d, hd⟩
  let ie : Fin B.packed.termCount := ⟨q.e, he⟩
  have hda : decodeNat B.count_pos B.decoder q.a = B.decoder ia := by
    simp only [decodeNat, ha, ↓reduceDIte, ia]
  have hdb : decodeNat B.count_pos B.decoder q.b = B.decoder ib := by
    simp only [decodeNat, hb, ↓reduceDIte, ib]
  have hdc : decodeNat B.count_pos B.decoder q.c = B.decoder ic := by
    simp only [decodeNat, hc, ↓reduceDIte, ic]
  have hdd : decodeNat B.count_pos B.decoder q.d = B.decoder id := by
    simp only [decodeNat, hd, ↓reduceDIte, id]
  have hde' : decodeNat B.count_pos B.decoder q.e = B.decoder ie := by
    simp only [decodeNat, he, ↓reduceDIte, ie]
  have hstate : B.decodeCode q =
      {B.decoder ia, B.decoder ib, B.decoder ic, B.decoder id, B.decoder ie} := by
    rw [B.decodeCode_eq_insert, hda, hdb, hdc, hdd, hde']
  have hset :
      (↑((B.decodeCode q).image (fun t => t.2.1.1)) : Set (CoordinateVector p.second)) =
        Set.range (fiveMaskVectors p.second
          (termFactors B.packed q.a).2.1 (termFactors B.packed q.b).2.1
          (termFactors B.packed q.c).2.1 (termFactors B.packed q.d).2.1
          (termFactors B.packed q.e).2.1) := by
    rw [hstate]
    have hrange := coe_image_insert_five_eq_range (fun t : Carrier p => t.2.1.1)
      (B.decoder ia) (B.decoder ib) (B.decoder ic) (B.decoder id) (B.decoder ie)
    simpa only [B.second_spec, ia, ib, ic, id, ie, fiveMaskVectors] using hrange
  rw [B.second_eq]
  rw [spans5_eq_true_iff_span_eq_top (B.second_bound ia) (B.second_bound ib)
    (B.second_bound ic) (B.second_bound id) (B.second_bound ie)]
  rw [secondFactorSpan, hset]

private theorem ProfileDecoderData.third_spans5_iff {p : Profile}
    (B : ProfileDecoderData p) (q : FiveCode) (hq : q.Valid B.packed) :
    spans5 B.packed.third (termFactors B.packed q.a).2.2
        (termFactors B.packed q.b).2.2 (termFactors B.packed q.c).2.2
        (termFactors B.packed q.d).2.2 (termFactors B.packed q.e).2.2 = true ↔
      thirdFactorSpan (B.decodeCode q) = ⊤ := by
  rcases hq with ⟨hab, hbc, hcd, hde, he⟩
  have ha : q.a < B.packed.termCount := by omega
  have hb : q.b < B.packed.termCount := by omega
  have hc : q.c < B.packed.termCount := by omega
  have hd : q.d < B.packed.termCount := by omega
  let ia : Fin B.packed.termCount := ⟨q.a, ha⟩
  let ib : Fin B.packed.termCount := ⟨q.b, hb⟩
  let ic : Fin B.packed.termCount := ⟨q.c, hc⟩
  let id : Fin B.packed.termCount := ⟨q.d, hd⟩
  let ie : Fin B.packed.termCount := ⟨q.e, he⟩
  have hda : decodeNat B.count_pos B.decoder q.a = B.decoder ia := by
    simp only [decodeNat, ha, ↓reduceDIte, ia]
  have hdb : decodeNat B.count_pos B.decoder q.b = B.decoder ib := by
    simp only [decodeNat, hb, ↓reduceDIte, ib]
  have hdc : decodeNat B.count_pos B.decoder q.c = B.decoder ic := by
    simp only [decodeNat, hc, ↓reduceDIte, ic]
  have hdd : decodeNat B.count_pos B.decoder q.d = B.decoder id := by
    simp only [decodeNat, hd, ↓reduceDIte, id]
  have hde' : decodeNat B.count_pos B.decoder q.e = B.decoder ie := by
    simp only [decodeNat, he, ↓reduceDIte, ie]
  have hstate : B.decodeCode q =
      {B.decoder ia, B.decoder ib, B.decoder ic, B.decoder id, B.decoder ie} := by
    rw [B.decodeCode_eq_insert, hda, hdb, hdc, hdd, hde']
  have hset :
      (↑((B.decodeCode q).image (fun t => t.2.2.1)) : Set (CoordinateVector p.third)) =
        Set.range (fiveMaskVectors p.third
          (termFactors B.packed q.a).2.2 (termFactors B.packed q.b).2.2
          (termFactors B.packed q.c).2.2 (termFactors B.packed q.d).2.2
          (termFactors B.packed q.e).2.2) := by
    rw [hstate]
    have hrange := coe_image_insert_five_eq_range (fun t : Carrier p => t.2.2.1)
      (B.decoder ia) (B.decoder ib) (B.decoder ic) (B.decoder id) (B.decoder ie)
    simpa only [B.third_spec, ia, ib, ic, id, ie, fiveMaskVectors] using hrange
  rw [B.third_eq]
  rw [spans5_eq_true_iff_span_eq_top (B.third_bound ia) (B.third_bound ib)
    (B.third_bound ic) (B.third_bound id) (B.third_bound ie)]
  rw [thirdFactorSpan, hset]

private theorem ProfileDecoderData.tensor_check_iff {p : Profile}
    (B : ProfileDecoderData p) (q : FiveCode) (hq : q.Valid B.packed) :
    Nat.xor (B.packed.tensorMask q.a)
        (Nat.xor (B.packed.tensorMask q.b)
          (Nat.xor (B.packed.tensorMask q.c)
            (Nat.xor (B.packed.tensorMask q.d) (B.packed.tensorMask q.e)))) = 0 ↔
      stateEvaluation (B.decodeCode q) = 0 := by
  rcases hq with ⟨hab, hbc, hcd, hde, he⟩
  have ha : q.a < B.packed.termCount := by omega
  have hb : q.b < B.packed.termCount := by omega
  have hc : q.c < B.packed.termCount := by omega
  have hd : q.d < B.packed.termCount := by omega
  let ia : Fin B.packed.termCount := ⟨q.a, ha⟩
  let ib : Fin B.packed.termCount := ⟨q.b, hb⟩
  let ic : Fin B.packed.termCount := ⟨q.c, hc⟩
  let id : Fin B.packed.termCount := ⟨q.d, hd⟩
  let ie : Fin B.packed.termCount := ⟨q.e, he⟩
  have hda : decodeNat B.count_pos B.decoder q.a = B.decoder ia := by
    simp only [decodeNat, ha, ↓reduceDIte, ia]
  have hdb : decodeNat B.count_pos B.decoder q.b = B.decoder ib := by
    simp only [decodeNat, hb, ↓reduceDIte, ib]
  have hdc : decodeNat B.count_pos B.decoder q.c = B.decoder ic := by
    simp only [decodeNat, hc, ↓reduceDIte, ic]
  have hdd : decodeNat B.count_pos B.decoder q.d = B.decoder id := by
    simp only [decodeNat, hd, ↓reduceDIte, id]
  have hde' : decodeNat B.count_pos B.decoder q.e = B.decoder ie := by
    simp only [decodeNat, he, ↓reduceDIte, ie]
  have hstate : B.decodeCode q =
      {B.decoder ia, B.decoder ib, B.decoder ic, B.decoder id, B.decoder ie} := by
    rw [B.decodeCode_eq_insert, hda, hdb, hdc, hdd, hde']
  have hne (i j : Fin B.packed.termCount) (hval : i.val ≠ j.val) :
      B.decoder i ≠ B.decoder j := by
    intro hij
    exact hval (congrArg Fin.val (B.bijective.1 hij))
  have hab' : B.decoder ia ≠ B.decoder ib := hne ia ib (by simp only [ia, ib]; omega)
  have hac' : B.decoder ia ≠ B.decoder ic := hne ia ic (by simp only [ia, ic]; omega)
  have had' : B.decoder ia ≠ B.decoder id := hne ia id (by simp only [ia, id]; omega)
  have hae' : B.decoder ia ≠ B.decoder ie := hne ia ie (by simp only [ia, ie]; omega)
  have hbc' : B.decoder ib ≠ B.decoder ic := hne ib ic (by simp only [ib, ic]; omega)
  have hbd' : B.decoder ib ≠ B.decoder id := hne ib id (by simp only [ib, id]; omega)
  have hbe' : B.decoder ib ≠ B.decoder ie := hne ib ie (by simp only [ib, ie]; omega)
  have hcd' : B.decoder ic ≠ B.decoder id := hne ic id (by simp only [ic, id]; omega)
  have hce' : B.decoder ic ≠ B.decoder ie := hne ic ie (by simp only [ic, ie]; omega)
  have hde'' : B.decoder id ≠ B.decoder ie := hne id ie (by simp only [id, ie]; omega)
  have haNot : B.decoder ia ∉
      ({B.decoder ib, B.decoder ic, B.decoder id, B.decoder ie} : Finset (Carrier p)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hab', hac', had', hae'⟩
  have hbNot : B.decoder ib ∉
      ({B.decoder ic, B.decoder id, B.decoder ie} : Finset (Carrier p)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hbc', hbd', hbe'⟩
  have hcNot : B.decoder ic ∉
      ({B.decoder id, B.decoder ie} : Finset (Carrier p)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hcd', hce'⟩
  have hdNot : B.decoder id ∉ ({B.decoder ie} : Finset (Carrier p)) := by
    simpa only [Finset.mem_singleton] using hde''
  let ma := B.packed.tensorMask q.a
  let mb := B.packed.tensorMask q.b
  let mc := B.packed.tensorMask q.c
  let md := B.packed.tensorMask q.d
  let me := B.packed.tensorMask q.e
  let total := Nat.xor ma (Nat.xor mb (Nat.xor mc (Nat.xor md me)))
  have hevaluation : stateEvaluation (B.decodeCode q) = tensorOfMask p total := by
    calc
      stateEvaluation (B.decodeCode q) =
          tensorEvaluation (B.decoder ia) +
            (tensorEvaluation (B.decoder ib) +
              (tensorEvaluation (B.decoder ic) +
                (tensorEvaluation (B.decoder id) + tensorEvaluation (B.decoder ie)))) := by
        rw [hstate, stateEvaluation_eq_sum, Finset.sum_insert haNot,
          Finset.sum_insert hbNot, Finset.sum_insert hcNot,
          Finset.sum_insert hdNot, Finset.sum_singleton]
      _ = tensorOfMask p ma +
            (tensorOfMask p mb +
              (tensorOfMask p mc + (tensorOfMask p md + tensorOfMask p me))) := by
        rw [B.tensor_spec ia, B.tensor_spec ib, B.tensor_spec ic,
          B.tensor_spec id, B.tensor_spec ie]
      _ = tensorOfMask p total := by
        simp only [total, tensorOfMask_xor]
  have htotalBound : total < 2 ^ ((p.first * p.second) * p.third) := by
    have hselected := selectedXor5_lt_two_pow (selection := 31)
      (B.tensor_bound ia) (B.tensor_bound ib) (B.tensor_bound ic)
      (B.tensor_bound id) (B.tensor_bound ie)
    simp only [show (31 : Nat).testBit 0 = true by decide,
      show (31 : Nat).testBit 1 = true by decide,
      show (31 : Nat).testBit 2 = true by decide,
      show (31 : Nat).testBit 3 = true by decide,
      show (31 : Nat).testBit 4 = true by decide,
      if_true] at hselected
    simpa only [total, ma, mb, mc, md, me, ia, ib, ic, id, ie] using hselected
  change total = 0 ↔ stateEvaluation (B.decodeCode q) = 0
  rw [hevaluation, tensorOfMask_eq_zero_iff p htotalBound]

private theorem ProfileDecoderData.accepted_iff_isExactSupport {p : Profile}
    (B : ProfileDecoderData p) (q : FiveCode) (hq : q.Valid B.packed) :
    q.accepted B.packed = true ↔ IsExactSupport (B.decodeCode q) := by
  have hcard : (B.decodeCode q).card = 5 :=
    decodeFiveCodeWith_card B.count_pos B.decoder B.bijective.1 q hq
  simp only [FiveCode.accepted, accepts5, exactProfile5, Bool.and_eq_true, beq_iff_eq,
    B.tensor_check_iff q hq, B.first_spans5_iff q hq,
    B.second_spans5_iff q hq, B.third_spans5_iff q hq,
    IsExactSupport, HasExactFactorProfile, hcard, true_and]
  tauto

/-- Decode a compact 221 code to its canonical normalized support. -/
def decodeFiveCode221 (q : FiveCode) : State profile221 := data221.decodeCode q
/-- Decode a compact 411 code to its canonical normalized support. -/
def decodeFiveCode411 (q : FiveCode) : State profile411 := data411.decodeCode q
/-- Decode a compact 321 code to its canonical normalized support. -/
def decodeFiveCode321 (q : FiveCode) : State profile321 := data321.decodeCode q
/-- Decode a compact 222 code to its canonical normalized support. -/
def decodeFiveCode222 (q : FiveCode) : State profile222 := data222.decodeCode q

private theorem serializedTerm_decode221 (i : Fin packed221.termCount) :
    (serializedTermOfIndex packed221 i).decode? profile221 = some (decode221 i) := by
  fin_cases i <;> decide
private theorem serializedTerm_decode411 (i : Fin packed411.termCount) :
    (serializedTermOfIndex packed411 i).decode? profile411 = some (decode411 i) := by
  fin_cases i <;> decide
private theorem serializedTerm_decode321 (i : Fin packed321.termCount) :
    (serializedTermOfIndex packed321 i).decode? profile321 = some (decode321 i) := by
  fin_cases i <;> decide
private theorem serializedTerm_decode222 (i : Fin packed222.termCount) :
    (serializedTermOfIndex packed222 i).decode? profile222 = some (decode222 i) := by
  fin_cases i <;> decide

private theorem ProfileDecoderData.decodedSupport?_eq_some {p : Profile}
    (B : ProfileDecoderData p)
    (hserial : ∀ i : Fin B.packed.termCount,
      (serializedTermOfIndex B.packed i).decode? p = some (B.decoder i))
    (q : FiveCode) (hq : q.Valid B.packed) :
    decodedSupport? p B.packed q = some (B.decodeCode q) := by
  rcases hq with ⟨hab, hbc, hcd, hde, he⟩
  have ha : q.a < B.packed.termCount := by omega
  have hb : q.b < B.packed.termCount := by omega
  have hc : q.c < B.packed.termCount := by omega
  have hd : q.d < B.packed.termCount := by omega
  let ia : Fin B.packed.termCount := ⟨q.a, ha⟩
  let ib : Fin B.packed.termCount := ⟨q.b, hb⟩
  let ic : Fin B.packed.termCount := ⟨q.c, hc⟩
  let id : Fin B.packed.termCount := ⟨q.d, hd⟩
  let ie : Fin B.packed.termCount := ⟨q.e, he⟩
  have hsa := hserial ia
  have hsb := hserial ib
  have hsc := hserial ic
  have hsd := hserial id
  have hse := hserial ie
  rw [B.decodeCode_eq_insert]
  simp [decodedSupport?, serializedFiveTerms, SerializedEndpoints.decodeState?, hsa, hsb, hsc,
    hsd, hse, decodeNat, ha, hb, hc, hd, he, ia, ib, ic, id, ie]

/-- The canonical target-data decoder agrees with the 221 semantic decoder on valid codes. -/
theorem decodedSupport?_eq_some_decodeFiveCode221 (q : FiveCode) (hq : q.Valid packed221) :
    decodedSupport? profile221 packed221 q = some (decodeFiveCode221 q) := by
  exact data221.decodedSupport?_eq_some serializedTerm_decode221 q hq

/-- The canonical target-data decoder agrees with the 411 semantic decoder on valid codes. -/
theorem decodedSupport?_eq_some_decodeFiveCode411 (q : FiveCode) (hq : q.Valid packed411) :
    decodedSupport? profile411 packed411 q = some (decodeFiveCode411 q) := by
  exact data411.decodedSupport?_eq_some serializedTerm_decode411 q hq

/-- The canonical target-data decoder agrees with the 321 semantic decoder on valid codes. -/
theorem decodedSupport?_eq_some_decodeFiveCode321 (q : FiveCode) (hq : q.Valid packed321) :
    decodedSupport? profile321 packed321 q = some (decodeFiveCode321 q) := by
  exact data321.decodedSupport?_eq_some serializedTerm_decode321 q hq

/-- The canonical target-data decoder agrees with the 222 semantic decoder on valid codes. -/
theorem decodedSupport?_eq_some_decodeFiveCode222 (q : FiveCode) (hq : q.Valid packed222) :
    decodedSupport? profile222 packed222 q = some (decodeFiveCode222 q) := by
  exact data222.decodedSupport?_eq_some serializedTerm_decode222 q hq

private theorem ProfileDecoderData.aggregate_support_iff {p : Profile}
    (B : ProfileDecoderData p) (table : List FiveCode)
    (hcheck : exactTableCheck B.packed table = true)
    (hserial : ∀ q, q.Valid B.packed →
      decodedSupport? p B.packed q = some (B.decodeCode q)) (K : State p) :
    (∃ q ∈ table, decodedSupport? p B.packed q = some K) ↔ IsExactSupport K := by
  constructor
  · rintro ⟨q, hqTable, hdecode⟩
    have hchecked := (mem_iff_of_exactTableCheck B.packed table hcheck q).mp hqTable
    have hcanonical := hserial q hchecked.1
    have hsupport : B.decodeCode q = K := Option.some.inj (hcanonical.symm.trans hdecode)
    rw [← hsupport]
    exact (B.accepted_iff_isExactSupport q hchecked.1).mp hchecked.2
  · intro hK
    let equiv : Fin B.packed.termCount ≃ Carrier p := Equiv.ofBijective B.decoder B.bijective
    let s : Finset (Fin B.packed.termCount) := K.image equiv.symm
    have hsCard : s.card = 5 := by
      dsimp only [s]
      rw [Finset.card_image_of_injective K equiv.symm.injective, hK.1]
    let q := sortedFiveCode s hsCard
    have hvalid : q.Valid B.packed := sortedFiveCode_valid s hsCard
    have hdecode : B.decodeCode q = K := by
      rw [ProfileDecoderData.decodeCode]
      dsimp only [q]
      rw [decodeFiveCodeWith_sorted]
      change s.image equiv = K
      dsimp only [s]
      rw [Finset.image_image]
      ext x
      simp
    have haccepted : q.accepted B.packed = true :=
      (B.accepted_iff_isExactSupport q hvalid).mpr (hdecode ▸ hK)
    have hqTable := (mem_iff_of_exactTableCheck B.packed table hcheck q).mpr
      ⟨hvalid, haccepted⟩
    exact ⟨q, hqTable, (hserial q hvalid).trans (congrArg some hdecode)⟩

private theorem ProfileDecoderData.decodedFinset_eq_allExactSupports {p : Profile}
    [DecidableEq (State p)]
    (B : ProfileDecoderData p) (table : List FiveCode)
    (hcheck : exactTableCheck B.packed table = true)
    (hserial : ∀ q, q.Valid B.packed →
      decodedSupport? p B.packed q = some (B.decodeCode q)) :
    table.toFinset.image B.decodeCode = allExactSupports p := by
  ext K
  rw [mem_allExactSupports_iff]
  constructor
  · intro hK
    rcases Finset.mem_image.mp hK with ⟨q, hq, rfl⟩
    have hqTable : q ∈ table := by simpa only [List.mem_toFinset] using hq
    have hchecked := (mem_iff_of_exactTableCheck B.packed table hcheck q).mp hqTable
    exact (B.accepted_iff_isExactSupport q hchecked.1).mp hchecked.2
  · intro hK
    rcases (B.aggregate_support_iff table hcheck hserial K).mpr hK with
      ⟨q, hqTable, hqDecode⟩
    have hchecked := (mem_iff_of_exactTableCheck B.packed table hcheck q).mp hqTable
    have hcanonical := hserial q hchecked.1
    have hdecode : B.decodeCode q = K := Option.some.inj (hcanonical.symm.trans hqDecode)
    exact Finset.mem_image.mpr
      ⟨q, by simpa only [List.mem_toFinset] using hqTable, hdecode⟩

/-- The frozen 221 table decodes exactly the semantic exact supports. -/
theorem exactCodes221_decodedSupport_iff (K : State profile221) :
    (∃ q ∈ exactCodes221, decodedSupport? profile221 packed221 q = some K) ↔
      IsExactSupport K := by
  exact data221.aggregate_support_iff exactCodes221 exactTableCheckSmall.1
    (fun q hq => decodedSupport?_eq_some_decodeFiveCode221 q hq) K

/-- The frozen 411 table decodes exactly the semantic exact supports. -/
theorem exactCodes411_decodedSupport_iff (K : State profile411) :
    (∃ q ∈ exactCodes411, decodedSupport? profile411 packed411 q = some K) ↔
      IsExactSupport K := by
  exact data411.aggregate_support_iff exactCodes411 exactTableCheckSmall.2.1
    (fun q hq => decodedSupport?_eq_some_decodeFiveCode411 q hq) K

/-- The frozen 321 table decodes exactly the semantic exact supports. -/
theorem exactCodes321_decodedSupport_iff (K : State profile321) :
    (∃ q ∈ exactCodes321, decodedSupport? profile321 packed321 q = some K) ↔
      IsExactSupport K := by
  exact data321.aggregate_support_iff exactCodes321 exactTableCheckSmall.2.2
    (fun q hq => decodedSupport?_eq_some_decodeFiveCode321 q hq) K

/-- The frozen 222 table decodes exactly the semantic exact supports. -/
theorem exactCodes222_decodedSupport_iff (K : State profile222) :
    (∃ q ∈ exactCodes222, decodedSupport? profile222 packed222 q = some K) ↔
      IsExactSupport K := by
  exact data222.aggregate_support_iff exactCodes222 exactTableCheck222
    (fun q hq => decodedSupport?_eq_some_decodeFiveCode222 q hq) K

/-- The semantic supports obtained by decoding the frozen 221 compact-code table. -/
noncomputable def decodedExactSupports221 : Finset (State profile221) := by
  classical
  exact exactCodes221.toFinset.image decodeFiveCode221

/-- The semantic supports obtained by decoding the frozen 411 compact-code table. -/
noncomputable def decodedExactSupports411 : Finset (State profile411) := by
  classical
  exact exactCodes411.toFinset.image decodeFiveCode411

/-- The semantic supports obtained by decoding the frozen 321 compact-code table. -/
noncomputable def decodedExactSupports321 : Finset (State profile321) := by
  classical
  exact exactCodes321.toFinset.image decodeFiveCode321

/-- The semantic supports obtained by decoding the frozen 222 compact-code table. -/
noncomputable def decodedExactSupports222 : Finset (State profile222) := by
  classical
  exact exactCodes222.toFinset.image decodeFiveCode222

/-- Decoding the 221 compact-code table produces every and only exact support. -/
theorem decodedExactSupports221_eq_allExactSupports :
    decodedExactSupports221 = allExactSupports profile221 := by
  classical
  exact data221.decodedFinset_eq_allExactSupports exactCodes221 exactTableCheckSmall.1
    (fun q hq => decodedSupport?_eq_some_decodeFiveCode221 q hq)

/-- Decoding the 411 compact-code table produces every and only exact support. -/
theorem decodedExactSupports411_eq_allExactSupports :
    decodedExactSupports411 = allExactSupports profile411 := by
  classical
  exact data411.decodedFinset_eq_allExactSupports exactCodes411 exactTableCheckSmall.2.1
    (fun q hq => decodedSupport?_eq_some_decodeFiveCode411 q hq)

/-- Decoding the 321 compact-code table produces every and only exact support. -/
theorem decodedExactSupports321_eq_allExactSupports :
    decodedExactSupports321 = allExactSupports profile321 := by
  classical
  exact data321.decodedFinset_eq_allExactSupports exactCodes321 exactTableCheckSmall.2.2
    (fun q hq => decodedSupport?_eq_some_decodeFiveCode321 q hq)

/-- Decoding the 222 compact-code table produces every and only exact support. -/
theorem decodedExactSupports222_eq_allExactSupports :
    decodedExactSupports222 = allExactSupports profile222 := by
  classical
  exact data222.decodedFinset_eq_allExactSupports exactCodes222 exactTableCheck222
    (fun q hq => decodedSupport?_eq_some_decodeFiveCode222 q hq)

example : (⟨0, 1, 3, 4, 8⟩ : FiveCode).Valid packed221 := by decide
example : (⟨0, 1, 3, 7, 14⟩ : FiveCode).Valid packed411 := by decide
example : (⟨0, 1, 5, 11, 20⟩ : FiveCode).Valid packed321 := by decide
example : (⟨0, 1, 5, 17, 26⟩ : FiveCode).Valid packed222 := by decide

#check @exactCodes221_decodedSupport_iff
#check @exactCodes411_decodedSupport_iff
#check @exactCodes321_decodedSupport_iff
#check @exactCodes222_decodedSupport_iff
#print axioms exactCodes221_decodedSupport_iff
#print axioms exactCodes411_decodedSupport_iff
#print axioms exactCodes321_decodedSupport_iff
#print axioms exactCodes222_decodedSupport_iff
#print axioms decodedExactSupports221_eq_allExactSupports
#print axioms decodedExactSupports411_eq_allExactSupports
#print axioms decodedExactSupports321_eq_allExactSupports
#print axioms decodedExactSupports222_eq_allExactSupports

#check @decodeFiveCodeWith_card
#check @decodeFiveCodeWith_sorted
#print axioms decodeFiveCodeWith_card
#print axioms decodeFiveCodeWith_sorted

end BilinearComplexity.NormalizedBinaryCompactSemanticSupportBridge
