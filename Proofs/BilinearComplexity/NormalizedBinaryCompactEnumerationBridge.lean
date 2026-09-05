import BilinearComplexity.NormalizedBinaryCompactEnumerationChecksSmall
import BilinearComplexity.NormalizedBinaryCompactEnumerationChecks222
import BilinearComplexity.NormalizedBinaryRelationEnumeration
import BilinearComplexity.NormalizedBinaryFiveCircuitRows
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 1000000

/-!
# Foundations for decoding compact normalized binary support tables

This module proves canonical carrier-index bijections, agreement of literal
tensor masks with tensor evaluation, soundness/completeness reflection for the
compact Boolean table checker, and sorted five-code encoding of five-element
index sets. Natural masks and codes are only a reflected representation.

The remaining acceptance-to-semantic-support bridge and decoded-table equality
with the independent support and relation enumerators are not proved here.
In particular, this module does not establish semantic orbit coverage or a
total normalized compiler.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.NormalizedBinaryCompactEnumeration

/-- List the five fields of a compact support code in their encoded order. -/
def FiveCode.toList (q : FiveCode) : List Nat := [q.a, q.b, q.c, q.d, q.e]

end BilinearComplexity.NormalizedBinaryCompactEnumeration

namespace BilinearComplexity.NormalizedBinaryCompactEnumerationBridge

open NormalizedBinaryCarrier
open NormalizedBinaryFiveCircuitRows
open NormalizedBinaryRelationEnumeration
open NormalizedBinaryCompactEnumeration

example : (FiveCode.mk 0 1 2 3 4).toList = [0, 1, 2, 3, 4] := rfl

/-- Decode a profile-221 mixed-radix index into the normalized carrier. -/
def decode221 (i : Fin 9) : Carrier profile221 :=
  let factors := termFactors packed221 i
  carrierOfMasks profile221 factors.1 factors.2.1 factors.2.2
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)

/-- Decode a profile-411 mixed-radix index into the normalized carrier. -/
def decode411 (i : Fin 15) : Carrier profile411 :=
  let factors := termFactors packed411 i
  carrierOfMasks profile411 factors.1 factors.2.1 factors.2.2
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)

/-- Decode a profile-321 mixed-radix index into the normalized carrier. -/
def decode321 (i : Fin 21) : Carrier profile321 :=
  let factors := termFactors packed321 i
  carrierOfMasks profile321 factors.1 factors.2.1 factors.2.2
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)

/-- Decode a profile-222 mixed-radix index into the normalized carrier. -/
def decode222 (i : Fin 27) : Carrier profile222 :=
  let factors := termFactors packed222 i
  carrierOfMasks profile222 factors.1 factors.2.1 factors.2.2
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)

example : (decode221 0).1.1 (0 : Fin 2) = 1 := by decide
example : (decode411 14).1.1 (3 : Fin 4) = 1 := by decide
example : (decode321 20).2.1.1 (1 : Fin 2) = 1 := by decide
example : (decode222 26).2.2.1 (1 : Fin 2) = 1 := by decide

/-- The profile-221 decoder lists every carrier term exactly once. -/
theorem decode221_bijective : Function.Bijective decode221 := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> decide
  · simpa only [Fintype.card_fin] using card_profile221.symm

/-- The profile-411 decoder lists every carrier term exactly once. -/
theorem decode411_bijective : Function.Bijective decode411 := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> decide
  · simpa only [Fintype.card_fin] using card_profile411.symm

/-- The profile-321 decoder lists every carrier term exactly once. -/
theorem decode321_bijective : Function.Bijective decode321 := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> decide
  · simpa only [Fintype.card_fin] using card_profile321.symm

/-- The profile-222 decoder lists every carrier term exactly once. -/
theorem decode222_bijective : Function.Bijective decode222 := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> decide
  · simpa only [Fintype.card_fin] using card_profile222.symm

/-- Decode a natural bit mask as a normalized tensor in little-endian
coordinate order. -/
def tensorOfMask (p : Profile) (mask : Nat) :
    Tensor F2 p.first p.second p.third :=
  fun i j k =>
    if mask.testBit ((i.val * p.second + j.val) * p.third + k.val) then 1 else 0

example : tensorOfMask profile222 1 (0 : Fin 2) (0 : Fin 2) (0 : Fin 2) = 1 := by decide
example : tensorOfMask profile222 1 (0 : Fin 2) (0 : Fin 2) (1 : Fin 2) = 0 := by decide

/-- The profile-221 literal tensor table agrees with semantic tensor evaluation. -/
theorem tensorMask221_spec (i : Fin 9) :
    tensorOfMask profile221 (packed221.tensorMask i) = tensorEvaluation (decode221 i) := by
  funext x y z
  fin_cases i <;> fin_cases x <;> fin_cases y <;> fin_cases z <;> decide

/-- The profile-411 literal tensor table agrees with semantic tensor evaluation. -/
theorem tensorMask411_spec (i : Fin 15) :
    tensorOfMask profile411 (packed411.tensorMask i) = tensorEvaluation (decode411 i) := by
  funext x y z
  fin_cases i <;> fin_cases x <;> fin_cases y <;> fin_cases z <;> decide

/-- The profile-321 literal tensor table agrees with semantic tensor evaluation. -/
theorem tensorMask321_spec (i : Fin 21) :
    tensorOfMask profile321 (packed321.tensorMask i) = tensorEvaluation (decode321 i) := by
  funext x y z
  fin_cases i <;> fin_cases x <;> fin_cases y <;> fin_cases z <;> decide

/-- The profile-222 literal tensor table agrees with semantic tensor evaluation. -/
theorem tensorMask222_spec (i : Fin 27) :
    tensorOfMask profile222 (packed222.tensorMask i) = tensorEvaluation (decode222 i) := by
  funext x y z
  fin_cases i <;> fin_cases x <;> fin_cases y <;> fin_cases z <;> decide

/-- Soundness reflection for a supplied compact support table. -/
theorem exactTableSound_eq_true_iff (p : PackedProfile) (table : List FiveCode) :
    exactTableSound p table = true ↔
      table.Nodup ∧ ∀ q ∈ table, q.Valid p ∧ q.accepted p = true := by
  simp only [exactTableSound, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true]

/-- Completeness reflection for a supplied compact support table. -/
theorem exactTableComplete_eq_true_iff (p : PackedProfile) (table : List FiveCode) :
    exactTableComplete p table = true ↔
      ∀ q, q.Valid p → q.accepted p = true → q ∈ table := by
  constructor
  · intro hcomplete q hvalid haccepted
    rcases hvalid with ⟨hab, hbc, hcd, hde, heN⟩
    have haN : q.a + 1 ≤ p.termCount := by omega
    have hbN : q.b + 1 ≤ p.termCount := by omega
    have hcN : q.c + 1 ≤ p.termCount := by omega
    have hdN : q.d + 1 ≤ p.termCount := by omega
    rw [exactTableComplete, allRange_eq_true_iff] at hcomplete
    have ha := hcomplete q.a (Nat.zero_le q.a) (by omega)
    rw [allRange_eq_true_iff] at ha
    have hb := ha q.b (by omega) (by rw [Nat.add_sub_of_le haN]; omega)
    rw [allRange_eq_true_iff] at hb
    have hc := hb q.c (by omega) (by rw [Nat.add_sub_of_le hbN]; omega)
    rw [allRange_eq_true_iff] at hc
    have hd := hc q.d (by omega) (by rw [Nat.add_sub_of_le hcN]; omega)
    rw [allRange_eq_true_iff] at hd
    have he := hd q.e (by omega) (by rw [Nat.add_sub_of_le hdN]; omega)
    simp only [FiveCode.accepted] at haccepted
    simp only [haccepted, Bool.not_true, Bool.false_or, List.contains_iff_mem] at he
    exact he
  · intro hall
    rw [exactTableComplete, allRange_eq_true_iff]
    intro a haLower haUpper
    rw [allRange_eq_true_iff]
    intro b hbLower hbUpper
    rw [allRange_eq_true_iff]
    intro c hcLower hcUpper
    rw [allRange_eq_true_iff]
    intro d hdLower hdUpper
    rw [allRange_eq_true_iff]
    intro e heLower heUpper
    have haN : a + 1 ≤ p.termCount := by omega
    have hbN : b + 1 ≤ p.termCount := by
      rw [Nat.add_sub_of_le haN] at hbUpper
      omega
    have hcN : c + 1 ≤ p.termCount := by
      rw [Nat.add_sub_of_le hbN] at hcUpper
      omega
    have hdN : d + 1 ≤ p.termCount := by
      rw [Nat.add_sub_of_le hcN] at hdUpper
      omega
    have heN : e < p.termCount := by
      rw [Nat.add_sub_of_le hdN] at heUpper
      exact heUpper
    by_cases haccepted : accepts5 p a b c d e = true
    · have hvalid : FiveCode.Valid p ⟨a, b, c, d, e⟩ := by
        change a < b ∧ b < c ∧ c < d ∧ d < e ∧ e < p.termCount
        exact ⟨by omega, by omega, by omega, by omega, heN⟩
      have hmem : (⟨a, b, c, d, e⟩ : FiveCode) ∈ table :=
        hall ⟨a, b, c, d, e⟩ hvalid haccepted
      simp only [haccepted, Bool.not_true, Bool.false_or, List.contains_iff_mem]
      exact hmem
    · have hacceptedFalse : accepts5 p a b c d e = false :=
        Bool.eq_false_of_not_eq_true haccepted
      simp only [hacceptedFalse, Bool.not_false, Bool.true_or]

/-- A fully checked table contains exactly the valid accepted five-codes. -/
theorem mem_iff_of_exactTableCheck (p : PackedProfile) (table : List FiveCode)
    (hcheck : exactTableCheck p table = true) (q : FiveCode) :
    q ∈ table ↔ q.Valid p ∧ q.accepted p = true := by
  have hparts : exactTableSound p table = true ∧ exactTableComplete p table = true := by
    simpa only [exactTableCheck, Bool.and_eq_true] using hcheck
  have hsound := (exactTableSound_eq_true_iff p table).mp hparts.1
  have hcomplete := (exactTableComplete_eq_true_iff p table).mp hparts.2
  constructor
  · exact hsound.2 q
  · intro hq
    exact hcomplete q hq.1 hq.2

/-- Encode a five-element finset of bounded natural indices in increasing order. -/
def sortedFiveCode {n : Nat} (s : Finset (Fin n)) (hcard : s.card = 5) : FiveCode :=
  let enum := s.orderEmbOfFin hcard
  ⟨enum 0, enum 1, enum 2, enum 3, enum 4⟩

/-- The sorted five-code fields are strictly increasing and bounded. -/
theorem sortedFiveCode_valid {n : Nat} (s : Finset (Fin n)) (hcard : s.card = 5) :
    let q := sortedFiveCode s hcard
    q.a < q.b ∧ q.b < q.c ∧ q.c < q.d ∧ q.d < q.e ∧ q.e < n := by
  dsimp only [sortedFiveCode]
  let enum := s.orderEmbOfFin hcard
  have hab : enum (0 : Fin 5) < enum (1 : Fin 5) := enum.strictMono (by decide)
  have hbc : enum (1 : Fin 5) < enum (2 : Fin 5) := enum.strictMono (by decide)
  have hcd : enum (2 : Fin 5) < enum (3 : Fin 5) := enum.strictMono (by decide)
  have hde : enum (3 : Fin 5) < enum (4 : Fin 5) := enum.strictMono (by decide)
  exact ⟨hab, hbc, hcd, hde, (enum (4 : Fin 5)).isLt⟩

/-- The fields of a sorted five-code are exactly the original index set. -/
theorem sortedFiveCode_toFinset {n : Nat} (s : Finset (Fin n)) (hcard : s.card = 5) :
    (sortedFiveCode s hcard).toList.toFinset = s.image Fin.val := by
  let enum := s.orderEmbOfFin hcard
  have henum : Finset.image enum Finset.univ = s :=
    Finset.image_orderEmbOfFin_univ s hcard
  calc
    (sortedFiveCode s hcard).toList.toFinset =
        Finset.image (fun i : Fin 5 => (enum i).val) Finset.univ := by
      ext x
      simp only [FiveCode.toList, sortedFiveCode, enum, List.mem_toFinset,
        List.mem_cons, List.mem_nil_iff, or_false, Finset.mem_image,
        Finset.mem_univ, true_and]
      constructor
      · intro hx
        rcases hx with hx | hx | hx | hx | hx
        · exact ⟨0, hx.symm⟩
        · exact ⟨1, hx.symm⟩
        · exact ⟨2, hx.symm⟩
        · exact ⟨3, hx.symm⟩
        · exact ⟨4, hx.symm⟩
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp
    _ = Finset.image Fin.val (Finset.image enum Finset.univ) := by
      rw [Finset.image_image]
      rfl
    _ = s.image Fin.val := by rw [henum]

example : (sortedFiveCode (Finset.univ : Finset (Fin 5)) (by decide)).toList.toFinset =
    {0, 1, 2, 3, 4} := by
  rw [sortedFiveCode_toFinset]
  decide

#check @decode221_bijective
#check @decode411_bijective
#check @decode321_bijective
#check @decode222_bijective
#check @tensorMask221_spec
#check @tensorMask411_spec
#check @tensorMask321_spec
#check @tensorMask222_spec
#check @mem_iff_of_exactTableCheck
#check @sortedFiveCode_valid
#check @sortedFiveCode_toFinset
#print axioms decode222_bijective
#print axioms tensorMask222_spec
#print axioms mem_iff_of_exactTableCheck
#print axioms sortedFiveCode_toFinset

end BilinearComplexity.NormalizedBinaryCompactEnumerationBridge
