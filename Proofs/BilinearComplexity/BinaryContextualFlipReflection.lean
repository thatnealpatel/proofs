import BilinearComplexity.BinaryContextualExclusionSemantics
import BilinearComplexity.BinaryContextualExclusionEnumeration

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Native four-support Flip reflection

This module reflects a normalized native four-support all-mode move into the
raw finite third-Flip predicate. It transports the intrinsic Flip witness,
source occupancy, target freshness, and every ordering of the four support
terms through all six mode orientations.

AI disclosure: produced with AI assistance (see `Proofs/README`).
-/

namespace BilinearComplexity.BinaryContextualFlipReflection

open scoped symmDiff
open BinaryAmbientCarrier
open BinaryAmbientMoves
open BinaryAmbientMoveSupport
open NormalizedBinaryCarrier
open NormalizedBinaryModePermutation
open Scheme.Action
open BinaryContextualExclusionSemantics
open BinaryAmbientContextFiniteExclusion
open BinaryContextualExclusionEnumeration

private theorem nodup_four_of_card_eq_four {α : Type*} [DecidableEq α]
    (a b c d : α) (hcard : ({a, b, c, d} : Finset α).card = 4) :
    [a, b, c, d].Nodup := by
  rw [← Multiset.coe_nodup]
  apply Multiset.toFinset_card_eq_card_iff_nodup.mp
  simpa using hcard

private theorem inverseCode_encode_permuteTerm {p : Profile} (o : Orientation)
    (t : Carrier p) :
    inverseCode o (Raw.encodeTerm (permuteTerm o t)) = Raw.encodeTerm t := by
  cases o <;> rcases p with ⟨u, v, w⟩ <;>
    rcases t with ⟨t₁, t₂, t₃⟩ <;> rfl

private theorem permuteState_symmDiff_card {p : Profile} (o : Orientation)
    (D E : State p) :
    (permuteState o D ∆ permuteState o E).card = (D ∆ E).card := by
  simp only [permuteState]
  rw [← Finset.image_symmDiff D E (permuteTerm_injective o)]
  exact Finset.card_image_of_injective _ (permuteTerm_injective o)

private theorem orientedSourceThirdFlip_encode {p : Profile} (o : Orientation)
    {D₀ E₀ : State p} {sl sr tl tr : Carrier p}
    (hflip : SourceThirdFlip sl sr tl tr D₀ E₀)
    {D E : State (permProfile o p)}
    (hD : D = permuteState o D₀) (hE : E = permuteState o E₀)
    (hcard : (D ∆ E).card = 4)
    {a b c d : Carrier (permProfile o p)}
    (hset : D ∆ E = {a, b, c, d}) (hnodup : [a, b, c, d].Nodup)
    (occupied : TermCode → Bool)
    (hoccupied : ∀ t ∈ D ∆ E,
      occupied (Raw.encodeTerm t) = decide (t ∈ D)) :
    thirdFlip4 occupied (Raw.encodeTerm a) (Raw.encodeTerm b)
      (Raw.encodeTerm c) (Raw.encodeTerm d) = true := by
  let sl' := permuteTerm o sl
  let sr' := permuteTerm o sr
  let tl' := permuteTerm o tl
  let tr' := permuteTerm o tr
  have hwitnessABC := Raw.thirdFlipWitnessABC_encode hflip
  have hbaseSupport : D₀ ∆ E₀ = {sl, sr, tl, tr} :=
    SourceThirdFlip.symmDiff_eq hflip
  have hsupport : D ∆ E = {sl', sr', tl', tr'} := by
    rw [hD, hE]
    simp only [permuteState]
    rw [← Finset.image_symmDiff D₀ E₀ (permuteTerm_injective o), hbaseSupport]
    simp only [Finset.image_insert, Finset.image_singleton, sl', sr', tl', tr']
  have hbaseCard : ({sl, sr, tl, tr} : Finset (Carrier p)).card = 4 := by
    calc
      ({sl, sr, tl, tr} : Finset (Carrier p)).card =
          (Finset.image (permuteTerm o) {sl, sr, tl, tr}).card :=
        (Finset.card_image_of_injective _ (permuteTerm_injective o)).symm
      _ = ({sl', sr', tl', tr'} : Finset _).card := by
        simp only [Finset.image_insert, Finset.image_singleton, sl', sr', tl', tr']
      _ = (D ∆ E).card := congrArg Finset.card hsupport.symm
      _ = 4 := hcard
  have hbaseNodup : [sl, sr, tl, tr].Nodup :=
    nodup_four_of_card_eq_four sl sr tl tr hbaseCard
  have htlSl : tl ≠ sl := by
    intro heq
    subst tl
    simp at hbaseNodup
  have htlSr : tl ≠ sr := by
    intro heq
    subst tl
    simp at hbaseNodup
  have htrSl : tr ≠ sl := by
    intro heq
    subst tr
    simp at hbaseNodup
  have htrSr : tr ≠ sr := by
    intro heq
    subst tr
    simp at hbaseNodup
  rcases hflip with ⟨hslD₀, hsrD₀, hslSr, htlFresh, htrFresh,
    htlTr, hshared, htlFirst, htlSecond, htlThird, htrFirst,
    htrSecond, htrThird, htarget⟩
  have htlD₀ : tl ∉ D₀ := by
    intro htlD₀
    apply htlFresh
    exact Finset.mem_erase.mpr ⟨htlSr,
      Finset.mem_erase.mpr ⟨htlSl, htlD₀⟩⟩
  have htrD₀ : tr ∉ D₀ := by
    intro htrD₀
    apply htrFresh
    exact Finset.mem_erase.mpr ⟨htrSr,
      Finset.mem_erase.mpr ⟨htrSl, htrD₀⟩⟩
  have hslSupport : sl' ∈ D ∆ E := by rw [hsupport]; simp
  have hsrSupport : sr' ∈ D ∆ E := by rw [hsupport]; simp
  have htlSupport : tl' ∈ D ∆ E := by rw [hsupport]; simp
  have htrSupport : tr' ∈ D ∆ E := by rw [hsupport]; simp
  have hslD : sl' ∈ D := by
    rw [hD]
    simpa only [sl', permuteState_mem] using hslD₀
  have hsrD : sr' ∈ D := by
    rw [hD]
    simpa only [sr', permuteState_mem] using hsrD₀
  have htlD : tl' ∉ D := by
    rw [hD]
    simpa only [tl', permuteState_mem] using htlD₀
  have htrD : tr' ∉ D := by
    rw [hD]
    simpa only [tr', permuteState_mem] using htrD₀
  have hosl : occupied (Raw.encodeTerm sl') = true := by
    rw [hoccupied sl' hslSupport]
    simp [hslD]
  have hosr : occupied (Raw.encodeTerm sr') = true := by
    rw [hoccupied sr' hsrSupport]
    simp [hsrD]
  have hotl : occupied (Raw.encodeTerm tl') = false := by
    rw [hoccupied tl' htlSupport]
    simp [htlD]
  have hotr : occupied (Raw.encodeTerm tr') = false := by
    rw [hoccupied tr' htrSupport]
    simp [htrD]
  have hwitness : thirdFlipWitnessABC
      (inverseCode o (Raw.encodeTerm sl'))
      (inverseCode o (Raw.encodeTerm sr'))
      (inverseCode o (Raw.encodeTerm tl'))
      (inverseCode o (Raw.encodeTerm tr')) = true := by
    simpa only [sl', sr', tl', tr', inverseCode_encode_permuteTerm]
      using hwitnessABC
  have hpermNative : [sl', sr', tl', tr'].Perm [a, b, c, d] := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact nodup_four_of_card_eq_four sl' sr' tl' tr' (by
        rw [← hsupport, hcard])
    · exact hnodup
    · simpa using hsupport.symm.trans hset
  have hpermRaw :
      [Raw.encodeTerm sl', Raw.encodeTerm sr', Raw.encodeTerm tl',
        Raw.encodeTerm tr'].Perm
      [Raw.encodeTerm a, Raw.encodeTerm b, Raw.encodeTerm c,
        Raw.encodeTerm d] := hpermNative.map Raw.encodeTerm
  apply thirdFlip4_of_perm o occupied hwitness
  · simp [hosl, hosr, hotl, hotr]
  · exact hpermRaw

private theorem orientedMove_encode {p : Profile} (o : Orientation)
    {D₀ E₀ : State p} (hprimitive : Move D₀ E₀)
    {D E : State (permProfile o p)}
    (hD : D = permuteState o D₀) (hE : E = permuteState o E₀)
    (hcard : (D ∆ E).card = 4)
    {a b c d : Carrier (permProfile o p)}
    (hset : D ∆ E = {a, b, c, d}) (hnodup : [a, b, c, d].Nodup)
    (occupied : TermCode → Bool)
    (hoccupied : ∀ t ∈ D ∆ E,
      occupied (Raw.encodeTerm t) = decide (t ∈ D)) :
    thirdFlip4 occupied (Raw.encodeTerm a) (Raw.encodeTerm b)
      (Raw.encodeTerm c) (Raw.encodeTerm d) = true := by
  have hcard₀ : (D₀ ∆ E₀).card = 4 := by
    rw [hD, hE, permuteState_symmDiff_card o] at hcard
    exact hcard
  rcases BinaryAmbientMoveSupport.Move.support_four_factor_flip
      hprimitive hcard₀ with ⟨sl, sr, tl, tr, hflip, hsupport⟩
  exact orientedSourceThirdFlip_encode o hflip hD hE hcard
    hset hnodup occupied hoccupied

open NormalizedBinaryReplay221 in
example :
    let occupied : TermCode → Bool :=
      fun q => decide (q ∈ S1.image Raw.encodeTerm)
    AllModeMove S1 S2 ∧
      (S1 ∆ S2).card = 4 ∧
      S1 ∆ S2 = {E22, E31, E12, J} ∧
      [E22, E31, E12, J].Nodup ∧
      ∀ t ∈ S1 ∆ S2,
        occupied (Raw.encodeTerm t) = decide (t ∈ S1) := by
  dsimp only
  refine ⟨.abc (.sourceThirdFlip forwardFlip), ?_,
    SourceThirdFlip.symmDiff_eq forwardFlip, by decide, ?_⟩
  · rw [SourceThirdFlip.symmDiff_eq forwardFlip]
    decide
  · intro t ht
    simp only [Raw.encodeTerm_injective.mem_finset_image]

/-- A native four-support all-mode move is detected by the raw six-orientation
third-Flip checker in every duplicate-free ordering of its support, provided
the supplied raw occupancy agrees with membership in the native source state
on that support. -/
theorem allModeFlipCandidate_encode {p : Profile} {D E : State p}
    (hmove : AllModeMove D E) (hcard : (D ∆ E).card = 4)
    {a b c d : Carrier p} (hset : D ∆ E = {a, b, c, d})
    (hnodup : [a, b, c, d].Nodup) (occupied : TermCode → Bool)
    (hoccupied : ∀ t ∈ D ∆ E,
      occupied (Raw.encodeTerm t) = decide (t ∈ D)) :
    thirdFlip4 occupied (Raw.encodeTerm a) (Raw.encodeTerm b)
      (Raw.encodeTerm c) (Raw.encodeTerm d) = true := by
  rcases p with ⟨u, v, w⟩
  cases hmove with
  | abc hprimitive =>
      exact orientedMove_encode (p := ⟨u, v, w⟩) .abc hprimitive
        (permuteState_abc D).symm (permuteState_abc E).symm hcard
        hset hnodup occupied hoccupied
  | @bca D₀ E₀ D' E' hprimitive hD hE =>
      have hD' : D = permuteState (p := ⟨w, u, v⟩) .bca D₀ := by
        change D = Finset.image permuteBCATerm D₀
        exact hD
      have hE' : E = permuteState (p := ⟨w, u, v⟩) .bca E₀ := by
        change E = Finset.image permuteBCATerm E₀
        exact hE
      exact orientedMove_encode (p := ⟨w, u, v⟩) .bca hprimitive hD' hE'
        hcard hset hnodup occupied hoccupied
  | @cab D₀ E₀ D' E' hprimitive hD hE =>
      have hD' : D = permuteState (p := ⟨v, w, u⟩) .cab D₀ := by
        change D = Finset.image permuteCABTerm D₀
        exact hD
      have hE' : E = permuteState (p := ⟨v, w, u⟩) .cab E₀ := by
        change E = Finset.image permuteCABTerm E₀
        exact hE
      exact orientedMove_encode (p := ⟨v, w, u⟩) .cab hprimitive hD' hE'
        hcard hset hnodup occupied hoccupied
  | @acb D₀ E₀ D' E' hprimitive hD hE =>
      have hD' : D = permuteState (p := ⟨u, w, v⟩) .acb D₀ := by
        change D = Finset.image permuteACBTerm D₀
        exact hD
      have hE' : E = permuteState (p := ⟨u, w, v⟩) .acb E₀ := by
        change E = Finset.image permuteACBTerm E₀
        exact hE
      exact orientedMove_encode (p := ⟨u, w, v⟩) .acb hprimitive hD' hE'
        hcard hset hnodup occupied hoccupied
  | @cba D₀ E₀ D' E' hprimitive hD hE =>
      have hD' : D = permuteState (p := ⟨w, v, u⟩) .cba D₀ := by
        change D = Finset.image permuteCBATerm D₀
        exact hD
      have hE' : E = permuteState (p := ⟨w, v, u⟩) .cba E₀ := by
        change E = Finset.image permuteCBATerm E₀
        exact hE
      exact orientedMove_encode (p := ⟨w, v, u⟩) .cba hprimitive hD' hE'
        hcard hset hnodup occupied hoccupied
  | @bac D₀ E₀ D' E' hprimitive hD hE =>
      have hD' : D = permuteState (p := ⟨v, u, w⟩) .bac D₀ := by
        change D = Finset.image permuteBACTerm D₀
        exact hD
      have hE' : E = permuteState (p := ⟨v, u, w⟩) .bac E₀ := by
        change E = Finset.image permuteBACTerm E₀
        exact hE
      exact orientedMove_encode (p := ⟨v, u, w⟩) .bac hprimitive hD' hE'
        hcard hset hnodup occupied hoccupied

#check @allModeFlipCandidate_encode

#print axioms allModeFlipCandidate_encode

end BilinearComplexity.BinaryContextualFlipReflection
