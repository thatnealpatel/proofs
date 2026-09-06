import BilinearComplexity.BinaryContextualExclusionSemantics
import BilinearComplexity.BinaryContextualExclusionEnumeration
import BilinearComplexity.BinaryContextualFlipReflection

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace BilinearComplexity.BinaryContextualNativeExclusion

open scoped symmDiff
open BinaryCircuit BinaryAmbientCarrier BinaryAmbientMoves BinaryAmbientMoveSupport
open BinaryAmbientContextOptimality NormalizedBinaryCarrier NormalizedBinaryFiveCircuitRows
open Scheme.Action
open BinaryContextualExclusionSemantics BinaryContextualExclusionEnumeration
open BinaryAmbientContextFiniteExclusion BinaryContextualFlipReflection

private theorem localized_support_partition {α : Type*} [DecidableEq α]
    {P Q Z : Finset α} {t : α}
    (htZ : t ∉ Z) (hinter : P ∩ Q = {t})
    (hunion : P ∪ Q = insert t Z)
    (hPcard : P.card = 3) (hQcard : Q.card = 4) :
    t ∈ P ∧ t ∈ Q ∧
      (P.erase t).card = 2 ∧ (Q.erase t).card = 3 ∧
      Disjoint (P.erase t) (Q.erase t) ∧
      P.erase t ∪ Q.erase t = Z ∧
      Q.erase t = Z \ P.erase t := by
  have htInter : t ∈ P ∩ Q := by rw [hinter]; simp
  have htP : t ∈ P := (Finset.mem_inter.mp htInter).1
  have htQ : t ∈ Q := (Finset.mem_inter.mp htInter).2
  have hPcardErase : (P.erase t).card = 2 := by
    rw [Finset.card_erase_of_mem htP, hPcard]
  have hQcardErase : (Q.erase t).card = 3 := by
    rw [Finset.card_erase_of_mem htQ, hQcard]
  have hdisjoint : Disjoint (P.erase t) (Q.erase t) := by
    rw [Finset.disjoint_left]
    intro x hxP hxQ
    have hxInter : x ∈ P ∩ Q := Finset.mem_inter.mpr ⟨(Finset.mem_erase.mp hxP).2,
      (Finset.mem_erase.mp hxQ).2⟩
    rw [hinter] at hxInter
    exact (Finset.mem_erase.mp hxP).1 (Finset.mem_singleton.mp hxInter)
  have heraseUnion : P.erase t ∪ Q.erase t = Z := by
    ext x
    constructor
    · intro hx
      have hxne : x ≠ t := by
        rcases Finset.mem_union.mp hx with hxP | hxQ
        · exact (Finset.mem_erase.mp hxP).1
        · exact (Finset.mem_erase.mp hxQ).1
      have hxUnion : x ∈ P ∪ Q := by
        rcases Finset.mem_union.mp hx with hxP | hxQ
        · exact Finset.mem_union_left _ (Finset.mem_erase.mp hxP).2
        · exact Finset.mem_union_right _ (Finset.mem_erase.mp hxQ).2
      rw [hunion] at hxUnion
      exact (Finset.mem_insert.mp hxUnion).resolve_left hxne
    · intro hxZ
      have hxUnion : x ∈ P ∪ Q := by
        rw [hunion]
        exact Finset.mem_insert_of_mem hxZ
      rcases Finset.mem_union.mp hxUnion with hxP | hxQ
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun h => htZ (h ▸ hxZ), hxP⟩)
      · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨fun h => htZ (h ▸ hxZ), hxQ⟩)
  have hcomplement : Q.erase t = Z \ P.erase t := by
    ext x
    constructor
    · intro hxQ
      have hxUnion : x ∈ P.erase t ∪ Q.erase t := Finset.mem_union_right _ hxQ
      have hxZ : x ∈ Z := by rw [← heraseUnion]; exact hxUnion
      exact Finset.mem_sdiff.mpr ⟨hxZ, fun hxP => Finset.disjoint_left.mp hdisjoint hxP hxQ⟩
    · intro hx
      rcases Finset.mem_sdiff.mp hx with ⟨hxZ, hxnotP⟩
      have hxUnion : x ∈ P.erase t ∪ Q.erase t := by rw [heraseUnion]; exact hxZ
      exact (Finset.mem_union.mp hxUnion).resolve_left hxnotP
  exact ⟨htP, htQ, hPcardErase, hQcardErase, hdisjoint, heraseUnion, hcomplement⟩

private theorem list_contains_encodeTerm_eq_decide_mem {p : Profile}
    (L : List BinaryAmbientContextFiniteExclusion.TermCode)
    (S : State p) (himage : S.image Raw.encodeTerm = L.toFinset)
    (q : NormalizedBinaryCarrier.Carrier p) :
    L.contains (Raw.encodeTerm q) = decide (q ∈ S) := by
  rw [List.contains_eq_mem]
  apply decide_eq_decide.mpr
  rw [← List.mem_toFinset, ← himage]
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨x, hxS, hxeq⟩
    have hxq : x = q := Raw.encodeTerm_injective hxeq
    simpa only [hxq] using hxS
  · intro hqS
    exact ⟨q, hqS, rfl⟩

private theorem startOccupied_encodeTerm_eq_decide_mem {p : Profile}
    {A B C : State p} (Acode : List BinaryAmbientContextFiniteExclusion.TermCode)
    (hCA : Disjoint C A) (hCB : Disjoint C B)
    (hAimage : A.image Raw.encodeTerm = Acode.toFinset)
    {t q : NormalizedBinaryCarrier.Carrier p} (ht : t ∉ A ∪ B)
    (hq : q ∈ insert t (A ∪ B)) :
    ((decide (t ∈ C ∪ A) && Raw.encodeTerm q == Raw.encodeTerm t) ||
        Acode.contains (Raw.encodeTerm q)) = decide (q ∈ C ∪ A) := by
  have htA : t ∉ A := fun htA => ht (Finset.mem_union_left _ htA)
  by_cases hqt : q = t
  · subst q
    rw [list_contains_encodeTerm_eq_decide_mem Acode A hAimage]
    simp [htA]
  · have hqAB : q ∈ A ∪ B := (Finset.mem_insert.mp hq).resolve_left hqt
    have hqC : q ∉ C := by
      rcases Finset.mem_union.mp hqAB with hqA | hqB
      · exact fun hqCin => Finset.disjoint_left.mp hCA hqCin hqA
      · exact fun hqCin => Finset.disjoint_left.mp hCB hqCin hqB
    rw [list_contains_encodeTerm_eq_decide_mem Acode A hAimage]
    simp [hqt, Raw.encodeTerm_injective.eq_iff, hqC]

private theorem xor_decide_mem_support {α : Type*} [DecidableEq α]
    (X Y : Finset α) (q : α) :
    xor (decide (q ∈ X)) (decide (q ∈ X ∆ Y)) = decide (q ∈ Y) := by
  simp only [Finset.mem_symmDiff]
  by_cases hqX : q ∈ X <;> by_cases hqY : q ∈ Y <;> simp [hqX, hqY]

private theorem support3Contains_encodeTerm {p : Profile}
    (t x y q : NormalizedBinaryCarrier.Carrier p) :
    BinaryAmbientContextFiniteExclusion.support3Contains
      (Raw.encodeTerm t) (Raw.encodeTerm x) (Raw.encodeTerm y) (Raw.encodeTerm q) =
        decide (q ∈ ({t, x, y} : Finset _)) := by
  apply Bool.eq_iff_iff.mpr
  simp [BinaryAmbientContextFiniteExclusion.support3Contains,
    Raw.encodeTerm_injective.eq_iff]
  tauto

private theorem support4Contains_encodeTerm {p : Profile}
    (t u v w q : NormalizedBinaryCarrier.Carrier p) :
    (Raw.encodeTerm q == Raw.encodeTerm t || Raw.encodeTerm q == Raw.encodeTerm u ||
      Raw.encodeTerm q == Raw.encodeTerm v || Raw.encodeTerm q == Raw.encodeTerm w) =
        decide (q ∈ ({t, u, v, w} : Finset _)) := by
  apply Bool.eq_iff_iff.mpr
  simp [Raw.encodeTerm_injective.eq_iff]
  tauto

private theorem move_line_source_inter_card {p : Profile} {D E : State p}
    (hmove : Move D E) (hcard : (D ∆ E).card = 3) :
    (D ∩ (D ∆ E)).card = 1 ∨ (D ∩ (D ∆ E)).card = 2 := by
  rcases Move.support_three_factor_line hmove hcard with
    ⟨s, l, r, hsplit, hsupport⟩ | ⟨l, r, t, hreduction, hsupport⟩
  · left
    have htriple : ({s, l, r} : Finset _).card = 3 := by rw [← hsupport]; exact hcard
    have hsl : s ≠ l := by
      intro h
      subst l
      have hle : ({s, r} : Finset _).card ≤ 2 := Finset.card_le_two
      have hcontra : ({s, r} : Finset _).card = 3 := by simpa using htriple
      rw [hcontra] at hle
      omega
    have hsr : s ≠ r := by
      intro h
      subst r
      have hle : ({s, l} : Finset _).card ≤ 2 := Finset.card_le_two
      have hcontra : ({s, l} : Finset _).card = 3 := by
        simpa [Finset.pair_comm] using htriple
      rw [hcontra] at hle
      omega
    rcases hsplit with ⟨hsD, hlr, hlFresh, hrFresh, hsum, hl2, hr2, hl3, hr3, hE⟩
    have hlD : l ∉ D := fun hlD => hlFresh (Finset.mem_erase.mpr ⟨hsl.symm, hlD⟩)
    have hrD : r ∉ D := fun hrD => hrFresh (Finset.mem_erase.mpr ⟨hsr.symm, hrD⟩)
    rw [hsupport]
    simp [hsD, hlD, hrD]
  · right
    have htriple : ({l, r, t} : Finset _).card = 3 := by rw [← hsupport]; exact hcard
    have htl : t ≠ l := by
      intro h
      subst t
      have hle : ({l, r} : Finset _).card ≤ 2 := Finset.card_le_two
      have hcontra : ({l, r} : Finset _).card = 3 := by
        simpa [Finset.pair_comm] using htriple
      rw [hcontra] at hle
      omega
    have htr : t ≠ r := by
      intro h
      subst t
      have hle : ({l, r} : Finset _).card ≤ 2 := Finset.card_le_two
      have hcontra : ({l, r} : Finset _).card = 3 := by
        simpa [Finset.pair_comm] using htriple
      rw [hcontra] at hle
      omega
    rcases hreduction with ⟨hlD, hrD, hlr, htFresh, hr2, hr3, hsum, ht2, ht3, hE⟩
    have htD : t ∉ D := fun htD => htFresh
      (Finset.mem_erase.mpr ⟨htr, Finset.mem_erase.mpr ⟨htl, htD⟩⟩)
    rw [hsupport]
    simp [hlD, hrD, htD, hlr]

private theorem source_inter_support_card_image
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (D E : Finset α) :
    (D.image f ∩ (D.image f ∆ E.image f)).card = (D ∩ (D ∆ E)).card := by
  rw [← Finset.image_symmDiff D E hf, ← Finset.image_inter D (D ∆ E) hf]
  exact Finset.card_image_of_injective _ hf

private theorem support_card_image
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (D E : Finset α) :
    (D.image f ∆ E.image f).card = (D ∆ E).card := by
  rw [← Finset.image_symmDiff D E hf]
  exact Finset.card_image_of_injective _ hf

private theorem allModeMove_line_source_inter_card {p : Profile} {D E : State p}
    (hmove : AllModeMove D E) (hcard : (D ∆ E).card = 3) :
    (D ∩ (D ∆ E)).card = 1 ∨ (D ∩ (D ∆ E)).card = 2 := by
  cases hmove with
  | abc h => exact move_line_source_inter_card h hcard
  | bca h hD hE =>
      subst D; subst E
      simp only [permuteBCAState]
      rw [source_inter_support_card_image permuteBCATerm permuteBCATerm_injective]
      apply move_line_source_inter_card (p := ⟨p.third, p.first, p.second⟩) h
      simp only [permuteBCAState] at hcard
      rw [support_card_image permuteBCATerm permuteBCATerm_injective] at hcard
      exact hcard
  | cab h hD hE =>
      subst D; subst E
      simp only [permuteCABState]
      rw [source_inter_support_card_image permuteCABTerm permuteCABTerm_injective]
      apply move_line_source_inter_card (p := ⟨p.second, p.third, p.first⟩) h
      simp only [permuteCABState] at hcard
      rw [support_card_image permuteCABTerm permuteCABTerm_injective] at hcard
      exact hcard
  | acb h hD hE =>
      subst D; subst E
      simp only [permuteACBState]
      rw [source_inter_support_card_image permuteACBTerm permuteACBTerm_injective]
      apply move_line_source_inter_card (p := ⟨p.first, p.third, p.second⟩) h
      simp only [permuteACBState] at hcard
      rw [support_card_image permuteACBTerm permuteACBTerm_injective] at hcard
      exact hcard
  | cba h hD hE =>
      subst D; subst E
      simp only [permuteCBAState]
      rw [source_inter_support_card_image permuteCBATerm permuteCBATerm_injective]
      apply move_line_source_inter_card (p := ⟨p.third, p.second, p.first⟩) h
      simp only [permuteCBAState] at hcard
      rw [support_card_image permuteCBATerm permuteCBATerm_injective] at hcard
      exact hcard
  | bac h hD hE =>
      subst D; subst E
      simp only [permuteBACState]
      rw [source_inter_support_card_image permuteBACTerm permuteBACTerm_injective]
      apply move_line_source_inter_card (p := ⟨p.second, p.first, p.third⟩) h
      simp only [permuteBACState] at hcard
      rw [support_card_image permuteBACTerm permuteBACTerm_injective] at hcard
      exact hcard

private theorem allModeLineOccupancy_encode {p : Profile} {D E : State p}
    (hmove : AllModeMove D E) {t x y : Carrier p}
    (htx : t ≠ x) (hty : t ≠ y) (hxy : x ≠ y)
    (hsupport : D ∆ E = {t, x, y})
    (occupied : BinaryAmbientContextFiniteExclusion.TermCode → Bool)
    (hoccupied : ∀ q ∈ ({t, x, y} : Finset (Carrier p)),
      occupied (Raw.encodeTerm q) = decide (q ∈ D)) :
    BinaryAmbientContextFiniteExclusion.lineOccupancy occupied (Raw.encodeTerm t)
      (Raw.encodeTerm x) (Raw.encodeTerm y) = true := by
  have hcard : (D ∆ E).card = 3 := by
    rw [hsupport]
    exact Finset.card_eq_three.mpr ⟨t, x, y, htx, hty, hxy, rfl⟩
  have hsource := allModeMove_line_source_inter_card hmove hcard
  rw [hsupport] at hsource
  have hot := hoccupied t (by simp)
  have hox := hoccupied x (by simp)
  have hoy := hoccupied y (by simp)
  unfold BinaryAmbientContextFiniteExclusion.lineOccupancy
  rw [hot, hox, hoy]
  by_cases ht : t ∈ D
  · by_cases hx : x ∈ D
    · by_cases hy : y ∈ D
      · exfalso
        rcases hsource with hsource | hsource <;>
          simp [ht, hx, hy, htx, hty, hxy] at hsource
      · simp [ht, hx, hy]
    · by_cases hy : y ∈ D <;> simp [ht, hx, hy]
  · by_cases hx : x ∈ D
    · by_cases hy : y ∈ D <;> simp [ht, hx, hy]
    · by_cases hy : y ∈ D
      · simp [ht, hx, hy]
      · exfalso
        rcases hsource with hsource | hsource <;>
          simp [ht, hx, hy] at hsource

private theorem exists_encoded_support_split {p : Profile}
    {P Q Z : Finset (Carrier p)} {t : Carrier p} {Zcode : List TermCode}
    (htZ : t ∉ Z) (hinter : P ∩ Q = {t})
    (hunion : P ∪ Q = insert t Z)
    (hPcard : P.card = 3) (hQcard : Q.card = 4)
    (hZencode : Z.image Raw.encodeTerm = Zcode.toFinset)
    (hZlength : Zcode.length = 5) (hZnodup : Zcode.Nodup) :
    ∃ x y u v w : Carrier p,
      ((Raw.encodeTerm x, Raw.encodeTerm y),
          (Raw.encodeTerm u, Raw.encodeTerm v, Raw.encodeTerm w)) ∈ splits5 Zcode ∧
      P = {t, x, y} ∧ Q = {t, u, v, w} ∧
      [t, x, y].Nodup ∧ [t, u, v, w].Nodup := by
  obtain ⟨htP, htQ, hPcardErase, hQcardErase, hdisjoint,
      hunionErase, hQdiff⟩ :=
    localized_support_partition htZ hinter hunion hPcard hQcard
  let S := (P.erase t).image Raw.encodeTerm
  have hScard : S.card = 2 := by
    dsimp only [S]
    rw [Finset.card_image_of_injective _ Raw.encodeTerm_injective, hPcardErase]
  have hSsubset : S ⊆ Zcode.toFinset := by
    rw [← hZencode]
    dsimp only [S]
    apply Finset.image_mono
    intro q hq
    rw [← hunionErase]
    exact Finset.mem_union_left _ hq
  obtain ⟨xc, yc, uc, vc, wc, hsplit, hpair, htriple, hperm, hfiveNodup⟩ :=
    exists_mem_splits5_of_card_eq_two Zcode hZlength hZnodup S hScard hSsubset
  have hQcode : ({uc, vc, wc} : Finset TermCode) =
      (Q.erase t).image Raw.encodeTerm := by
    calc
      ({uc, vc, wc} : Finset TermCode) = Zcode.toFinset \ S := htriple
      _ = Z.image Raw.encodeTerm \ (P.erase t).image Raw.encodeTerm := by
        rw [hZencode]
      _ = (Z \ P.erase t).image Raw.encodeTerm := by
        rw [Finset.image_sdiff Z (P.erase t) Raw.encodeTerm_injective]
      _ = (Q.erase t).image Raw.encodeTerm := by rw [hQdiff]
  have hxc : xc ∈ S := by rw [← hpair]; simp
  have hyc : yc ∈ S := by rw [← hpair]; simp
  have huc : uc ∈ (Q.erase t).image Raw.encodeTerm := by rw [← hQcode]; simp
  have hvc : vc ∈ (Q.erase t).image Raw.encodeTerm := by rw [← hQcode]; simp
  have hwc : wc ∈ (Q.erase t).image Raw.encodeTerm := by rw [← hQcode]; simp
  rcases Finset.mem_image.mp hxc with ⟨x, hxP, hxc⟩
  rcases Finset.mem_image.mp hyc with ⟨y, hyP, hyc⟩
  rcases Finset.mem_image.mp huc with ⟨u, huQ, huc⟩
  rcases Finset.mem_image.mp hvc with ⟨v, hvQ, hvc⟩
  rcases Finset.mem_image.mp hwc with ⟨w, hwQ, hwc⟩
  subst xc
  subst yc
  subst uc
  subst vc
  subst wc
  have hpairNative : ({x, y} : Finset (Carrier p)) = P.erase t := by
    apply Finset.image_injective Raw.encodeTerm_injective
    simpa only [Finset.image_insert, Finset.image_singleton] using hpair
  have htripleNative : ({u, v, w} : Finset (Carrier p)) = Q.erase t := by
    apply Finset.image_injective Raw.encodeTerm_injective
    simpa only [Finset.image_insert, Finset.image_singleton] using hQcode
  have hPset : P = {t, x, y} := by
    rw [← Finset.insert_erase htP, ← hpairNative]
  have hQset : Q = {t, u, v, w} := by
    rw [← Finset.insert_erase htQ, ← htripleNative]
  have hlineNodup : [t, x, y].Nodup := by
    rw [← Multiset.coe_nodup]
    apply Multiset.toFinset_card_eq_card_iff_nodup.mp
    simpa [← hPset] using hPcard
  have hflipNodup : [t, u, v, w].Nodup := by
    rw [← Multiset.coe_nodup]
    apply Multiset.toFinset_card_eq_card_iff_nodup.mp
    simpa [← hQset] using hQcard
  exact ⟨x, y, u, v, w, hsplit, hPset, hQset,
    hlineNodup, hflipNodup⟩

private theorem encoded_endpoint_list_data {p : Profile}
    {A B : Finset (Carrier p)} {Acode Bcode : List TermCode}
    (hAB : Disjoint A B)
    (hAencode : A.image Raw.encodeTerm = Acode.toFinset)
    (hBencode : B.image Raw.encodeTerm = Bcode.toFinset)
    (hAlength : Acode.length = 2) (hBlength : Bcode.length = 3)
    (hAnodup : Acode.Nodup) (hBnodup : Bcode.Nodup) :
    (Acode ++ Bcode).length = 5 ∧ (Acode ++ Bcode).Nodup ∧
      (A ∪ B).image Raw.encodeTerm = (Acode ++ Bcode).toFinset := by
  have hcodeDisjoint : Disjoint Acode.toFinset Bcode.toFinset := by
    rw [← hAencode, ← hBencode]
    exact (Finset.disjoint_image Raw.encodeTerm_injective).mpr hAB
  have hcross : ∀ a ∈ Acode, ∀ b ∈ Bcode, a ≠ b := by
    intro a ha b hb hab
    subst b
    exact (Finset.disjoint_left.mp hcodeDisjoint)
      (List.mem_toFinset.mpr ha) (List.mem_toFinset.mpr hb)
  refine ⟨by simp only [List.length_append, hAlength, hBlength],
    List.nodup_append.mpr ⟨hAnodup, hBnodup, hcross⟩, ?_⟩
  rw [List.toFinset_append, ← hAencode, ← hBencode,
    Finset.image_union]

private theorem checker_of_line_then_flip {p : Profile}
    {C A B D : State p} {Acode Bcode : List TermCode}
    (hCA : Disjoint C A) (hCB : Disjoint C B)
    (hline : AllModeMove (C ∪ A) D) (hflip : AllModeMove D (C ∪ B))
    {t : Carrier p} (htZ : t ∉ A ∪ B)
    (hsupportInter : ((C ∪ A) ∆ D) ∩ (D ∆ (C ∪ B)) = {t})
    (hsupportUnion : ((C ∪ A) ∆ D) ∪ (D ∆ (C ∪ B)) =
      insert t (A ∪ B))
    (hlineCard : ((C ∪ A) ∆ D).card = 3)
    (hflipCard : (D ∆ (C ∪ B)).card = 4)
    (hAencode : A.image Raw.encodeTerm = Acode.toFinset)
    (hZencode : (A ∪ B).image Raw.encodeTerm = (Acode ++ Bcode).toFinset)
    (hZlength : (Acode ++ Bcode).length = 5)
    (hZnodup : (Acode ++ Bcode).Nodup) :
    hasContextualTwoEdgePath Acode Bcode = true := by
  obtain ⟨x, y, u, v, w, hsplit, hPset, hQset,
      hlineNodup, hflipNodup⟩ :=
    exists_encoded_support_split htZ hsupportInter hsupportUnion
      hlineCard hflipCard hZencode hZlength hZnodup
  have hdistinct : (t ≠ x ∧ t ≠ y) ∧ x ≠ y := by
    simpa using hlineNodup
  rcases hdistinct with ⟨⟨htx, hty⟩, hxy⟩
  have hlineSet : (C ∪ A) ∆ D = {x, y, t} := by
    rw [hPset]
    ext q
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  obtain ⟨o, ho, hcandidate⟩ := allModeLineCandidate_encode hline hlineCard
    hlineSet hxy htx.symm hty.symm
  let startOccupied : TermCode → Bool := fun q =>
    (decide (t ∈ C ∪ A) && q == Raw.encodeTerm t) || Acode.contains q
  have hstart (q : Carrier p) (hq : q ∈ insert t (A ∪ B)) :
      startOccupied (Raw.encodeTerm q) = decide (q ∈ C ∪ A) := by
    exact startOccupied_encodeTerm_eq_decide_mem Acode hCA hCB hAencode htZ hq
  have hlineOccupancy : lineOccupancy startOccupied (Raw.encodeTerm t)
      (Raw.encodeTerm x) (Raw.encodeTerm y) = true := by
    apply allModeLineOccupancy_encode hline htx hty hxy hPset startOccupied
    intro q hq
    apply hstart q
    rw [← hPset] at hq
    rw [← hsupportUnion]
    exact Finset.mem_union_left _ hq
  let afterLine : TermCode → Bool := fun q =>
    xor (startOccupied q)
      (support3Contains (Raw.encodeTerm t) (Raw.encodeTerm x) (Raw.encodeTerm y) q)
  have hafterLine (q : Carrier p) (hq : q ∈ D ∆ (C ∪ B)) :
      afterLine (Raw.encodeTerm q) = decide (q ∈ D) := by
    have hqUnion : q ∈ insert t (A ∪ B) := by
      rw [← hsupportUnion]
      exact Finset.mem_union_right _ hq
    dsimp only [afterLine]
    rw [hstart q hqUnion, support3Contains_encodeTerm t x y q, ← hPset]
    exact xor_decide_mem_support (C ∪ A) D q
  have hflipCandidate : thirdFlip4 afterLine (Raw.encodeTerm t)
      (Raw.encodeTerm u) (Raw.encodeTerm v) (Raw.encodeTerm w) = true := by
    exact allModeFlipCandidate_encode hflip hflipCard hQset hflipNodup
      afterLine hafterLine
  have htContains : (Acode ++ Bcode).contains (Raw.encodeTerm t) = false := by
    rw [list_contains_encodeTerm_eq_decide_mem (Acode ++ Bcode) (A ∪ B) hZencode]
    simp [htZ]
  unfold hasContextualTwoEdgePath
  apply List.any_eq_true.mpr
  refine ⟨((Raw.encodeTerm x, Raw.encodeTerm y),
    (Raw.encodeTerm u, Raw.encodeTerm v, Raw.encodeTerm w)), hsplit, ?_⟩
  dsimp only
  apply List.any_eq_true.mpr
  refine ⟨o, ho, ?_⟩
  rw [hcandidate]
  simp only
  unfold checkCandidate
  rw [htContains]
  simp only [Bool.not_false, Bool.true_and]
  apply List.any_eq_true.mpr
  refine ⟨decide (t ∈ C ∪ A), by cases decide (t ∈ C ∪ A) <;> simp, ?_⟩
  change ((lineOccupancy startOccupied (Raw.encodeTerm t)
    (Raw.encodeTerm x) (Raw.encodeTerm y) &&
    thirdFlip4 afterLine (Raw.encodeTerm t) (Raw.encodeTerm u)
      (Raw.encodeTerm v) (Raw.encodeTerm w)) || _) = true
  rw [hlineOccupancy, hflipCandidate]
  simp only [Bool.true_and, Bool.true_or]

private theorem checker_of_flip_then_line {p : Profile}
    {C A B D : State p} {Acode Bcode : List TermCode}
    (hCA : Disjoint C A) (hCB : Disjoint C B)
    (hflip : AllModeMove (C ∪ A) D) (hline : AllModeMove D (C ∪ B))
    {t : Carrier p} (htZ : t ∉ A ∪ B)
    (hsupportInter : ((C ∪ A) ∆ D) ∩ (D ∆ (C ∪ B)) = {t})
    (hsupportUnion : ((C ∪ A) ∆ D) ∪ (D ∆ (C ∪ B)) =
      insert t (A ∪ B))
    (hflipCard : ((C ∪ A) ∆ D).card = 4)
    (hlineCard : (D ∆ (C ∪ B)).card = 3)
    (hAencode : A.image Raw.encodeTerm = Acode.toFinset)
    (hZencode : (A ∪ B).image Raw.encodeTerm = (Acode ++ Bcode).toFinset)
    (hZlength : (Acode ++ Bcode).length = 5)
    (hZnodup : (Acode ++ Bcode).Nodup) :
    hasContextualTwoEdgePath Acode Bcode = true := by
  have hsupportInter' : (D ∆ (C ∪ B)) ∩ ((C ∪ A) ∆ D) = {t} := by
    rw [Finset.inter_comm]
    exact hsupportInter
  have hsupportUnion' : (D ∆ (C ∪ B)) ∪ ((C ∪ A) ∆ D) =
      insert t (A ∪ B) := by
    rw [Finset.union_comm]
    exact hsupportUnion
  obtain ⟨x, y, u, v, w, hsplit, hLineSet, hFlipSet,
      hlineNodup, hflipNodup⟩ :=
    exists_encoded_support_split htZ hsupportInter' hsupportUnion'
      hlineCard hflipCard hZencode hZlength hZnodup
  have hdistinct : (t ≠ x ∧ t ≠ y) ∧ x ≠ y := by
    simpa using hlineNodup
  rcases hdistinct with ⟨⟨htx, hty⟩, hxy⟩
  have hlineSet' : D ∆ (C ∪ B) = {x, y, t} := by
    rw [hLineSet]
    ext q
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  obtain ⟨o, ho, hcandidate⟩ := allModeLineCandidate_encode hline hlineCard
    hlineSet' hxy htx.symm hty.symm
  let startOccupied : TermCode → Bool := fun q =>
    (decide (t ∈ C ∪ A) && q == Raw.encodeTerm t) || Acode.contains q
  have hstart (q : Carrier p) (hq : q ∈ insert t (A ∪ B)) :
      startOccupied (Raw.encodeTerm q) = decide (q ∈ C ∪ A) := by
    exact startOccupied_encodeTerm_eq_decide_mem Acode hCA hCB hAencode htZ hq
  have hflipCandidate : thirdFlip4 startOccupied (Raw.encodeTerm t)
      (Raw.encodeTerm u) (Raw.encodeTerm v) (Raw.encodeTerm w) = true := by
    apply allModeFlipCandidate_encode hflip hflipCard hFlipSet hflipNodup
      startOccupied
    intro q hq
    apply hstart q
    rw [← hsupportUnion]
    exact Finset.mem_union_left _ hq
  let afterFlip : TermCode → Bool := fun q =>
    xor (startOccupied q) (q == Raw.encodeTerm t || q == Raw.encodeTerm u ||
      q == Raw.encodeTerm v || q == Raw.encodeTerm w)
  have hafterFlip (q : Carrier p) (hq : q ∈ D ∆ (C ∪ B)) :
      afterFlip (Raw.encodeTerm q) = decide (q ∈ D) := by
    have hqUnion : q ∈ insert t (A ∪ B) := by
      rw [← hsupportUnion]
      exact Finset.mem_union_right _ hq
    dsimp only [afterFlip]
    rw [hstart q hqUnion, support4Contains_encodeTerm t u v w q, ← hFlipSet]
    exact xor_decide_mem_support (C ∪ A) D q
  have hlineOccupancy : lineOccupancy afterFlip (Raw.encodeTerm t)
      (Raw.encodeTerm x) (Raw.encodeTerm y) = true := by
    apply allModeLineOccupancy_encode hline htx hty hxy hLineSet afterFlip
    intro q hq
    apply hafterFlip q
    rw [hLineSet]
    exact hq
  have htContains : (Acode ++ Bcode).contains (Raw.encodeTerm t) = false := by
    rw [list_contains_encodeTerm_eq_decide_mem (Acode ++ Bcode) (A ∪ B) hZencode]
    simp [htZ]
  unfold hasContextualTwoEdgePath
  apply List.any_eq_true.mpr
  refine ⟨((Raw.encodeTerm x, Raw.encodeTerm y),
    (Raw.encodeTerm u, Raw.encodeTerm v, Raw.encodeTerm w)), hsplit, ?_⟩
  dsimp only
  apply List.any_eq_true.mpr
  refine ⟨o, ho, ?_⟩
  rw [hcandidate]
  simp only
  unfold checkCandidate
  rw [htContains]
  simp only [Bool.not_false, Bool.true_and]
  apply List.any_eq_true.mpr
  refine ⟨decide (t ∈ C ∪ A), by cases decide (t ∈ C ∪ A) <;> simp, ?_⟩
  change (_ || (thirdFlip4 startOccupied (Raw.encodeTerm t)
    (Raw.encodeTerm u) (Raw.encodeTerm v) (Raw.encodeTerm w) &&
    lineOccupancy afterFlip (Raw.encodeTerm t) (Raw.encodeTerm x)
      (Raw.encodeTerm y))) = true
  rw [hflipCandidate, hlineOccupancy]
  simp only [Bool.true_and, Bool.or_true]

/-- A native path of length below three between correctly encoded contextual endpoints
is detected by the finite two-edge checker. -/
theorem hasContextualTwoEdgePath_of_native_path_lt_three {p : Profile}
    {C A B : State p} {Acode Bcode : List TermCode}
    (hCA : Disjoint C A) (hCB : Disjoint C B) (hAB : Disjoint A B)
    (hAcard : A.card = 2) (hBcard : B.card = 3)
    (hAencode : A.image Raw.encodeTerm = Acode.toFinset)
    (hBencode : B.image Raw.encodeTerm = Bcode.toFinset)
    (hAlength : Acode.length = 2) (hBlength : Bcode.length = 3)
    (hAnodup : Acode.Nodup) (hBnodup : Bcode.Nodup)
    (path : MovePath (fun X Y : State p => AllModeMove X Y)
      (C ∪ A) (C ∪ B))
    (hlength : path.length < 3) :
    hasContextualTwoEdgePath Acode Bcode = true := by
  obtain ⟨hZlength, hZnodup, hZencode⟩ :=
    encoded_endpoint_list_data hAB hAencode hBencode hAlength hBlength
      hAnodup hBnodup
  obtain ⟨D, t, hfirst, hsecond, htZ, hinter, hunion, _, _, horder⟩ :=
    short_path_two_support_localization hCA hCB hAB hAcard hBcard
      (fun {_ _} hmove => AllModeMove.support_card hmove) path hlength
  rcases horder with ⟨hfirstCard, hsecondCard⟩ | ⟨hfirstCard, hsecondCard⟩
  · exact checker_of_line_then_flip hCA hCB hfirst hsecond htZ hinter hunion
      hfirstCard hsecondCard hAencode hZencode hZlength hZnodup
  · exact checker_of_flip_then_line hCA hCB hfirst hsecond htZ hinter hunion
      hfirstCard hsecondCard hAencode hZencode hZlength hZnodup

/-- A false finite checker certificate excludes every native contextual path of
length below three. -/
theorem native_contextual_path_length_three_le_of_checker_false {p : Profile}
    {C A B : State p} {Acode Bcode : List TermCode}
    (hCA : Disjoint C A) (hCB : Disjoint C B) (hAB : Disjoint A B)
    (hAcard : A.card = 2) (hBcard : B.card = 3)
    (hAencode : A.image Raw.encodeTerm = Acode.toFinset)
    (hBencode : B.image Raw.encodeTerm = Bcode.toFinset)
    (hAlength : Acode.length = 2) (hBlength : Bcode.length = 3)
    (hAnodup : Acode.Nodup) (hBnodup : Bcode.Nodup)
    (hchecker : hasContextualTwoEdgePath Acode Bcode = false)
    (path : MovePath (fun X Y : State p => AllModeMove X Y)
      (C ∪ A) (C ∪ B)) :
    3 ≤ path.length := by
  by_contra hnot
  have hlength : path.length < 3 := Nat.lt_of_not_ge hnot
  have hdetected := hasContextualTwoEdgePath_of_native_path_lt_three
    hCA hCB hAB hAcard hBcard hAencode hBencode hAlength hBlength
    hAnodup hBnodup path hlength
  rw [hchecker] at hdetected
  exact Bool.noConfusion hdetected

private def reverseNativePath {p : Profile} :
    {X Y : State p} →
      MovePath (fun D E : State p => AllModeMove D E) X Y →
      MovePath (fun D E : State p => AllModeMove D E) Y X
  | _, _, .singleton X => .singleton X
  | _, _, .snoc path h =>
      (MovePath.one (AllModeMove.reverse h)).trans (reverseNativePath path)

private theorem movePath_trans_length {α : Type*} [DecidableEq α]
    {R : Finset α → Finset α → Prop} {X Y Z : Finset α}
    (p : MovePath R X Y) (q : MovePath R Y Z) :
    (p.trans q).length = p.length + q.length := by
  induction q with
  | singleton => simp only [MovePath.trans, MovePath.length, Nat.add_zero]
  | snoc q h ih => simp only [MovePath.trans, MovePath.length, ih, Nat.add_assoc]

private theorem reverseNativePath_length {p : Profile} {X Y : State p}
    (path : MovePath (fun D E : State p => AllModeMove D E) X Y) :
    (reverseNativePath path).length = path.length := by
  induction path with
  | singleton => simp only [reverseNativePath, MovePath.length]
  | snoc path h ih =>
      rw [reverseNativePath, movePath_trans_length, ih]
      simp only [MovePath.one, MovePath.length]
      omega

/-- The forward checker certificate also excludes reverse native paths, by
reversing every native move and preserving path length. -/
theorem reverse_native_contextual_path_length_three_le_of_checker_false {p : Profile}
    {C A B : State p} {Acode Bcode : List TermCode}
    (hCA : Disjoint C A) (hCB : Disjoint C B) (hAB : Disjoint A B)
    (hAcard : A.card = 2) (hBcard : B.card = 3)
    (hAencode : A.image Raw.encodeTerm = Acode.toFinset)
    (hBencode : B.image Raw.encodeTerm = Bcode.toFinset)
    (hAlength : Acode.length = 2) (hBlength : Bcode.length = 3)
    (hAnodup : Acode.Nodup) (hBnodup : Bcode.Nodup)
    (hchecker : hasContextualTwoEdgePath Acode Bcode = false)
    (path : MovePath (fun X Y : State p => AllModeMove X Y)
      (C ∪ B) (C ∪ A)) :
    3 ≤ path.length := by
  rw [← reverseNativePath_length path]
  exact native_contextual_path_length_three_le_of_checker_false
    hCA hCB hAB hAcard hBcard hAencode hBencode hAlength hBlength
    hAnodup hBnodup hchecker (reverseNativePath path)

/-- Every contextual native path from the `411-01` start row to its finish row
has length at least three. -/
theorem row41101_forward_contextual_length_three_le
    (C : State profile411)
    (hC : Disjoint C (row41101Start ∪ row41101Finish))
    (path : MovePath (fun X Y : State profile411 => AllModeMove X Y)
      (C ∪ row41101Start) (C ∪ row41101Finish)) :
    3 ≤ path.length := by
  apply native_contextual_path_length_three_le_of_checker_false
    (hC.mono_right Finset.subset_union_left)
    (hC.mono_right Finset.subset_union_right)
    row41101_disjoint row41101_card_start row41101_card_finish
    row41101Start_encode row41101Finish_encode
    (by decide) (by decide) (by decide) (by decide) row41101_no_two_edge path

/-- Every contextual native path from the `411-01` finish row back to its start
row has length at least three. -/
theorem row41101_reverse_contextual_length_three_le
    (C : State profile411)
    (hC : Disjoint C (row41101Start ∪ row41101Finish))
    (path : MovePath (fun X Y : State profile411 => AllModeMove X Y)
      (C ∪ row41101Finish) (C ∪ row41101Start)) :
    3 ≤ path.length := by
  apply reverse_native_contextual_path_length_three_le_of_checker_false
    (hC.mono_right Finset.subset_union_left)
    (hC.mono_right Finset.subset_union_right)
    row41101_disjoint row41101_card_start row41101_card_finish
    row41101Start_encode row41101Finish_encode
    (by decide) (by decide) (by decide) (by decide) row41101_no_two_edge path

/-- Every contextual native path from the `321-01` start row to its finish row
has length at least three. -/
theorem row32101_forward_contextual_length_three_le
    (C : State profile321)
    (hC : Disjoint C (row32101Start ∪ row32101Finish))
    (path : MovePath (fun X Y : State profile321 => AllModeMove X Y)
      (C ∪ row32101Start) (C ∪ row32101Finish)) :
    3 ≤ path.length := by
  apply native_contextual_path_length_three_le_of_checker_false
    (hC.mono_right Finset.subset_union_left)
    (hC.mono_right Finset.subset_union_right)
    row32101_disjoint row32101_card_start row32101_card_finish
    row32101Start_encode row32101Finish_encode
    (by decide) (by decide) (by decide) (by decide) row32101_no_two_edge path

/-- Every contextual native path from the `321-01` finish row back to its start
row has length at least three. -/
theorem row32101_reverse_contextual_length_three_le
    (C : State profile321)
    (hC : Disjoint C (row32101Start ∪ row32101Finish))
    (path : MovePath (fun X Y : State profile321 => AllModeMove X Y)
      (C ∪ row32101Finish) (C ∪ row32101Start)) :
    3 ≤ path.length := by
  apply reverse_native_contextual_path_length_three_le_of_checker_false
    (hC.mono_right Finset.subset_union_left)
    (hC.mono_right Finset.subset_union_right)
    row32101_disjoint row32101_card_start row32101_card_finish
    row32101Start_encode row32101Finish_encode
    (by decide) (by decide) (by decide) (by decide) row32101_no_two_edge path

/-- Every contextual native path from the `321-02` start row to its finish row
has length at least three. -/
theorem row32102_forward_contextual_length_three_le
    (C : State profile321)
    (hC : Disjoint C (row32102Start ∪ row32102Finish))
    (path : MovePath (fun X Y : State profile321 => AllModeMove X Y)
      (C ∪ row32102Start) (C ∪ row32102Finish)) :
    3 ≤ path.length := by
  apply native_contextual_path_length_three_le_of_checker_false
    (hC.mono_right Finset.subset_union_left)
    (hC.mono_right Finset.subset_union_right)
    row32102_disjoint row32102_card_start row32102_card_finish
    row32102Start_encode row32102Finish_encode
    (by decide) (by decide) (by decide) (by decide) row32102_no_two_edge path

/-- Every contextual native path from the `321-02` finish row back to its start
row has length at least three. -/
theorem row32102_reverse_contextual_length_three_le
    (C : State profile321)
    (hC : Disjoint C (row32102Start ∪ row32102Finish))
    (path : MovePath (fun X Y : State profile321 => AllModeMove X Y)
      (C ∪ row32102Finish) (C ∪ row32102Start)) :
    3 ≤ path.length := by
  apply reverse_native_contextual_path_length_three_le_of_checker_false
    (hC.mono_right Finset.subset_union_left)
    (hC.mono_right Finset.subset_union_right)
    row32102_disjoint row32102_card_start row32102_card_finish
    row32102Start_encode row32102Finish_encode
    (by decide) (by decide) (by decide) (by decide) row32102_no_two_edge path

/-- Every contextual native path from the `321-03` start row to its finish row
has length at least three. -/
theorem row32103_forward_contextual_length_three_le
    (C : State profile321)
    (hC : Disjoint C (row32103Start ∪ row32103Finish))
    (path : MovePath (fun X Y : State profile321 => AllModeMove X Y)
      (C ∪ row32103Start) (C ∪ row32103Finish)) :
    3 ≤ path.length := by
  apply native_contextual_path_length_three_le_of_checker_false
    (hC.mono_right Finset.subset_union_left)
    (hC.mono_right Finset.subset_union_right)
    row32103_disjoint row32103_card_start row32103_card_finish
    row32103Start_encode row32103Finish_encode
    (by decide) (by decide) (by decide) (by decide) row32103_no_two_edge path

/-- Every contextual native path from the `321-03` finish row back to its start
row has length at least three. -/
theorem row32103_reverse_contextual_length_three_le
    (C : State profile321)
    (hC : Disjoint C (row32103Start ∪ row32103Finish))
    (path : MovePath (fun X Y : State profile321 => AllModeMove X Y)
      (C ∪ row32103Finish) (C ∪ row32103Start)) :
    3 ≤ path.length := by
  apply reverse_native_contextual_path_length_three_le_of_checker_false
    (hC.mono_right Finset.subset_union_left)
    (hC.mono_right Finset.subset_union_right)
    row32103_disjoint row32103_card_start row32103_card_finish
    row32103Start_encode row32103Finish_encode
    (by decide) (by decide) (by decide) (by decide) row32103_no_two_edge path

/-- Every contextual native path from the `222-01` start row to its finish row
has length at least three. -/
theorem row22201_forward_contextual_length_three_le
    (C : State profile222)
    (hC : Disjoint C (row22201Start ∪ row22201Finish))
    (path : MovePath (fun X Y : State profile222 => AllModeMove X Y)
      (C ∪ row22201Start) (C ∪ row22201Finish)) :
    3 ≤ path.length := by
  apply native_contextual_path_length_three_le_of_checker_false
    (hC.mono_right Finset.subset_union_left)
    (hC.mono_right Finset.subset_union_right)
    row22201_disjoint row22201_card_start row22201_card_finish
    row22201Start_encode row22201Finish_encode
    (by decide) (by decide) (by decide) (by decide) row22201_no_two_edge path

/-- Every contextual native path from the `222-01` finish row back to its start
row has length at least three. -/
theorem row22201_reverse_contextual_length_three_le
    (C : State profile222)
    (hC : Disjoint C (row22201Start ∪ row22201Finish))
    (path : MovePath (fun X Y : State profile222 => AllModeMove X Y)
      (C ∪ row22201Finish) (C ∪ row22201Start)) :
    3 ≤ path.length := by
  apply reverse_native_contextual_path_length_three_le_of_checker_false
    (hC.mono_right Finset.subset_union_left)
    (hC.mono_right Finset.subset_union_right)
    row22201_disjoint row22201_card_start row22201_card_finish
    row22201Start_encode row22201Finish_encode
    (by decide) (by decide) (by decide) (by decide) row22201_no_two_edge path

end BilinearComplexity.BinaryContextualNativeExclusion
