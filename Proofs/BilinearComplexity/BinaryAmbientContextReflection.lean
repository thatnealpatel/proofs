import BilinearComplexity.BinaryAmbientContextTransport
import BilinearComplexity.BinaryAmbientMoveSupport

/-!
# Reflection of local ambient moves into exact-span coordinates

An ambient intrinsic edge whose complete symmetric-difference support lies in
an exact endpoint factor box can be reflected into the supplied normalized
coordinates.  The reflection retains the primitive constructor, witness order,
freshness, and direction in every simultaneous mode orientation.
-/

set_option autoImplicit false

namespace BilinearComplexity.BinaryAmbientContextReflection

open scoped symmDiff
open BinaryCircuit
open BinaryAmbientCarrier
open BinaryAmbientMoves
open BinaryAmbientMoveSupport
open BinaryAmbientMoveTransport
open BinaryAmbientNormalization
open BinaryFiveCircuitCompiler
open BinaryAmbientContextTransport
open NormalizedBinaryCarrier

universe u v w

variable {U : Type u} {V : Type v} {W : Type w}
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [Module F2 U] [Module F2 V] [Module F2 W]
variable [DecidableEq U] [DecidableEq V] [DecidableEq W]

private structure FactorChart (p : Profile) (U : Type u) (V : Type v)
    (W : Type w) [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W] where
  firstSpan : Submodule F2 U
  secondSpan : Submodule F2 V
  thirdSpan : Submodule F2 W
  firstCoordinates : CoordinateVector p.first ≃ₗ[F2] firstSpan
  secondCoordinates : CoordinateVector p.second ≃ₗ[F2] secondSpan
  thirdCoordinates : CoordinateVector p.third ≃ₗ[F2] thirdSpan

private def FactorChart.embedding {p : Profile} (Q : FactorChart p U V W) :
    CoordinateEmbedding p U V W where
  first := Q.firstSpan.subtype.comp Q.firstCoordinates.toLinearMap
  second := Q.secondSpan.subtype.comp Q.secondCoordinates.toLinearMap
  third := Q.thirdSpan.subtype.comp Q.thirdCoordinates.toLinearMap
  first_injective := by
    intro x y hxy
    apply Q.firstCoordinates.injective
    exact Subtype.ext hxy
  second_injective := by
    intro x y hxy
    apply Q.secondCoordinates.injective
    exact Subtype.ext hxy
  third_injective := by
    intro x y hxy
    apply Q.thirdCoordinates.injective
    exact Subtype.ext hxy

private def FactorChart.box {p : Profile} (Q : FactorChart p U V W) :
    BinaryAmbientCarrier.State U V W :=
  mapState Q.embedding (Finset.univ : NormalizedBinaryCarrier.State p)

private def FactorChart.normalize {p : Profile} (Q : FactorChart p U V W)
    (X : BinaryAmbientCarrier.State U V W) : NormalizedBinaryCarrier.State p :=
  Finset.univ.filter (fun t => mapTerm Q.embedding t ∈ X)

private theorem FactorChart.mem_normalize_iff {p : Profile}
    (Q : FactorChart p U V W) (X : BinaryAmbientCarrier.State U V W)
    (s : NormalizedBinaryCarrier.Carrier p) :
    s ∈ Q.normalize X ↔ mapTerm Q.embedding s ∈ X := by
  simp only [FactorChart.normalize, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem FactorChart.mapState_normalize {p : Profile}
    (Q : FactorChart p U V W) (X : BinaryAmbientCarrier.State U V W) :
    mapState Q.embedding (Q.normalize X) = X ∩ Q.box := by
  ext t
  constructor
  · intro ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_inter.mpr ⟨(Q.mem_normalize_iff X s).mp hs,
      Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩⟩
  · intro ht
    obtain ⟨htX, htBox⟩ := Finset.mem_inter.mp ht
    obtain ⟨s, _hs, hst⟩ := Finset.mem_image.mp htBox
    subst t
    exact Finset.mem_image.mpr ⟨s, (Q.mem_normalize_iff X s).mpr htX, rfl⟩

private theorem FactorChart.mem_box_iff {p : Profile}
    (Q : FactorChart p U V W) (t : BinaryAmbientCarrier.Carrier U V W) :
    t ∈ Q.box ↔
      t.1.1 ∈ Q.firstSpan ∧ t.2.1.1 ∈ Q.secondSpan ∧
        t.2.2.1 ∈ Q.thirdSpan := by
  constructor
  · intro ht
    obtain ⟨s, _hs, hst⟩ := Finset.mem_image.mp ht
    rw [← hst]
    exact ⟨(Q.firstCoordinates s.1.1).property,
      (Q.secondCoordinates s.2.1.1).property,
      (Q.thirdCoordinates s.2.2.1).property⟩
  · rintro ⟨hfirst, hsecond, hthird⟩
    let x := Q.firstCoordinates.symm ⟨t.1.1, hfirst⟩
    let y := Q.secondCoordinates.symm ⟨t.2.1.1, hsecond⟩
    let z := Q.thirdCoordinates.symm ⟨t.2.2.1, hthird⟩
    have hx : x ≠ 0 := by
      intro hxzero
      have hsub : (⟨t.1.1, hfirst⟩ : Q.firstSpan) = 0 := by
        calc
          _ = Q.firstCoordinates x := (Q.firstCoordinates.apply_symm_apply _).symm
          _ = Q.firstCoordinates 0 := congrArg Q.firstCoordinates hxzero
          _ = 0 := Q.firstCoordinates.map_zero
      exact t.1.2 (congrArg Subtype.val hsub)
    have hy : y ≠ 0 := by
      intro hyzero
      have hsub : (⟨t.2.1.1, hsecond⟩ : Q.secondSpan) = 0 := by
        calc
          _ = Q.secondCoordinates y := (Q.secondCoordinates.apply_symm_apply _).symm
          _ = Q.secondCoordinates 0 := congrArg Q.secondCoordinates hyzero
          _ = 0 := Q.secondCoordinates.map_zero
      exact t.2.1.2 (congrArg Subtype.val hsub)
    have hz : z ≠ 0 := by
      intro hzzero
      have hsub : (⟨t.2.2.1, hthird⟩ : Q.thirdSpan) = 0 := by
        calc
          _ = Q.thirdCoordinates z := (Q.thirdCoordinates.apply_symm_apply _).symm
          _ = Q.thirdCoordinates 0 := congrArg Q.thirdCoordinates hzzero
          _ = 0 := Q.thirdCoordinates.map_zero
      exact t.2.2.2 (congrArg Subtype.val hsub)
    let s : NormalizedBinaryCarrier.Carrier p :=
      (⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩)
    apply Finset.mem_image.mpr
    refine ⟨s, Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      change (Q.firstCoordinates x).1 = t.1.1
      simp only [x, Q.firstCoordinates.apply_symm_apply]
    · apply Prod.ext
      · apply Subtype.ext
        change (Q.secondCoordinates y).1 = t.2.1.1
        simp only [y, Q.secondCoordinates.apply_symm_apply]
      · apply Subtype.ext
        change (Q.thirdCoordinates z).1 = t.2.2.1
        simp only [z, Q.thirdCoordinates.apply_symm_apply]

private def FactorChart.pullTerm {p : Profile} (Q : FactorChart p U V W)
    (t : BinaryAmbientCarrier.Carrier U V W) (ht : t ∈ Q.box) :
    NormalizedBinaryCarrier.Carrier p :=
  let h := (Q.mem_box_iff t).mp ht
  let x := Q.firstCoordinates.symm ⟨t.1.1, h.1⟩
  let y := Q.secondCoordinates.symm ⟨t.2.1.1, h.2.1⟩
  let z := Q.thirdCoordinates.symm ⟨t.2.2.1, h.2.2⟩
  (⟨x, by
      intro hxzero
      have hsub : (⟨t.1.1, h.1⟩ : Q.firstSpan) = 0 := by
        calc
          _ = Q.firstCoordinates x := (Q.firstCoordinates.apply_symm_apply _).symm
          _ = Q.firstCoordinates 0 := congrArg Q.firstCoordinates hxzero
          _ = 0 := Q.firstCoordinates.map_zero
      exact t.1.2 (congrArg Subtype.val hsub)⟩,
   ⟨y, by
      intro hyzero
      have hsub : (⟨t.2.1.1, h.2.1⟩ : Q.secondSpan) = 0 := by
        calc
          _ = Q.secondCoordinates y := (Q.secondCoordinates.apply_symm_apply _).symm
          _ = Q.secondCoordinates 0 := congrArg Q.secondCoordinates hyzero
          _ = 0 := Q.secondCoordinates.map_zero
      exact t.2.1.2 (congrArg Subtype.val hsub)⟩,
   ⟨z, by
      intro hzzero
      have hsub : (⟨t.2.2.1, h.2.2⟩ : Q.thirdSpan) = 0 := by
        calc
          _ = Q.thirdCoordinates z := (Q.thirdCoordinates.apply_symm_apply _).symm
          _ = Q.thirdCoordinates 0 := congrArg Q.thirdCoordinates hzzero
          _ = 0 := Q.thirdCoordinates.map_zero
      exact t.2.2.2 (congrArg Subtype.val hsub)⟩)

private theorem FactorChart.mapTerm_pullTerm {p : Profile}
    (Q : FactorChart p U V W) (t : BinaryAmbientCarrier.Carrier U V W)
    (ht : t ∈ Q.box) : mapTerm Q.embedding (Q.pullTerm t ht) = t := by
  apply Prod.ext
  · apply Subtype.ext
    change (Q.firstCoordinates (Q.firstCoordinates.symm _)).1 = t.1.1
    exact congrArg Subtype.val (Q.firstCoordinates.apply_symm_apply _)
  · apply Prod.ext
    · apply Subtype.ext
      change (Q.secondCoordinates (Q.secondCoordinates.symm _)).1 = t.2.1.1
      exact congrArg Subtype.val (Q.secondCoordinates.apply_symm_apply _)
    · apply Subtype.ext
      change (Q.thirdCoordinates (Q.thirdCoordinates.symm _)).1 = t.2.2.1
      exact congrArg Subtype.val (Q.thirdCoordinates.apply_symm_apply _)

private def presentationChart {A B : BinaryAmbientCarrier.State U V W}
    (P : ExactSpanPresentation A B) : FactorChart P.profile U V W where
  firstSpan := firstSpan (A ∪ B)
  secondSpan := secondSpan (A ∪ B)
  thirdSpan := thirdSpan (A ∪ B)
  firstCoordinates := P.firstCoordinates
  secondCoordinates := P.secondCoordinates
  thirdCoordinates := P.thirdCoordinates

private theorem presentationChart_box {A B : BinaryAmbientCarrier.State U V W}
    (P : ExactSpanPresentation A B) : (presentationChart P).box = localBox P := rfl

private theorem presentationChart_normalize {A B : BinaryAmbientCarrier.State U V W}
    (P : ExactSpanPresentation A B) (X : BinaryAmbientCarrier.State U V W) :
    (presentationChart P).normalize X = normalizeLocalContext P X := rfl

omit [Module F2 U] [Module F2 V] [Module F2 W] in
private theorem generatedFirstSplit_inter
    {source outputLeft outputRight : BinaryAmbientCarrier.Carrier U V W}
    {X Y K : BinaryAmbientCarrier.State U V W}
    (h : GeneratedFirstSplit source outputLeft outputRight X Y)
    (hsupport : X ∆ Y ⊆ K) :
    GeneratedFirstSplit source outputLeft outputRight (X ∩ K) (Y ∩ K) := by
  have hdiff := BinaryAmbientMoveSupport.GeneratedFirstSplit.symmDiff_eq h
  have hsourceK : source ∈ K := hsupport (by rw [hdiff]; simp)
  have hleftK : outputLeft ∈ K := hsupport (by rw [hdiff]; simp)
  have hrightK : outputRight ∈ K := hsupport (by rw [hdiff]; simp)
  rcases h with ⟨hsource, houtputs, hfreshLeft, hfreshRight, hfirst,
    hleftSecond, hrightSecond, hleftThird, hrightThird, hY⟩
  refine ⟨Finset.mem_inter.mpr ⟨hsource, hsourceK⟩, houtputs, ?_, ?_,
    hfirst, hleftSecond, hrightSecond, hleftThird, hrightThird, ?_⟩
  · intro hmem
    obtain ⟨hne, hmemX, _hmemK⟩ := by
      simpa only [Finset.mem_erase, Finset.mem_inter] using hmem
    exact hfreshLeft (Finset.mem_erase.mpr ⟨hne, hmemX⟩)
  · intro hmem
    obtain ⟨hne, hmemX, _hmemK⟩ := by
      simpa only [Finset.mem_erase, Finset.mem_inter] using hmem
    exact hfreshRight (Finset.mem_erase.mpr ⟨hne, hmemX⟩)
  · ext t
    rw [hY]
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
    by_cases htLeft : t = outputLeft
    · simp [htLeft, hleftK]
    by_cases htRight : t = outputRight
    · simp [htRight, hrightK]
    by_cases htSource : t = source
    · simp [htSource, hsourceK]
    simp [htLeft, htRight, htSource]

omit [Module F2 U] [Module F2 W] in
private theorem sourceThirdFlip_inter
    {sourceLeft sourceRight targetLeft targetRight :
      BinaryAmbientCarrier.Carrier U V W}
    {X Y K : BinaryAmbientCarrier.State U V W}
    (h : SourceThirdFlip sourceLeft sourceRight targetLeft targetRight X Y)
    (hsupport : X ∆ Y ⊆ K) :
    SourceThirdFlip sourceLeft sourceRight targetLeft targetRight
      (X ∩ K) (Y ∩ K) := by
  have hdiff := BinaryAmbientMoveSupport.SourceThirdFlip.symmDiff_eq h
  have hsourceLeftK : sourceLeft ∈ K := hsupport (by rw [hdiff]; simp)
  have hsourceRightK : sourceRight ∈ K := hsupport (by rw [hdiff]; simp)
  have htargetLeftK : targetLeft ∈ K := hsupport (by rw [hdiff]; simp)
  have htargetRightK : targetRight ∈ K := hsupport (by rw [hdiff]; simp)
  rcases h with ⟨hleft, hright, hsources, hfreshLeft, hfreshRight, htargets,
    hthird, htargetLeftFirst, htargetLeftSecond, htargetLeftThird,
    htargetRightFirst, htargetRightSecond, htargetRightThird, hY⟩
  refine ⟨Finset.mem_inter.mpr ⟨hleft, hsourceLeftK⟩,
    Finset.mem_inter.mpr ⟨hright, hsourceRightK⟩, hsources, ?_, ?_, htargets,
    hthird, htargetLeftFirst, htargetLeftSecond, htargetLeftThird,
    htargetRightFirst, htargetRightSecond, htargetRightThird, ?_⟩
  · intro hmem
    obtain ⟨hneRight, hneLeft, hmemX, _hmemK⟩ := by
      simpa only [Finset.mem_erase, Finset.mem_inter] using hmem
    exact hfreshLeft (Finset.mem_erase.mpr ⟨hneRight,
      Finset.mem_erase.mpr ⟨hneLeft, hmemX⟩⟩)
  · intro hmem
    obtain ⟨hneRight, hneLeft, hmemX, _hmemK⟩ := by
      simpa only [Finset.mem_erase, Finset.mem_inter] using hmem
    exact hfreshRight (Finset.mem_erase.mpr ⟨hneRight,
      Finset.mem_erase.mpr ⟨hneLeft, hmemX⟩⟩)
  · ext t
    rw [hY]
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
    by_cases htTL : t = targetLeft
    · simp [htTL, htargetLeftK]
    by_cases htTR : t = targetRight
    · simp [htTR, htargetRightK]
    by_cases htSL : t = sourceLeft
    · simp [htSL, hsourceLeftK]
    by_cases htSR : t = sourceRight
    · simp [htSR, hsourceRightK]
    simp [htTL, htTR, htSL, htSR]

omit [Module F2 U] [Module F2 V] [Module F2 W] in
private theorem directedNarrowPairReduction_inter
    {sourceLeft sourceRight target : BinaryAmbientCarrier.Carrier U V W}
    {X Y K : BinaryAmbientCarrier.State U V W}
    (h : DirectedNarrowPairReduction sourceLeft sourceRight target X Y)
    (hsupport : X ∆ Y ⊆ K) :
    DirectedNarrowPairReduction sourceLeft sourceRight target (X ∩ K) (Y ∩ K) := by
  have hdiff := BinaryAmbientMoveSupport.DirectedNarrowPairReduction.symmDiff_eq h
  have hsourceLeftK : sourceLeft ∈ K := hsupport (by rw [hdiff]; simp)
  have hsourceRightK : sourceRight ∈ K := hsupport (by rw [hdiff]; simp)
  have htargetK : target ∈ K := hsupport (by rw [hdiff]; simp)
  rcases h with ⟨hleft, hright, hsources, hfresh, hsecond, hthird,
    htargetFirst, htargetSecond, htargetThird, hY⟩
  refine ⟨Finset.mem_inter.mpr ⟨hleft, hsourceLeftK⟩,
    Finset.mem_inter.mpr ⟨hright, hsourceRightK⟩, hsources, ?_, hsecond,
    hthird, htargetFirst, htargetSecond, htargetThird, ?_⟩
  · intro hmem
    obtain ⟨hneRight, hneLeft, hmemX, _hmemK⟩ := by
      simpa only [Finset.mem_erase, Finset.mem_inter] using hmem
    exact hfresh (Finset.mem_erase.mpr ⟨hneRight,
      Finset.mem_erase.mpr ⟨hneLeft, hmemX⟩⟩)
  · ext t
    rw [hY]
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
    by_cases htTarget : t = target
    · simp [htTarget, htargetK]
    by_cases htSL : t = sourceLeft
    · simp [htSL, hsourceLeftK]
    by_cases htSR : t = sourceRight
    · simp [htSR, hsourceRightK]
    simp [htTarget, htSL, htSR]

private theorem FactorChart.mapState_injective {p : Profile}
    (Q : FactorChart p U V W) : Function.Injective (mapState Q.embedding) :=
  Finset.image_injective (mapTerm_injective Q.embedding)

private theorem generatedFirstSplit_pullback {p : Profile}
    (Q : FactorChart p U V W)
    {source outputLeft outputRight : BinaryAmbientCarrier.Carrier U V W}
    {X Y : BinaryAmbientCarrier.State U V W}
    (h : GeneratedFirstSplit source outputLeft outputRight X Y)
    (hsupport : X ∆ Y ⊆ Q.box) :
    BinaryAmbientMoves.GeneratedFirstSplit
      (Q.pullTerm source (hsupport (by
        rw [BinaryAmbientMoveSupport.GeneratedFirstSplit.symmDiff_eq h]; simp)))
      (Q.pullTerm outputLeft (hsupport (by
        rw [BinaryAmbientMoveSupport.GeneratedFirstSplit.symmDiff_eq h]; simp)))
      (Q.pullTerm outputRight (hsupport (by
        rw [BinaryAmbientMoveSupport.GeneratedFirstSplit.symmDiff_eq h]; simp)))
      (Q.normalize X) (Q.normalize Y) := by
  have hdiff := BinaryAmbientMoveSupport.GeneratedFirstSplit.symmDiff_eq h
  let hsK : source ∈ Q.box := hsupport (by rw [hdiff]; simp)
  let hlK : outputLeft ∈ Q.box := hsupport (by rw [hdiff]; simp)
  let hrK : outputRight ∈ Q.box := hsupport (by rw [hdiff]; simp)
  let s := Q.pullTerm source hsK
  let l := Q.pullTerm outputLeft hlK
  let r := Q.pullTerm outputRight hrK
  have hsMap : mapTerm Q.embedding s = source := Q.mapTerm_pullTerm source hsK
  have hlMap : mapTerm Q.embedding l = outputLeft := Q.mapTerm_pullTerm outputLeft hlK
  have hrMap : mapTerm Q.embedding r = outputRight := Q.mapTerm_pullTerm outputRight hrK
  have hi := generatedFirstSplit_inter h hsupport
  change GeneratedFirstSplit s l r (Q.normalize X) (Q.normalize Y)
  refine ⟨(Q.mem_normalize_iff X s).mpr (by rw [hsMap]; exact h.1), ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hlr
    apply h.2.1
    rw [← hlMap, ← hrMap, hlr]
  · intro hmem
    apply hi.2.2.1
    have hmapped : mapTerm Q.embedding l ∈
        mapState Q.embedding ((Q.normalize X).erase s) :=
      (mapState_mem Q.embedding).mpr hmem
    rw [mapState_erase, Q.mapState_normalize, hsMap, hlMap] at hmapped
    exact hmapped
  · intro hmem
    apply hi.2.2.2.1
    have hmapped : mapTerm Q.embedding r ∈
        mapState Q.embedding ((Q.normalize X).erase s) :=
      (mapState_mem Q.embedding).mpr hmem
    rw [mapState_erase, Q.mapState_normalize, hsMap, hrMap] at hmapped
    exact hmapped
  · apply Q.embedding.first_injective
    rw [Q.embedding.first.map_add]
    exact (congrArg (fun t => t.1.1) hsMap).trans
      (h.2.2.2.2.1.trans (congrArg₂ (· + ·)
        (congrArg (fun t => t.1.1) hlMap).symm
        (congrArg (fun t => t.1.1) hrMap).symm))
  · apply Q.embedding.second_injective
    exact (congrArg (fun t => t.2.1.1) hlMap).trans
      (h.2.2.2.2.2.1.trans (congrArg (fun t => t.2.1.1) hsMap).symm)
  · apply Q.embedding.second_injective
    exact (congrArg (fun t => t.2.1.1) hrMap).trans
      (h.2.2.2.2.2.2.1.trans (congrArg (fun t => t.2.1.1) hsMap).symm)
  · apply Q.embedding.third_injective
    exact (congrArg (fun t => t.2.2.1) hlMap).trans
      (h.2.2.2.2.2.2.2.1.trans (congrArg (fun t => t.2.2.1) hsMap).symm)
  · apply Q.embedding.third_injective
    exact (congrArg (fun t => t.2.2.1) hrMap).trans
      (h.2.2.2.2.2.2.2.2.1.trans (congrArg (fun t => t.2.2.1) hsMap).symm)
  · apply Q.mapState_injective
    rw [mapState_insert, mapState_insert, mapState_erase,
      Q.mapState_normalize, Q.mapState_normalize, hlMap, hrMap, hsMap]
    exact hi.2.2.2.2.2.2.2.2.2

private theorem sourceThirdFlip_pullback {p : Profile}
    (Q : FactorChart p U V W)
    {sourceLeft sourceRight targetLeft targetRight :
      BinaryAmbientCarrier.Carrier U V W}
    {X Y : BinaryAmbientCarrier.State U V W}
    (h : SourceThirdFlip sourceLeft sourceRight targetLeft targetRight X Y)
    (hsupport : X ∆ Y ⊆ Q.box) :
    BinaryAmbientMoves.SourceThirdFlip
      (Q.pullTerm sourceLeft (hsupport (by
        rw [BinaryAmbientMoveSupport.SourceThirdFlip.symmDiff_eq h]; simp)))
      (Q.pullTerm sourceRight (hsupport (by
        rw [BinaryAmbientMoveSupport.SourceThirdFlip.symmDiff_eq h]; simp)))
      (Q.pullTerm targetLeft (hsupport (by
        rw [BinaryAmbientMoveSupport.SourceThirdFlip.symmDiff_eq h]; simp)))
      (Q.pullTerm targetRight (hsupport (by
        rw [BinaryAmbientMoveSupport.SourceThirdFlip.symmDiff_eq h]; simp)))
      (Q.normalize X) (Q.normalize Y) := by
  have hdiff := BinaryAmbientMoveSupport.SourceThirdFlip.symmDiff_eq h
  let hslK : sourceLeft ∈ Q.box := hsupport (by rw [hdiff]; simp)
  let hsrK : sourceRight ∈ Q.box := hsupport (by rw [hdiff]; simp)
  let htlK : targetLeft ∈ Q.box := hsupport (by rw [hdiff]; simp)
  let htrK : targetRight ∈ Q.box := hsupport (by rw [hdiff]; simp)
  let sl := Q.pullTerm sourceLeft hslK
  let sr := Q.pullTerm sourceRight hsrK
  let tl := Q.pullTerm targetLeft htlK
  let tr := Q.pullTerm targetRight htrK
  have hslMap : mapTerm Q.embedding sl = sourceLeft := Q.mapTerm_pullTerm sourceLeft hslK
  have hsrMap : mapTerm Q.embedding sr = sourceRight := Q.mapTerm_pullTerm sourceRight hsrK
  have htlMap : mapTerm Q.embedding tl = targetLeft := Q.mapTerm_pullTerm targetLeft htlK
  have htrMap : mapTerm Q.embedding tr = targetRight := Q.mapTerm_pullTerm targetRight htrK
  have hi := sourceThirdFlip_inter h hsupport
  change SourceThirdFlip sl sr tl tr (Q.normalize X) (Q.normalize Y)
  refine ⟨(Q.mem_normalize_iff X sl).mpr (by rw [hslMap]; exact h.1),
    (Q.mem_normalize_iff X sr).mpr (by rw [hsrMap]; exact h.2.1), ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro heq
    apply h.2.2.1
    rw [← hslMap, ← hsrMap, heq]
  · intro hmem
    apply hi.2.2.2.1
    have hmapped : mapTerm Q.embedding tl ∈
        mapState Q.embedding (((Q.normalize X).erase sl).erase sr) :=
      (mapState_mem Q.embedding).mpr hmem
    rw [mapState_erase, mapState_erase, Q.mapState_normalize,
      hslMap, hsrMap, htlMap] at hmapped
    exact hmapped
  · intro hmem
    apply hi.2.2.2.2.1
    have hmapped : mapTerm Q.embedding tr ∈
        mapState Q.embedding (((Q.normalize X).erase sl).erase sr) :=
      (mapState_mem Q.embedding).mpr hmem
    rw [mapState_erase, mapState_erase, Q.mapState_normalize,
      hslMap, hsrMap, htrMap] at hmapped
    exact hmapped
  · intro heq
    apply h.2.2.2.2.2.1
    rw [← htlMap, ← htrMap, heq]
  · apply Q.embedding.third_injective
    exact (congrArg (fun t => t.2.2.1) hsrMap).trans
      (h.2.2.2.2.2.2.1.trans (congrArg (fun t => t.2.2.1) hslMap).symm)
  · apply Q.embedding.first_injective
    rw [Q.embedding.first.map_add]
    exact (congrArg (fun t => t.1.1) htlMap).trans
      (h.2.2.2.2.2.2.2.1.trans (congrArg₂ (· + ·)
        (congrArg (fun t => t.1.1) hslMap).symm
        (congrArg (fun t => t.1.1) hsrMap).symm))
  · apply Q.embedding.second_injective
    exact (congrArg (fun t => t.2.1.1) htlMap).trans
      (h.2.2.2.2.2.2.2.2.1.trans (congrArg (fun t => t.2.1.1) hslMap).symm)
  · apply Q.embedding.third_injective
    exact (congrArg (fun t => t.2.2.1) htlMap).trans
      (h.2.2.2.2.2.2.2.2.2.1.trans (congrArg (fun t => t.2.2.1) hslMap).symm)
  · apply Q.embedding.first_injective
    exact (congrArg (fun t => t.1.1) htrMap).trans
      (h.2.2.2.2.2.2.2.2.2.2.1.trans (congrArg (fun t => t.1.1) hsrMap).symm)
  · apply Q.embedding.second_injective
    rw [Q.embedding.second.map_sub]
    exact (congrArg (fun t => t.2.1.1) htrMap).trans
      (h.2.2.2.2.2.2.2.2.2.2.2.1.trans (congrArg₂ (· - ·)
        (congrArg (fun t => t.2.1.1) hsrMap).symm
        (congrArg (fun t => t.2.1.1) hslMap).symm))
  · apply Q.embedding.third_injective
    exact (congrArg (fun t => t.2.2.1) htrMap).trans
      (h.2.2.2.2.2.2.2.2.2.2.2.2.1.trans
        (congrArg (fun t => t.2.2.1) hslMap).symm)
  · apply Q.mapState_injective
    rw [mapState_insert, mapState_insert, mapState_erase, mapState_erase,
      Q.mapState_normalize, Q.mapState_normalize, htlMap, htrMap, hslMap, hsrMap]
    exact hi.2.2.2.2.2.2.2.2.2.2.2.2.2

private theorem directedNarrowPairReduction_pullback {p : Profile}
    (Q : FactorChart p U V W)
    {sourceLeft sourceRight target : BinaryAmbientCarrier.Carrier U V W}
    {X Y : BinaryAmbientCarrier.State U V W}
    (h : DirectedNarrowPairReduction sourceLeft sourceRight target X Y)
    (hsupport : X ∆ Y ⊆ Q.box) :
    BinaryAmbientMoves.DirectedNarrowPairReduction
      (Q.pullTerm sourceLeft (hsupport (by
        rw [BinaryAmbientMoveSupport.DirectedNarrowPairReduction.symmDiff_eq h]; simp)))
      (Q.pullTerm sourceRight (hsupport (by
        rw [BinaryAmbientMoveSupport.DirectedNarrowPairReduction.symmDiff_eq h]; simp)))
      (Q.pullTerm target (hsupport (by
        rw [BinaryAmbientMoveSupport.DirectedNarrowPairReduction.symmDiff_eq h]; simp)))
      (Q.normalize X) (Q.normalize Y) := by
  have hdiff := BinaryAmbientMoveSupport.DirectedNarrowPairReduction.symmDiff_eq h
  let hslK : sourceLeft ∈ Q.box := hsupport (by rw [hdiff]; simp)
  let hsrK : sourceRight ∈ Q.box := hsupport (by rw [hdiff]; simp)
  let htK : target ∈ Q.box := hsupport (by rw [hdiff]; simp)
  let sl := Q.pullTerm sourceLeft hslK
  let sr := Q.pullTerm sourceRight hsrK
  let t := Q.pullTerm target htK
  have hslMap : mapTerm Q.embedding sl = sourceLeft := Q.mapTerm_pullTerm sourceLeft hslK
  have hsrMap : mapTerm Q.embedding sr = sourceRight := Q.mapTerm_pullTerm sourceRight hsrK
  have htMap : mapTerm Q.embedding t = target := Q.mapTerm_pullTerm target htK
  have hi := directedNarrowPairReduction_inter h hsupport
  change DirectedNarrowPairReduction sl sr t (Q.normalize X) (Q.normalize Y)
  refine ⟨(Q.mem_normalize_iff X sl).mpr (by rw [hslMap]; exact h.1),
    (Q.mem_normalize_iff X sr).mpr (by rw [hsrMap]; exact h.2.1), ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro heq
    apply h.2.2.1
    rw [← hslMap, ← hsrMap, heq]
  · intro hmem
    apply hi.2.2.2.1
    have hmapped : mapTerm Q.embedding t ∈
        mapState Q.embedding (((Q.normalize X).erase sl).erase sr) :=
      (mapState_mem Q.embedding).mpr hmem
    rw [mapState_erase, mapState_erase, Q.mapState_normalize,
      hslMap, hsrMap, htMap] at hmapped
    exact hmapped
  · apply Q.embedding.second_injective
    exact (congrArg (fun z => z.2.1.1) hsrMap).trans
      (h.2.2.2.2.1.trans (congrArg (fun z => z.2.1.1) hslMap).symm)
  · apply Q.embedding.third_injective
    exact (congrArg (fun z => z.2.2.1) hsrMap).trans
      (h.2.2.2.2.2.1.trans (congrArg (fun z => z.2.2.1) hslMap).symm)
  · apply Q.embedding.first_injective
    rw [Q.embedding.first.map_add]
    exact (congrArg (fun z => z.1.1) htMap).trans
      (h.2.2.2.2.2.2.1.trans (congrArg₂ (· + ·)
        (congrArg (fun z => z.1.1) hslMap).symm
        (congrArg (fun z => z.1.1) hsrMap).symm))
  · apply Q.embedding.second_injective
    exact (congrArg (fun z => z.2.1.1) htMap).trans
      (h.2.2.2.2.2.2.2.1.trans (congrArg (fun z => z.2.1.1) hslMap).symm)
  · apply Q.embedding.third_injective
    exact (congrArg (fun z => z.2.2.1) htMap).trans
      (h.2.2.2.2.2.2.2.2.1.trans (congrArg (fun z => z.2.2.1) hslMap).symm)
  · apply Q.mapState_injective
    rw [mapState_insert, mapState_erase, mapState_erase,
      Q.mapState_normalize, Q.mapState_normalize, htMap, hslMap, hsrMap]
    exact hi.2.2.2.2.2.2.2.2.2

private theorem move_pullback {p : Profile} (Q : FactorChart p U V W)
    {X Y : BinaryAmbientCarrier.State U V W}
    (h : BinaryAmbientMoves.Move X Y) (hsupport : X ∆ Y ⊆ Q.box) :
    BinaryAmbientMoves.Move
      (U := CoordinateVector p.first) (V := CoordinateVector p.second)
      (W := CoordinateVector p.third) (Q.normalize X) (Q.normalize Y) := by
  cases h with
  | generatedFirstSplit hsplit =>
      exact .generatedFirstSplit (generatedFirstSplit_pullback Q hsplit hsupport)
  | sourceThirdFlip hflip =>
      exact .sourceThirdFlip (sourceThirdFlip_pullback Q hflip hsupport)
  | directedNarrowPairReduction hreduction =>
      exact .directedNarrowPairReduction
        (directedNarrowPairReduction_pullback Q hreduction hsupport)

private def FactorChart.bca {p : Profile} (Q : FactorChart p U V W) :
    FactorChart ⟨p.third, p.first, p.second⟩ W U V where
  firstSpan := Q.thirdSpan
  secondSpan := Q.firstSpan
  thirdSpan := Q.secondSpan
  firstCoordinates := Q.thirdCoordinates
  secondCoordinates := Q.firstCoordinates
  thirdCoordinates := Q.secondCoordinates

private def FactorChart.cab {p : Profile} (Q : FactorChart p U V W) :
    FactorChart ⟨p.second, p.third, p.first⟩ V W U where
  firstSpan := Q.secondSpan
  secondSpan := Q.thirdSpan
  thirdSpan := Q.firstSpan
  firstCoordinates := Q.secondCoordinates
  secondCoordinates := Q.thirdCoordinates
  thirdCoordinates := Q.firstCoordinates

private def FactorChart.acb {p : Profile} (Q : FactorChart p U V W) :
    FactorChart ⟨p.first, p.third, p.second⟩ U W V where
  firstSpan := Q.firstSpan
  secondSpan := Q.thirdSpan
  thirdSpan := Q.secondSpan
  firstCoordinates := Q.firstCoordinates
  secondCoordinates := Q.thirdCoordinates
  thirdCoordinates := Q.secondCoordinates

private def FactorChart.cba {p : Profile} (Q : FactorChart p U V W) :
    FactorChart ⟨p.third, p.second, p.first⟩ W V U where
  firstSpan := Q.thirdSpan
  secondSpan := Q.secondSpan
  thirdSpan := Q.firstSpan
  firstCoordinates := Q.thirdCoordinates
  secondCoordinates := Q.secondCoordinates
  thirdCoordinates := Q.firstCoordinates

private def FactorChart.bac {p : Profile} (Q : FactorChart p U V W) :
    FactorChart ⟨p.second, p.first, p.third⟩ V U W where
  firstSpan := Q.secondSpan
  secondSpan := Q.firstSpan
  thirdSpan := Q.thirdSpan
  firstCoordinates := Q.secondCoordinates
  secondCoordinates := Q.firstCoordinates
  thirdCoordinates := Q.thirdCoordinates

private theorem FactorChart.normalize_permuteBCA {p : Profile}
    (Q : FactorChart p U V W) (D : BinaryAmbientCarrier.State W U V) :
    Q.normalize (permuteBCAState D) = permuteBCAState (Q.bca.normalize D) := by
  ext s
  rcases s with ⟨x, y, z⟩
  let r : NormalizedBinaryCarrier.Carrier ⟨p.third, p.first, p.second⟩ := (z, x, y)
  have hcompat : permuteBCATerm (mapTerm Q.bca.embedding r) =
      mapTerm Q.embedding (x, y, z) := rfl
  constructor
  · intro hs
    have hmapped := (Q.mem_normalize_iff (permuteBCAState D) (x, y, z)).mp hs
    rcases Finset.mem_image.mp hmapped with ⟨t, htD, ht⟩
    have htr : t = mapTerm Q.bca.embedding r := by
      apply permuteBCATerm_injective
      rw [ht, hcompat]
    apply Finset.mem_image.mpr
    refine ⟨r, (Q.bca.mem_normalize_iff D r).mpr ?_, rfl⟩
    rwa [← htr]
  · intro hs
    rcases Finset.mem_image.mp hs with ⟨t, ht, hts⟩
    have htD := (Q.bca.mem_normalize_iff D t).mp ht
    apply (Q.mem_normalize_iff (permuteBCAState D) (x, y, z)).mpr
    apply Finset.mem_image.mpr
    refine ⟨mapTerm Q.bca.embedding t, htD, ?_⟩
    calc
      permuteBCATerm (mapTerm Q.bca.embedding t) =
          mapTerm Q.embedding (permuteBCATerm t) := by
            rcases t with ⟨tx, ty, tz⟩
            rfl
      _ = mapTerm Q.embedding (x, y, z) := congrArg (mapTerm Q.embedding) hts

private theorem FactorChart.normalize_permuteCAB {p : Profile}
    (Q : FactorChart p U V W) (D : BinaryAmbientCarrier.State V W U) :
    Q.normalize (permuteCABState D) = permuteCABState (Q.cab.normalize D) := by
  ext s
  rcases s with ⟨x, y, z⟩
  let r : NormalizedBinaryCarrier.Carrier ⟨p.second, p.third, p.first⟩ := (y, z, x)
  have hcompat : permuteCABTerm (mapTerm Q.cab.embedding r) =
      mapTerm Q.embedding (x, y, z) := rfl
  constructor
  · intro hs
    have hmapped := (Q.mem_normalize_iff (permuteCABState D) (x, y, z)).mp hs
    rcases Finset.mem_image.mp hmapped with ⟨t, htD, ht⟩
    have htr : t = mapTerm Q.cab.embedding r := by
      apply permuteCABTerm_injective
      rw [ht, hcompat]
    apply Finset.mem_image.mpr
    refine ⟨r, (Q.cab.mem_normalize_iff D r).mpr ?_, rfl⟩
    rwa [← htr]
  · intro hs
    rcases Finset.mem_image.mp hs with ⟨t, ht, hts⟩
    have htD := (Q.cab.mem_normalize_iff D t).mp ht
    apply (Q.mem_normalize_iff (permuteCABState D) (x, y, z)).mpr
    apply Finset.mem_image.mpr
    refine ⟨mapTerm Q.cab.embedding t, htD, ?_⟩
    calc
      permuteCABTerm (mapTerm Q.cab.embedding t) =
          mapTerm Q.embedding (permuteCABTerm t) := by
            rcases t with ⟨tx, ty, tz⟩
            rfl
      _ = mapTerm Q.embedding (x, y, z) := congrArg (mapTerm Q.embedding) hts

private theorem FactorChart.normalize_permuteACB {p : Profile}
    (Q : FactorChart p U V W) (D : BinaryAmbientCarrier.State U W V) :
    Q.normalize (permuteACBState D) = permuteACBState (Q.acb.normalize D) := by
  ext s
  rcases s with ⟨x, y, z⟩
  let r : NormalizedBinaryCarrier.Carrier ⟨p.first, p.third, p.second⟩ := (x, z, y)
  have hcompat : permuteACBTerm (mapTerm Q.acb.embedding r) =
      mapTerm Q.embedding (x, y, z) := rfl
  constructor
  · intro hs
    have hmapped := (Q.mem_normalize_iff (permuteACBState D) (x, y, z)).mp hs
    rcases Finset.mem_image.mp hmapped with ⟨t, htD, ht⟩
    have htr : t = mapTerm Q.acb.embedding r := by
      apply permuteACBTerm_injective
      rw [ht, hcompat]
    apply Finset.mem_image.mpr
    refine ⟨r, (Q.acb.mem_normalize_iff D r).mpr ?_, rfl⟩
    rwa [← htr]
  · intro hs
    rcases Finset.mem_image.mp hs with ⟨t, ht, hts⟩
    have htD := (Q.acb.mem_normalize_iff D t).mp ht
    apply (Q.mem_normalize_iff (permuteACBState D) (x, y, z)).mpr
    apply Finset.mem_image.mpr
    refine ⟨mapTerm Q.acb.embedding t, htD, ?_⟩
    calc
      permuteACBTerm (mapTerm Q.acb.embedding t) =
          mapTerm Q.embedding (permuteACBTerm t) := by
            rcases t with ⟨tx, ty, tz⟩
            rfl
      _ = mapTerm Q.embedding (x, y, z) := congrArg (mapTerm Q.embedding) hts

private theorem FactorChart.normalize_permuteCBA {p : Profile}
    (Q : FactorChart p U V W) (D : BinaryAmbientCarrier.State W V U) :
    Q.normalize (permuteCBAState D) = permuteCBAState (Q.cba.normalize D) := by
  ext s
  rcases s with ⟨x, y, z⟩
  let r : NormalizedBinaryCarrier.Carrier ⟨p.third, p.second, p.first⟩ := (z, y, x)
  have hcompat : permuteCBATerm (mapTerm Q.cba.embedding r) =
      mapTerm Q.embedding (x, y, z) := rfl
  constructor
  · intro hs
    have hmapped := (Q.mem_normalize_iff (permuteCBAState D) (x, y, z)).mp hs
    rcases Finset.mem_image.mp hmapped with ⟨t, htD, ht⟩
    have htr : t = mapTerm Q.cba.embedding r := by
      apply permuteCBATerm_injective
      rw [ht, hcompat]
    apply Finset.mem_image.mpr
    refine ⟨r, (Q.cba.mem_normalize_iff D r).mpr ?_, rfl⟩
    rwa [← htr]
  · intro hs
    rcases Finset.mem_image.mp hs with ⟨t, ht, hts⟩
    have htD := (Q.cba.mem_normalize_iff D t).mp ht
    apply (Q.mem_normalize_iff (permuteCBAState D) (x, y, z)).mpr
    apply Finset.mem_image.mpr
    refine ⟨mapTerm Q.cba.embedding t, htD, ?_⟩
    calc
      permuteCBATerm (mapTerm Q.cba.embedding t) =
          mapTerm Q.embedding (permuteCBATerm t) := by
            rcases t with ⟨tx, ty, tz⟩
            rfl
      _ = mapTerm Q.embedding (x, y, z) := congrArg (mapTerm Q.embedding) hts

private theorem FactorChart.normalize_permuteBAC {p : Profile}
    (Q : FactorChart p U V W) (D : BinaryAmbientCarrier.State V U W) :
    Q.normalize (permuteBACState D) = permuteBACState (Q.bac.normalize D) := by
  ext s
  rcases s with ⟨x, y, z⟩
  let r : NormalizedBinaryCarrier.Carrier ⟨p.second, p.first, p.third⟩ := (y, x, z)
  have hcompat : permuteBACTerm (mapTerm Q.bac.embedding r) =
      mapTerm Q.embedding (x, y, z) := rfl
  constructor
  · intro hs
    have hmapped := (Q.mem_normalize_iff (permuteBACState D) (x, y, z)).mp hs
    rcases Finset.mem_image.mp hmapped with ⟨t, htD, ht⟩
    have htr : t = mapTerm Q.bac.embedding r := by
      apply permuteBACTerm_injective
      rw [ht, hcompat]
    apply Finset.mem_image.mpr
    refine ⟨r, (Q.bac.mem_normalize_iff D r).mpr ?_, rfl⟩
    rwa [← htr]
  · intro hs
    rcases Finset.mem_image.mp hs with ⟨t, ht, hts⟩
    have htD := (Q.bac.mem_normalize_iff D t).mp ht
    apply (Q.mem_normalize_iff (permuteBACState D) (x, y, z)).mpr
    apply Finset.mem_image.mpr
    refine ⟨mapTerm Q.bac.embedding t, htD, ?_⟩
    calc
      permuteBACTerm (mapTerm Q.bac.embedding t) =
          mapTerm Q.embedding (permuteBACTerm t) := by
            rcases t with ⟨tx, ty, tz⟩
            rfl
      _ = mapTerm Q.embedding (x, y, z) := congrArg (mapTerm Q.embedding) hts

private theorem support_bca {p : Profile} (Q : FactorChart p U V W)
    {X Y : BinaryAmbientCarrier.State U V W}
    {D E : BinaryAmbientCarrier.State W U V}
    (hX : X = permuteBCAState D) (hY : Y = permuteBCAState E)
    (hsupport : X ∆ Y ⊆ Q.box) : D ∆ E ⊆ Q.bca.box := by
  intro t ht
  have htperm : permuteBCATerm t ∈ X ∆ Y := by
    rw [hX, hY]
    change permuteBCATerm t ∈ D.image permuteBCATerm ∆ E.image permuteBCATerm
    rw [← Finset.image_symmDiff D E permuteBCATerm_injective]
    exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
  obtain ⟨hfirst, hsecond, hthird⟩ :=
    (Q.mem_box_iff (permuteBCATerm t)).mp (hsupport htperm)
  exact (Q.bca.mem_box_iff t).mpr ⟨hthird, hfirst, hsecond⟩

private theorem support_cab {p : Profile} (Q : FactorChart p U V W)
    {X Y : BinaryAmbientCarrier.State U V W}
    {D E : BinaryAmbientCarrier.State V W U}
    (hX : X = permuteCABState D) (hY : Y = permuteCABState E)
    (hsupport : X ∆ Y ⊆ Q.box) : D ∆ E ⊆ Q.cab.box := by
  intro t ht
  have htperm : permuteCABTerm t ∈ X ∆ Y := by
    rw [hX, hY]
    change permuteCABTerm t ∈ D.image permuteCABTerm ∆ E.image permuteCABTerm
    rw [← Finset.image_symmDiff D E permuteCABTerm_injective]
    exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
  obtain ⟨hfirst, hsecond, hthird⟩ :=
    (Q.mem_box_iff (permuteCABTerm t)).mp (hsupport htperm)
  exact (Q.cab.mem_box_iff t).mpr ⟨hsecond, hthird, hfirst⟩

private theorem support_acb {p : Profile} (Q : FactorChart p U V W)
    {X Y : BinaryAmbientCarrier.State U V W}
    {D E : BinaryAmbientCarrier.State U W V}
    (hX : X = permuteACBState D) (hY : Y = permuteACBState E)
    (hsupport : X ∆ Y ⊆ Q.box) : D ∆ E ⊆ Q.acb.box := by
  intro t ht
  have htperm : permuteACBTerm t ∈ X ∆ Y := by
    rw [hX, hY]
    change permuteACBTerm t ∈ D.image permuteACBTerm ∆ E.image permuteACBTerm
    rw [← Finset.image_symmDiff D E permuteACBTerm_injective]
    exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
  obtain ⟨hfirst, hsecond, hthird⟩ :=
    (Q.mem_box_iff (permuteACBTerm t)).mp (hsupport htperm)
  exact (Q.acb.mem_box_iff t).mpr ⟨hfirst, hthird, hsecond⟩

private theorem support_cba {p : Profile} (Q : FactorChart p U V W)
    {X Y : BinaryAmbientCarrier.State U V W}
    {D E : BinaryAmbientCarrier.State W V U}
    (hX : X = permuteCBAState D) (hY : Y = permuteCBAState E)
    (hsupport : X ∆ Y ⊆ Q.box) : D ∆ E ⊆ Q.cba.box := by
  intro t ht
  have htperm : permuteCBATerm t ∈ X ∆ Y := by
    rw [hX, hY]
    change permuteCBATerm t ∈ D.image permuteCBATerm ∆ E.image permuteCBATerm
    rw [← Finset.image_symmDiff D E permuteCBATerm_injective]
    exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
  obtain ⟨hfirst, hsecond, hthird⟩ :=
    (Q.mem_box_iff (permuteCBATerm t)).mp (hsupport htperm)
  exact (Q.cba.mem_box_iff t).mpr ⟨hthird, hsecond, hfirst⟩

private theorem support_bac {p : Profile} (Q : FactorChart p U V W)
    {X Y : BinaryAmbientCarrier.State U V W}
    {D E : BinaryAmbientCarrier.State V U W}
    (hX : X = permuteBACState D) (hY : Y = permuteBACState E)
    (hsupport : X ∆ Y ⊆ Q.box) : D ∆ E ⊆ Q.bac.box := by
  intro t ht
  have htperm : permuteBACTerm t ∈ X ∆ Y := by
    rw [hX, hY]
    change permuteBACTerm t ∈ D.image permuteBACTerm ∆ E.image permuteBACTerm
    rw [← Finset.image_symmDiff D E permuteBACTerm_injective]
    exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
  obtain ⟨hfirst, hsecond, hthird⟩ :=
    (Q.mem_box_iff (permuteBACTerm t)).mp (hsupport htperm)
  exact (Q.bac.mem_box_iff t).mpr ⟨hsecond, hfirst, hthird⟩

private theorem allModeMove_pullback {p : Profile} (Q : FactorChart p U V W)
    {X Y : BinaryAmbientCarrier.State U V W}
    (h : BinaryAmbientMoves.AllModeMove X Y) (hsupport : X ∆ Y ⊆ Q.box) :
    BinaryAmbientMoves.AllModeMove
      (U := CoordinateVector p.first) (V := CoordinateVector p.second)
      (W := CoordinateVector p.third) (Q.normalize X) (Q.normalize Y) := by
  cases h with
  | abc hmove =>
      exact .abc (move_pullback Q hmove hsupport)
  | bca hmove hX hY =>
      refine .bca (move_pullback Q.bca hmove (support_bca Q hX hY hsupport)) ?_ ?_
      · exact (congrArg Q.normalize hX).trans (Q.normalize_permuteBCA _)
      · exact (congrArg Q.normalize hY).trans (Q.normalize_permuteBCA _)
  | cab hmove hX hY =>
      refine .cab (move_pullback Q.cab hmove (support_cab Q hX hY hsupport)) ?_ ?_
      · exact (congrArg Q.normalize hX).trans (Q.normalize_permuteCAB _)
      · exact (congrArg Q.normalize hY).trans (Q.normalize_permuteCAB _)
  | acb hmove hX hY =>
      refine .acb (move_pullback Q.acb hmove (support_acb Q hX hY hsupport)) ?_ ?_
      · exact (congrArg Q.normalize hX).trans (Q.normalize_permuteACB _)
      · exact (congrArg Q.normalize hY).trans (Q.normalize_permuteACB _)
  | cba hmove hX hY =>
      refine .cba (move_pullback Q.cba hmove (support_cba Q hX hY hsupport)) ?_ ?_
      · exact (congrArg Q.normalize hX).trans (Q.normalize_permuteCBA _)
      · exact (congrArg Q.normalize hY).trans (Q.normalize_permuteCBA _)
  | bac hmove hX hY =>
      refine .bac (move_pullback Q.bac hmove (support_bac Q hX hY hsupport)) ?_ ?_
      · exact (congrArg Q.normalize hX).trans (Q.normalize_permuteBAC _)
      · exact (congrArg Q.normalize hY).trans (Q.normalize_permuteBAC _)

/-- An ambient all-mode edge supported in the exact-span local box reflects
into the supplied executable normalized coordinates, with the same direction. -/
theorem allModeMove_normalizeLocalContext
    {A B X Y : BinaryAmbientCarrier.State U V W}
    (P : ExactSpanPresentation A B)
    (h : BinaryAmbientMoves.AllModeMove X Y)
    (hsupport : X ∆ Y ⊆ localBox P) :
    @NormalizedBinaryAllModeMove.AllModeMove P.profile
      (normalizeLocalContext P X) (normalizeLocalContext P Y) := by
  apply BinaryAmbientMoves.Coordinate.allModeMove_iff_normalized.mp
  exact allModeMove_pullback (presentationChart P) h
    (by simpa only [presentationChart_box] using hsupport)

private theorem left_subset_localBox
    {A B : BinaryAmbientCarrier.State U V W}
    (P : ExactSpanPresentation A B) : A ⊆ localBox P := by
  intro t ht
  rw [localBox_eq_mapState]
  rw [← mapState_normalizedLeft P] at ht
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
  exact Finset.mem_image.mpr ⟨s, mem_normalizedBox s, rfl⟩

private theorem right_subset_localBox
    {A B : BinaryAmbientCarrier.State U V W}
    (P : ExactSpanPresentation A B) : B ⊆ localBox P := by
  intro t ht
  rw [localBox_eq_mapState]
  rw [← mapState_normalizedRight P] at ht
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
  exact Finset.mem_image.mpr ⟨s, mem_normalizedBox s, rfl⟩

/-- Normalizing a context unioned with the left endpoint is exactly the union
of the normalized context and the normalized left endpoint. -/
@[simp] theorem normalizeLocalContext_union_left
    {A B : BinaryAmbientCarrier.State U V W}
    (P : ExactSpanPresentation A B) (C : BinaryAmbientCarrier.State U V W) :
    normalizeLocalContext P (C ∪ A) =
      normalizeLocalContext P C ∪ normalizedLeft P := by
  apply (presentationChart P).mapState_injective
  change mapState (exactSpanCoordinateEmbedding P)
      (normalizeLocalContext P (C ∪ A)) =
    mapState (exactSpanCoordinateEmbedding P)
      (normalizeLocalContext P C ∪ normalizedLeft P)
  rw [mapState_union, mapState_normalizedLeft]
  change mapState (presentationChart P).embedding
      ((presentationChart P).normalize (C ∪ A)) = _
  rw [(presentationChart P).mapState_normalize,
    mapState_normalizeLocalContext]
  ext t
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨htC | htA, htBox⟩
    · exact Or.inl ⟨htC, htBox⟩
    · exact Or.inr htA
  · rintro (⟨htC, htBox⟩ | htA)
    · exact ⟨Or.inl htC, htBox⟩
    · exact ⟨Or.inr htA, left_subset_localBox P htA⟩

/-- Normalizing a context unioned with the right endpoint is exactly the union
of the normalized context and the normalized right endpoint. -/
@[simp] theorem normalizeLocalContext_union_right
    {A B : BinaryAmbientCarrier.State U V W}
    (P : ExactSpanPresentation A B) (C : BinaryAmbientCarrier.State U V W) :
    normalizeLocalContext P (C ∪ B) =
      normalizeLocalContext P C ∪ normalizedRight P := by
  apply (presentationChart P).mapState_injective
  change mapState (exactSpanCoordinateEmbedding P)
      (normalizeLocalContext P (C ∪ B)) =
    mapState (exactSpanCoordinateEmbedding P)
      (normalizeLocalContext P C ∪ normalizedRight P)
  rw [mapState_union, mapState_normalizedRight]
  change mapState (presentationChart P).embedding
      ((presentationChart P).normalize (C ∪ B)) = _
  rw [(presentationChart P).mapState_normalize,
    mapState_normalizeLocalContext]
  ext t
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨htC | htB, htBox⟩
    · exact Or.inl ⟨htC, htBox⟩
    · exact Or.inr htB
  · rintro (⟨htC, htBox⟩ | htB)
    · exact ⟨Or.inl htC, htBox⟩
    · exact ⟨Or.inr htB, right_subset_localBox P htB⟩

#check @allModeMove_normalizeLocalContext
#check @normalizeLocalContext_union_left
#check @normalizeLocalContext_union_right

#print axioms allModeMove_normalizeLocalContext
#print axioms normalizeLocalContext_union_left
#print axioms normalizeLocalContext_union_right

end BilinearComplexity.BinaryAmbientContextReflection
