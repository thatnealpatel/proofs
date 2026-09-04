import BilinearComplexity.FiveCircuit

set_option autoImplicit false

/-!
# Profile-polymorphic normalized binary moves and profile-221 replay

This module defines the profile-polymorphic finite-set predicates for the three
move labels used here, together with their evaluation, cardinality, and path
infrastructure. It then uses those predicates to replay one designated path in
the normalized `(2,2,1)` carrier. The labels remain separate: an
implementation-generated first-factor Split, a source ordinary third-factor
Flip, and a directed narrow two-to-one Reduction.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.NormalizedBinaryReplay221

open NormalizedBinaryCarrier
open BinaryCircuit
open scoped BigOperators

/-- A normalized carrier term for the ordered binary profile `(2,2,1)`. -/
abbrev Term := Carrier profile221

/-- A squarefree finite-set state in the ordered binary profile `(2,2,1)`. -/
abbrev State221 := State profile221

/-- The first standard basis vector `(1,0)` of `F2²`. -/
def e1 : NonzeroVector 2 := ⟨![1, 0], by decide⟩

/-- The second standard basis vector `(0,1)` of `F2²`. -/
def e2 : NonzeroVector 2 := ⟨![0, 1], by decide⟩

/-- The third nonzero vector `(1,1)` of `F2²`. -/
def ep : NonzeroVector 2 := ⟨![1, 1], by decide⟩

/-- The unique nonzero vector `(1)` of `F2¹`. -/
def w : NonzeroVector 1 := ⟨![1], by decide⟩

/-- The carrier term `(e1,e1,w)`. -/
def E11 : Term := (e1, e1, w)

/-- The carrier term `(e1,e2,w)`. -/
def E12 : Term := (e1, e2, w)

/-- The carrier term `(e2,e1,w)`. -/
def E21 : Term := (e2, e1, w)

/-- The carrier term `(e2,e2,w)`. -/
def E22 : Term := (e2, e2, w)

/-- The carrier term `(ep,e1,w)`. -/
def E31 : Term := (ep, e1, w)

/-- The carrier term `(ep,ep,w)`. -/
def J : Term := (ep, ep, w)

/-- A legal implementation-generated first-factor Split replaces one present
term by two distinct fresh terms, sharing the other factors, whose first
factors sum to the source first factor. The target is required to be the exact
finite-set replacement. -/
def GeneratedFirstSplit {p : Profile}
    (source outputLeft outputRight : Carrier p) (D E : State p) : Prop :=
    source ∈ D ∧
    outputLeft ≠ outputRight ∧
    outputLeft ∉ D.erase source ∧
    outputRight ∉ D.erase source ∧
    source.1.1 = outputLeft.1.1 + outputRight.1.1 ∧
    outputLeft.2.1.1 = source.2.1.1 ∧
    outputRight.2.1.1 = source.2.1.1 ∧
    outputLeft.2.2.1 = source.2.2.1 ∧
    outputRight.2.2.1 = source.2.2.1 ∧
    E = insert outputLeft (insert outputRight (D.erase source))

/-- A legal source ordinary Flip in the third-factor mode replaces an ordered
present pair by the displayed unit shear. The pair literally shares its third
factor, both outputs are collision-free, and the target is the exact finite-set
replacement. -/
def SourceThirdFlip {p : Profile}
    (sourceLeft sourceRight targetLeft targetRight : Carrier p)
    (D E : State p) : Prop :=
    sourceLeft ∈ D ∧
    sourceRight ∈ D ∧
    sourceLeft ≠ sourceRight ∧
    targetLeft ∉ (D.erase sourceLeft).erase sourceRight ∧
    targetRight ∉ (D.erase sourceLeft).erase sourceRight ∧
    targetLeft ≠ targetRight ∧
    sourceRight.2.2.1 = sourceLeft.2.2.1 ∧
    targetLeft.1.1 = sourceLeft.1.1 + sourceRight.1.1 ∧
    targetLeft.2.1.1 = sourceLeft.2.1.1 ∧
    targetLeft.2.2.1 = sourceLeft.2.2.1 ∧
    targetRight.1.1 = sourceRight.1.1 ∧
    targetRight.2.1.1 = sourceRight.2.1.1 - sourceLeft.2.1.1 ∧
    targetRight.2.2.1 = sourceLeft.2.2.1 ∧
    E = insert targetLeft
      (insert targetRight ((D.erase sourceLeft).erase sourceRight))

/-- A legal directed narrow pair Reduction replaces two distinct present terms
sharing their second and third factors by one fresh term whose first factor is
their sum. This is only the displayed two-to-one template, not a claim that all
KM Reduction instances have this form. -/
def DirectedNarrowPairReduction {p : Profile}
    (sourceLeft sourceRight target : Carrier p) (D E : State p) : Prop :=
    sourceLeft ∈ D ∧
    sourceRight ∈ D ∧
    sourceLeft ≠ sourceRight ∧
    target ∉ (D.erase sourceLeft).erase sourceRight ∧
    sourceRight.2.1.1 = sourceLeft.2.1.1 ∧
    sourceRight.2.2.1 = sourceLeft.2.2.1 ∧
    target.1.1 = sourceLeft.1.1 + sourceRight.1.1 ∧
    target.2.1.1 = sourceLeft.2.1.1 ∧
    target.2.2.1 = sourceLeft.2.2.1 ∧
    E = insert target ((D.erase sourceLeft).erase sourceRight)

private theorem generatedFirstSplit_local_eq {p : Profile}
    (source outputLeft outputRight : Carrier p)
    (hfirst : source.1.1 = outputLeft.1.1 + outputRight.1.1)
    (hleftSecond : outputLeft.2.1.1 = source.2.1.1)
    (hrightSecond : outputRight.2.1.1 = source.2.1.1)
    (hleftThird : outputLeft.2.2.1 = source.2.2.1)
    (hrightThird : outputRight.2.2.1 = source.2.2.1) :
    tensorEvaluation source =
      tensorEvaluation outputLeft + tensorEvaluation outputRight := by
  funext i j k
  change source.1.1 i * source.2.1.1 j * source.2.2.1 k =
    outputLeft.1.1 i * outputLeft.2.1.1 j * outputLeft.2.2.1 k +
      outputRight.1.1 i * outputRight.2.1.1 j * outputRight.2.2.1 k
  rw [congrFun hfirst i, congrFun hleftSecond j, congrFun hrightSecond j,
    congrFun hleftThird k, congrFun hrightThird k]
  simp only [Pi.add_apply]
  ring

private theorem sourceThirdFlip_local_eq {p : Profile}
    (sourceLeft sourceRight targetLeft targetRight : Carrier p)
    (hsourceThird : sourceRight.2.2.1 = sourceLeft.2.2.1)
    (htargetLeftFirst : targetLeft.1.1 = sourceLeft.1.1 + sourceRight.1.1)
    (htargetLeftSecond : targetLeft.2.1.1 = sourceLeft.2.1.1)
    (htargetLeftThird : targetLeft.2.2.1 = sourceLeft.2.2.1)
    (htargetRightFirst : targetRight.1.1 = sourceRight.1.1)
    (htargetRightSecond :
      targetRight.2.1.1 = sourceRight.2.1.1 - sourceLeft.2.1.1)
    (htargetRightThird : targetRight.2.2.1 = sourceLeft.2.2.1) :
    tensorEvaluation sourceLeft + tensorEvaluation sourceRight =
      tensorEvaluation targetLeft + tensorEvaluation targetRight := by
  funext i j k
  change
    sourceLeft.1.1 i * sourceLeft.2.1.1 j * sourceLeft.2.2.1 k +
      sourceRight.1.1 i * sourceRight.2.1.1 j * sourceRight.2.2.1 k =
    targetLeft.1.1 i * targetLeft.2.1.1 j * targetLeft.2.2.1 k +
      targetRight.1.1 i * targetRight.2.1.1 j * targetRight.2.2.1 k
  rw [congrFun hsourceThird k, congrFun htargetLeftFirst i,
    congrFun htargetLeftSecond j, congrFun htargetLeftThird k,
    congrFun htargetRightFirst i, congrFun htargetRightSecond j,
    congrFun htargetRightThird k]
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

private theorem directedNarrowPairReduction_local_eq {p : Profile}
    (sourceLeft sourceRight target : Carrier p)
    (hsecond : sourceRight.2.1.1 = sourceLeft.2.1.1)
    (hthird : sourceRight.2.2.1 = sourceLeft.2.2.1)
    (htargetFirst : target.1.1 = sourceLeft.1.1 + sourceRight.1.1)
    (htargetSecond : target.2.1.1 = sourceLeft.2.1.1)
    (htargetThird : target.2.2.1 = sourceLeft.2.2.1) :
    tensorEvaluation sourceLeft + tensorEvaluation sourceRight =
      tensorEvaluation target := by
  funext i j k
  change
    sourceLeft.1.1 i * sourceLeft.2.1.1 j * sourceLeft.2.2.1 k +
      sourceRight.1.1 i * sourceRight.2.1.1 j * sourceRight.2.2.1 k =
    target.1.1 i * target.2.1.1 j * target.2.2.1 k
  rw [congrFun hsecond j, congrFun hthird k, congrFun htargetFirst i,
    congrFun htargetSecond j, congrFun htargetThird k]
  simp only [Pi.add_apply]
  ring

private lemma replace_one_by_two_evaluation {p : Profile}
    (D E : State p) (x y z : Carrier p)
    (hx : x ∈ D) (hy : y ∉ D.erase x) (hz : z ∉ D.erase x)
    (hyz : y ≠ z)
    (hlocal : tensorEvaluation x = tensorEvaluation y + tensorEvaluation z)
    (hE : E = insert y (insert z (D.erase x))) :
    stateEvaluation E = stateEvaluation D := by
  rw [hE]
  simp only [stateEvaluation, BinaryCircuit.evaluation]
  have hyInsert : y ∉ insert z (D.erase x) := by
    simpa only [Finset.mem_insert, not_or] using ⟨hyz, hy⟩
  rw [Finset.sum_insert hyInsert]
  rw [Finset.sum_insert hz]
  rw [← Finset.sum_erase_add _ _ hx]
  rw [hlocal]
  ac_rfl

private lemma replace_two_by_two_evaluation {p : Profile}
    (D E : State p) (x y x' y' : Carrier p)
    (hx : x ∈ D) (hy : y ∈ D) (hxy : x ≠ y)
    (hx' : x' ∉ (D.erase x).erase y) (hy' : y' ∉ (D.erase x).erase y)
    (hx'y' : x' ≠ y')
    (hlocal : tensorEvaluation x + tensorEvaluation y =
      tensorEvaluation x' + tensorEvaluation y')
    (hE : E = insert x' (insert y' ((D.erase x).erase y))) :
    stateEvaluation E = stateEvaluation D := by
  rw [hE]
  simp only [stateEvaluation, BinaryCircuit.evaluation]
  have hx'Insert : x' ∉ insert y' ((D.erase x).erase y) := by
    simpa only [Finset.mem_insert, not_or] using ⟨hx'y', hx'⟩
  rw [Finset.sum_insert hx'Insert]
  rw [Finset.sum_insert hy']
  have hyErase : y ∈ D.erase x := Finset.mem_erase.mpr ⟨hxy.symm, hy⟩
  rw [← Finset.sum_erase_add _ _ hx]
  rw [← Finset.sum_erase_add _ _ hyErase]
  calc
    tensorEvaluation x' + (tensorEvaluation y' +
        ∑ t ∈ (D.erase x).erase y, tensorEvaluation t) =
        (tensorEvaluation x' + tensorEvaluation y') +
          ∑ t ∈ (D.erase x).erase y, tensorEvaluation t := by ac_rfl
    _ = (tensorEvaluation x + tensorEvaluation y) +
          ∑ t ∈ (D.erase x).erase y, tensorEvaluation t := by rw [hlocal]
    _ = ∑ t ∈ (D.erase x).erase y, tensorEvaluation t +
          tensorEvaluation y + tensorEvaluation x := by ac_rfl

private lemma replace_two_by_one_evaluation {p : Profile}
    (D E : State p) (x y z : Carrier p)
    (hx : x ∈ D) (hy : y ∈ D) (hxy : x ≠ y)
    (hz : z ∉ (D.erase x).erase y)
    (hlocal : tensorEvaluation x + tensorEvaluation y = tensorEvaluation z)
    (hE : E = insert z ((D.erase x).erase y)) :
    stateEvaluation E = stateEvaluation D := by
  rw [hE]
  simp only [stateEvaluation, BinaryCircuit.evaluation]
  rw [Finset.sum_insert hz]
  have hyErase : y ∈ D.erase x := Finset.mem_erase.mpr ⟨hxy.symm, hy⟩
  rw [← Finset.sum_erase_add _ _ hx]
  rw [← Finset.sum_erase_add _ _ hyErase]
  calc
    tensorEvaluation z + ∑ t ∈ (D.erase x).erase y, tensorEvaluation t =
        (tensorEvaluation x + tensorEvaluation y) +
          ∑ t ∈ (D.erase x).erase y, tensorEvaluation t := by rw [hlocal]
    _ = ∑ t ∈ (D.erase x).erase y, tensorEvaluation t +
          tensorEvaluation y + tensorEvaluation x := by ac_rfl

/-- Every legal implementation-generated first-factor Split preserves state evaluation. -/
theorem GeneratedFirstSplit.preserves_evaluation {p : Profile}
    {source outputLeft outputRight : Carrier p} {D E : State p}
    (h : GeneratedFirstSplit source outputLeft outputRight D E) :
    stateEvaluation E = stateEvaluation D := by
  rcases h with ⟨hmem, hne, hfreshLeft, hfreshRight, hfirst, hleftSecond,
    hrightSecond, hleftThird, hrightThird, htarget⟩
  exact replace_one_by_two_evaluation D E source outputLeft outputRight hmem
    hfreshLeft hfreshRight hne
    (generatedFirstSplit_local_eq source outputLeft outputRight hfirst
      hleftSecond hrightSecond hleftThird hrightThird) htarget

/-- Every legal source third-factor Flip preserves state evaluation. -/
theorem SourceThirdFlip.preserves_evaluation {p : Profile}
    {sourceLeft sourceRight targetLeft targetRight : Carrier p} {D E : State p}
    (h : SourceThirdFlip sourceLeft sourceRight targetLeft targetRight D E) :
    stateEvaluation E = stateEvaluation D := by
  rcases h with ⟨hleftMem, hrightMem, hsources, hfreshLeft, hfreshRight,
    htargets, hsourceThird, htargetLeftFirst, htargetLeftSecond,
    htargetLeftThird, htargetRightFirst, htargetRightSecond, htargetRightThird,
    htarget⟩
  exact replace_two_by_two_evaluation D E sourceLeft sourceRight targetLeft
    targetRight hleftMem hrightMem hsources hfreshLeft hfreshRight htargets
    (sourceThirdFlip_local_eq sourceLeft sourceRight targetLeft targetRight
      hsourceThird htargetLeftFirst htargetLeftSecond htargetLeftThird
      htargetRightFirst htargetRightSecond htargetRightThird) htarget

/-- Every legal directed narrow pair Reduction preserves state evaluation. -/
theorem DirectedNarrowPairReduction.preserves_evaluation {p : Profile}
    {sourceLeft sourceRight target : Carrier p} {D E : State p}
    (h : DirectedNarrowPairReduction sourceLeft sourceRight target D E) :
    stateEvaluation E = stateEvaluation D := by
  rcases h with ⟨hleftMem, hrightMem, hsources, hfresh, hsecond, hthird,
    htargetFirst, htargetSecond, htargetThird, htarget⟩
  exact replace_two_by_one_evaluation D E sourceLeft sourceRight target hleftMem
    hrightMem hsources hfresh
    (directedNarrowPairReduction_local_eq sourceLeft sourceRight target hsecond
      hthird htargetFirst htargetSecond htargetThird) htarget

/-- A legal implementation-generated first-factor Split increases finite-set
cardinality by exactly one. -/
theorem GeneratedFirstSplit.card_eq {p : Profile}
    {source outputLeft outputRight : Carrier p} {D E : State p}
    (h : GeneratedFirstSplit source outputLeft outputRight D E) :
    E.card = D.card + 1 := by
  rcases h with ⟨hmem, hne, hfreshLeft, hfreshRight, _hfirst, _hleftSecond,
    _hrightSecond, _hleftThird, _hrightThird, htarget⟩
  have hleft : outputLeft ∉ insert outputRight (D.erase source) := by
    simpa only [Finset.mem_insert, not_or] using ⟨hne, hfreshLeft⟩
  rw [htarget, Finset.card_insert_of_notMem hleft,
    Finset.card_insert_of_notMem hfreshRight]
  have herase := Finset.card_erase_add_one hmem
  omega

/-- A legal source third-factor Flip preserves finite-set cardinality exactly. -/
theorem SourceThirdFlip.card_eq {p : Profile}
    {sourceLeft sourceRight targetLeft targetRight : Carrier p} {D E : State p}
    (h : SourceThirdFlip sourceLeft sourceRight targetLeft targetRight D E) :
    E.card = D.card := by
  rcases h with ⟨hleftMem, hrightMem, hsources, hfreshLeft, hfreshRight,
    htargets, _hsourceThird, _htargetLeftFirst, _htargetLeftSecond,
    _htargetLeftThird, _htargetRightFirst, _htargetRightSecond,
    _htargetRightThird, htarget⟩
  let R := (D.erase sourceLeft).erase sourceRight
  have hleft : targetLeft ∉ insert targetRight R := by
    simpa only [Finset.mem_insert, not_or] using ⟨htargets, hfreshLeft⟩
  have hrightErase : sourceRight ∈ D.erase sourceLeft :=
    Finset.mem_erase.mpr ⟨hsources.symm, hrightMem⟩
  have heraseLeft := Finset.card_erase_add_one hleftMem
  have heraseRight := Finset.card_erase_add_one hrightErase
  rw [htarget, Finset.card_insert_of_notMem hleft,
    Finset.card_insert_of_notMem hfreshRight]
  change R.card + 1 + 1 = D.card
  dsimp only [R] at heraseRight ⊢
  omega

/-- A legal directed narrow pair Reduction decreases finite-set cardinality by
exactly one, stated additively to avoid natural-number subtraction. -/
theorem DirectedNarrowPairReduction.card_add_one_eq {p : Profile}
    {sourceLeft sourceRight target : Carrier p} {D E : State p}
    (h : DirectedNarrowPairReduction sourceLeft sourceRight target D E) :
    E.card + 1 = D.card := by
  rcases h with ⟨hleftMem, hrightMem, hsources, hfresh, _hsecond, _hthird,
    _htargetFirst, _htargetSecond, _htargetThird, htarget⟩
  have hrightErase : sourceRight ∈ D.erase sourceLeft :=
    Finset.mem_erase.mpr ⟨hsources.symm, hrightMem⟩
  have heraseLeft := Finset.card_erase_add_one hleftMem
  have heraseRight := Finset.card_erase_add_one hrightErase
  rw [htarget, Finset.card_insert_of_notMem hfresh]
  omega

/-- Every normalized finite-set state consists of nonzero evaluated tensors,
and coordinate evaluation is injective on its terms. -/
theorem state_tensor_legality {p : Profile} (D : State p) :
    (∀ t, t ∈ D → tensorEvaluation t ≠ 0) ∧
      (∀ s, s ∈ D → ∀ t, t ∈ D →
        tensorEvaluation s = tensorEvaluation t → s = t) := by
  constructor
  · intro t _ht
    exact tensorEvaluation_ne_zero t
  · intro s _hs t _ht hst
    exact tensorEvaluation_injective hst

/-- The three intrinsically directed move labels at an ordered normalized profile. -/
inductive Move {p : Profile} : State p → State p → Prop
  /-- A forward implementation-generated first-factor Split edge. -/
  | generatedFirstSplit {source outputLeft outputRight : Carrier p} {D E : State p} :
      GeneratedFirstSplit source outputLeft outputRight D E → Move D E
  /-- A source ordinary third-factor Flip edge. -/
  | sourceThirdFlip {sourceLeft sourceRight targetLeft targetRight : Carrier p}
      {D E : State p} :
      SourceThirdFlip sourceLeft sourceRight targetLeft targetRight D E → Move D E
  /-- A directed narrow two-to-one Reduction edge. -/
  | directedNarrowPairReduction {sourceLeft sourceRight target : Carrier p}
      {D E : State p} :
      DirectedNarrowPairReduction sourceLeft sourceRight target D E → Move D E

/-- Every typed replay edge preserves normalized state evaluation. -/
theorem Move.preserves_evaluation {p : Profile} {D E : State p} (h : Move D E) :
    stateEvaluation E = stateEvaluation D := by
  cases h with
  | generatedFirstSplit hsplit => exact hsplit.preserves_evaluation
  | sourceThirdFlip hflip => exact hflip.preserves_evaluation
  | directedNarrowPairReduction hreduction => exact hreduction.preserves_evaluation

/-- Every concrete path of the three typed moves preserves endpoint evaluation. -/
theorem movePath_preserves_evaluation {p : Profile} {D E : State p}
    (path : MovePath (@Move p) D E) : stateEvaluation E = stateEvaluation D := by
  induction path with
  | singleton => rfl
  | snoc _ h ih => exact h.preserves_evaluation.trans ih

/-- The two-term source state `{E11,E22}`. -/
def S0 : State221 := {E11, E22}

/-- The three-term intermediate state `{E21,E31,E22}`. -/
def S1 : State221 := {E21, E31, E22}

/-- The three-term target state `{E12,E21,J}`. -/
def S2 : State221 := {E12, E21, J}

/-- The explicit six-term boundary containing every replay vertex. -/
def boundary : State221 := {E11, E22, E21, E31, E12, J}

private theorem endpoint_first_factor_span_eq_top :
    Submodule.span F2
      (((S0 ∪ S2).image (fun t => t.1.1) : Finset (Fin 2 → F2)) :
        Set (Fin 2 → F2)) = ⊤ := by
  apply top_unique
  intro v _hv
  have he1 : e1.1 ∈ Submodule.span F2
      (((S0 ∪ S2).image (fun t => t.1.1) : Finset (Fin 2 → F2)) :
        Set (Fin 2 → F2)) := by
    apply Submodule.subset_span
    exact Finset.mem_image.mpr ⟨E11, by decide, rfl⟩
  have he2 : e2.1 ∈ Submodule.span F2
      (((S0 ∪ S2).image (fun t => t.1.1) : Finset (Fin 2 → F2)) :
        Set (Fin 2 → F2)) := by
    apply Submodule.subset_span
    exact Finset.mem_image.mpr ⟨E21, by decide, rfl⟩
  have hv : v = v 0 • e1.1 + v 1 • e2.1 := by
    funext i
    fin_cases i <;> simp [e1, e2]
  rw [hv]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ he1)
    (Submodule.smul_mem _ _ he2)

private theorem endpoint_second_factor_span_eq_top :
    Submodule.span F2
      (((S0 ∪ S2).image (fun t => t.2.1.1) : Finset (Fin 2 → F2)) :
        Set (Fin 2 → F2)) = ⊤ := by
  apply top_unique
  intro v _hv
  have he1 : e1.1 ∈ Submodule.span F2
      (((S0 ∪ S2).image (fun t => t.2.1.1) : Finset (Fin 2 → F2)) :
        Set (Fin 2 → F2)) := by
    apply Submodule.subset_span
    exact Finset.mem_image.mpr ⟨E11, by decide, rfl⟩
  have he2 : e2.1 ∈ Submodule.span F2
      (((S0 ∪ S2).image (fun t => t.2.1.1) : Finset (Fin 2 → F2)) :
        Set (Fin 2 → F2)) := by
    apply Submodule.subset_span
    exact Finset.mem_image.mpr ⟨E12, by decide, rfl⟩
  have hv : v = v 0 • e1.1 + v 1 • e2.1 := by
    funext i
    fin_cases i <;> simp [e1, e2]
  rw [hv]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ he1)
    (Submodule.smul_mem _ _ he2)

private theorem endpoint_third_factor_span_eq_top :
    Submodule.span F2
      (((S0 ∪ S2).image (fun t => t.2.2.1) : Finset (Fin 1 → F2)) :
        Set (Fin 1 → F2)) = ⊤ := by
  apply top_unique
  intro v _hv
  have hw : w.1 ∈ Submodule.span F2
      (((S0 ∪ S2).image (fun t => t.2.2.1) : Finset (Fin 1 → F2)) :
        Set (Fin 1 → F2)) := by
    apply Submodule.subset_span
    exact Finset.mem_image.mpr ⟨E11, by decide, rfl⟩
  have hv : v = v 0 • w.1 := by
    funext i
    fin_cases i
    simp [w]
  rw [hv]
  exact Submodule.smul_mem _ _ hw

/-- The first forward edge is exactly the implementation-generated first-factor
Split `E11 ↦ {E21,E31}`. -/
theorem forwardSplit : GeneratedFirstSplit E11 E21 E31 S0 S1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

/-- The second forward edge is exactly the source third-factor Flip on the
ordered pair `(E22,E31)`, producing `(E12,J)`. -/
theorem forwardFlip : SourceThirdFlip E22 E31 E12 J S1 S2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

/-- The reverse Flip is the same source-defined third-factor operation on the
ordered pair `(E12,J)`, producing `(E22,E31)`. -/
theorem reverseFlip : SourceThirdFlip E12 J E22 E31 S2 S1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

/-- The reverse second edge is the directed narrow pair Reduction
`{E21,E31} ↦ E11`; it is not a converse orientation of Reduction. -/
theorem reverseReduction : DirectedNarrowPairReduction E21 E31 E11 S1 S0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

/-- The concrete split identity is `eval(E11) = eval(E21) + eval(E31)`. -/
theorem E11_split_formula :
    tensorEvaluation E11 = tensorEvaluation E21 + tensorEvaluation E31 := by
  apply generatedFirstSplit_local_eq E11 E21 E31 <;> decide

/-- The concrete Flip identity is
`eval(E22) + eval(E31) = eval(E12) + eval(J)`. -/
theorem E22_E31_flip_formula :
    tensorEvaluation E22 + tensorEvaluation E31 =
      tensorEvaluation E12 + tensorEvaluation J := by
  apply sourceThirdFlip_local_eq E22 E31 E12 J <;> decide

/-- The forward replay follows the labeled vertices `S0 → S1 → S2`. -/
def forwardPath : MovePath Move S0 S2 :=
  .snoc (.snoc (.singleton S0) (.generatedFirstSplit forwardSplit))
    (.sourceThirdFlip forwardFlip)

/-- The reverse replay follows the source Flip and then the directed narrow
Reduction along `S2 → S1 → S0`. -/
def reversePath : MovePath Move S2 S0 :=
  .snoc (.snoc (.singleton S2) (.sourceThirdFlip reverseFlip))
    (.directedNarrowPairReduction reverseReduction)

/-- Kernel reduction exposes exactly the three forward vertices and endpoints. -/
theorem forwardPath_vertices : forwardPath.vertices = [S0, S1, S2] := by
  simp [forwardPath, MovePath.vertices]

/-- Kernel reduction exposes exactly the three reverse vertices and endpoints. -/
theorem reversePath_vertices : reversePath.vertices = [S2, S1, S0] := by
  simp [reversePath, MovePath.vertices]

/-- The three named states have exact finite-set cardinalities `2,3,3`. -/
theorem state_cardinalities : S0.card = 2 ∧ S1.card = 3 ∧ S2.card = 3 := by
  decide

/-- Both concrete paths have exactly two edges and altitude exactly three. -/
theorem path_metrics :
    forwardPath.length = 2 ∧ reversePath.length = 2 ∧
      forwardPath.altitude = 3 ∧ reversePath.altitude = 3 := by
  rcases state_cardinalities with ⟨h0, h1, h2⟩
  simp only [forwardPath, reversePath, MovePath.length, MovePath.altitude]
  rw [h0, h1, h2]
  decide

/-- Every actual vertex of either replay is confined to the explicit six-term
boundary, which is strictly larger than the endpoint union. -/
theorem paths_confined :
    (∀ X, PathVertex forwardPath X → X ⊆ boundary) ∧
      (∀ X, PathVertex reversePath X → X ⊆ boundary) ∧
      boundary.card = 6 ∧ S0 ∪ S2 ⊂ boundary := by
  constructor
  · intro X hX
    have hcases : X = S0 ∨ X = S1 ∨ X = S2 := by
      simpa only [PathVertex, forwardPath_vertices, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false] using hX
    rcases hcases with rfl | rfl | rfl <;> decide
  constructor
  · intro X hX
    have hcases : X = S2 ∨ X = S1 ∨ X = S0 := by
      simpa only [PathVertex, reversePath_vertices, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false] using hX
    rcases hcases with rfl | rfl | rfl <;> decide
  · decide

/-- Both typed path orientations prove the corresponding endpoint evaluation equality. -/
theorem endpoint_evaluations :
    stateEvaluation S2 = stateEvaluation S0 ∧
      stateEvaluation S0 = stateEvaluation S2 :=
  ⟨movePath_preserves_evaluation forwardPath,
    movePath_preserves_evaluation reversePath⟩

/-- The designated endpoints form a genuine exact-profile `221` five-circuit.
The two sides are disjoint, their union has five terms, its three projected
factor spans have finranks `2`, `2`, and `1`, distinct terms on either side
share no factor beyond the common third factor, and every term has third factor
`w`. -/
theorem designated_endpoint_exact_profile_221 :
    Disjoint S0 S2 ∧
    (S0 ∪ S2).card = 5 ∧
    Circuit (@tensorEvaluation profile221) (S0 ∪ S2) ∧
    Module.finrank F2
      (Submodule.span F2
        (((S0 ∪ S2).image (fun t => t.1.1) : Finset (Fin 2 → F2)) :
          Set (Fin 2 → F2))) = 2 ∧
    Module.finrank F2
      (Submodule.span F2
        (((S0 ∪ S2).image (fun t => t.2.1.1) : Finset (Fin 2 → F2)) :
          Set (Fin 2 → F2))) = 2 ∧
    Module.finrank F2
      (Submodule.span F2
        (((S0 ∪ S2).image (fun t => t.2.2.1) : Finset (Fin 1 → F2)) :
          Set (Fin 1 → F2))) = 1 ∧
    (∀ x ∈ S0, ∀ y ∈ S0, x ≠ y →
      (x.1 ≠ y.1 ∧ x.2.1 ≠ y.2.1)) ∧
    (∀ x ∈ S2, ∀ y ∈ S2, x ≠ y →
      (x.1 ≠ y.1 ∧ x.2.1 ≠ y.2.1)) ∧
    (∀ x ∈ S0 ∪ S2, x.2.2 = w) := by
  have hDisjoint : Disjoint S0 S2 := by decide
  have hCircuit : Circuit (@tensorEvaluation profile221) (S0 ∪ S2) :=
    tensorEvaluation_circuit_union_of_disjoint_card_two_card_three hDisjoint
      state_cardinalities.1 state_cardinalities.2.2 endpoint_evaluations.2
  refine ⟨hDisjoint, by decide, hCircuit, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [endpoint_first_factor_span_eq_top, finrank_top,
      Module.finrank_fin_fun]
  · rw [endpoint_second_factor_span_eq_top, finrank_top,
      Module.finrank_fin_fun]
  · rw [endpoint_third_factor_span_eq_top, finrank_top,
      Module.finrank_fin_fun]
  · intro x hx y hy hxy
    have hx' : x = E11 ∨ x = E22 := by simpa [S0] using hx
    have hy' : y = E11 ∨ y = E22 := by simpa [S0] using hy
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
    all_goals first | contradiction | decide
  · intro x hx y hy hxy
    have hx' : x = E12 ∨ x = E21 ∨ x = J := by simpa [S2] using hx
    have hy' : y = E12 ∨ y = E21 ∨ y = J := by simpa [S2] using hy
    rcases hx' with rfl | rfl | rfl <;>
      rcases hy' with rfl | rfl | rfl
    all_goals first | contradiction | decide
  · intro x hx
    have hx' : x = E12 ∨ x = E21 ∨ x = E11 ∨ x = E22 ∨ x = J := by
      simpa [S0, S2] using hx
    rcases hx' with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The explicit profile-221 checkpoint packages the formula labels, exact
vertices, metrics, finite-set legality, explicit-boundary confinement, endpoint
evaluation equality, and the nine-point ambient carrier count. -/
theorem replay221_checkpoint :
    GeneratedFirstSplit E11 E21 E31 S0 S1 ∧
    SourceThirdFlip E22 E31 E12 J S1 S2 ∧
    SourceThirdFlip E12 J E22 E31 S2 S1 ∧
    DirectedNarrowPairReduction E21 E31 E11 S1 S0 ∧
    tensorEvaluation E11 = tensorEvaluation E21 + tensorEvaluation E31 ∧
    tensorEvaluation E22 + tensorEvaluation E31 =
      tensorEvaluation E12 + tensorEvaluation J ∧
    forwardPath.vertices = [S0, S1, S2] ∧
    reversePath.vertices = [S2, S1, S0] ∧
    forwardPath.length = 2 ∧ reversePath.length = 2 ∧
    forwardPath.altitude = 3 ∧ reversePath.altitude = 3 ∧
    S0.card = 2 ∧ S1.card = 3 ∧ S2.card = 3 ∧
    (∀ X, PathVertex forwardPath X → X ⊆ boundary) ∧
    (∀ X, PathVertex reversePath X → X ⊆ boundary) ∧
    boundary.card = 6 ∧ S0 ∪ S2 ⊂ boundary ∧
    stateEvaluation S2 = stateEvaluation S0 ∧
    stateEvaluation S0 = stateEvaluation S2 ∧
    Fintype.card Term = 9 := by
  refine ⟨forwardSplit, forwardFlip, reverseFlip, reverseReduction,
    E11_split_formula, E22_E31_flip_formula, forwardPath_vertices,
    reversePath_vertices, path_metrics.1, path_metrics.2.1,
    path_metrics.2.2.1, path_metrics.2.2.2, state_cardinalities.1,
    state_cardinalities.2.1, state_cardinalities.2.2, paths_confined.1,
    paths_confined.2.1, paths_confined.2.2.1, paths_confined.2.2.2,
    endpoint_evaluations.1, endpoint_evaluations.2, card_profile221⟩

end BilinearComplexity.NormalizedBinaryReplay221
