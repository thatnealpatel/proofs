import Mathlib.Data.FinEnum
import BilinearComplexity.BinaryAmbientNormalization

set_option autoImplicit false

/-!
# Effective coordinates for finite binary spans

This module exhaustively searches explicit finite binary coordinate data for a
basis of a finitely generated span.  Both the selected forward map and its
inverse coefficient lookup are executable; finite-dimensional basis choice is
used only to prove that the exhaustive search succeeds.
-/

namespace BilinearComplexity.BinaryEffectiveSpanCoordinates

open scoped BigOperators
open NormalizedBinaryCarrier (F2)

/-- Coordinate vectors over the binary field. -/
abbrev Coord (d : ℕ) := BinaryAmbientTensorCoordinates.Coord d

private theorem f2_eq_zero_or_one (x : F2) : x = 0 ∨ x = 1 := by
  have hxval : x.val < 2 := ZMod.val_lt x
  have hval : x.val = 0 ∨ x.val = 1 := by omega
  rcases hval with hval | hval
  · left
    apply ZMod.val_injective
    simpa using hval
  · right
    apply ZMod.val_injective
    exact hval

local instance : FinEnum F2 :=
  FinEnum.ofList [0, 1] (by
    intro x
    rcases f2_eq_zero_or_one x with hx | hx
    · simp [hx]
    · simp [hx])

/-- A candidate indexed family together with its explicitly computed length. -/
structure BasisCandidate (d : ℕ) where
  r : ℕ
  vectors : Fin r → Coord d

/-- The linear combination map of an indexed candidate family. -/
def coefficientMap {d r : ℕ} (b : Fin r → Coord d) :
    (Fin r → F2) →ₗ[F2] Coord d where
  toFun c := ∑ i, c i • b i
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
      RingHom.id_apply]

/-- An explicit finite coefficient witness that a vector belongs to the span
of a finite coordinate set. -/
def Represented {d : ℕ} (S : Finset (Coord d)) (x : Coord d) : Prop :=
  ∃ c : Coord d → F2,
    (∀ v, v ∉ S → c v = 0) ∧ ∑ v ∈ S, c v • v = x

instance {d : ℕ} (S : Finset (Coord d)) (x : Coord d) :
    Decidable (Represented S x) :=
  Fintype.decidableExistsFintype

/-- The executable guard for a genuine basis candidate: its vectors belong to
the input span, its full coefficient map has zero kernel, and every input
generator has coefficients in the candidate. -/
def BasisCandidate.Valid {d : ℕ} (S : Finset (Coord d))
    (q : BasisCandidate d) : Prop :=
  (∀ i, Represented S (q.vectors i)) ∧
    Function.Injective (coefficientMap q.vectors) ∧
    ∀ s ∈ S, ∃ c : Fin q.r → F2, coefficientMap q.vectors c = s

instance {d : ℕ} (S : Finset (Coord d)) (q : BasisCandidate d) :
    Decidable (q.Valid S) := by
  unfold BasisCandidate.Valid
  exact instDecidableAnd

/-- Exhaustive candidate enumeration, with ranks bounded by the supplied
ambient coordinate dimension. -/
def basisCandidates (d : ℕ) : List (BasisCandidate d) :=
  (List.range (d + 1)).flatMap fun r =>
    (FinEnum.toList (Fin r → Coord d)).map fun b => ⟨r, b⟩

/-- Explicit finite representations characterize membership in the ordinary
submodule span. -/
theorem represented_iff_mem_span {d : ℕ} {S : Finset (Coord d)} {x : Coord d} :
    Represented S x ↔ x ∈ Submodule.span F2 (S : Set (Coord d)) := by
  rw [Submodule.mem_span_finset]
  constructor
  · rintro ⟨c, hc, hsum⟩
    refine ⟨c, ?_, hsum⟩
    intro v hv
    by_contra hmem
    have hzero : c v = 0 := hc v hmem
    exact hv hzero
  · rintro ⟨c, hc, hsum⟩
    refine ⟨c, ?_, hsum⟩
    intro v hv
    by_contra hne
    exact hv (hc hne)

private theorem exists_valid_candidate {d : ℕ} (S : Finset (Coord d)) :
    ∃ q ∈ basisCandidates d, q.Valid S := by
  let P := Submodule.span F2 (S : Set (Coord d))
  let r := Module.finrank F2 P
  let e := Module.finBasis F2 P
  let b : Fin r → Coord d := fun i => (e i).1
  let q : BasisCandidate d := ⟨r, b⟩
  have hrle : r ≤ d := by
    calc
      r = Module.finrank F2 P := rfl
      _ ≤ Module.finrank F2 (Coord d) := Submodule.finrank_le P
      _ = d := Module.finrank_fin_fun (R := F2) (n := d)
  have hqmem : q ∈ basisCandidates d := by
    simp only [basisCandidates, List.mem_flatMap, List.mem_range, List.mem_map]
    refine ⟨r, Nat.lt_succ_iff.mpr hrle, b, FinEnum.mem_toList b, rfl⟩
  refine ⟨q, hqmem, ?_⟩
  dsimp only [BasisCandidate.Valid, q, b, BasisCandidate.vectors,
    BasisCandidate.r]
  constructor
  · intro i
    apply (represented_iff_mem_span (S := S)).mpr
    exact (e i).property
  constructor
  · intro c c' hcc'
    have hsub : (∑ i, c i • e i) = ∑ i, c' i • e i := by
      apply Subtype.ext
      change (∑ i, c i • (e i).1) = ∑ i, c' i • (e i).1 at hcc'
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using hcc'
    apply e.equivFun.symm.injective
    simpa only [Module.Basis.equivFun_symm_apply] using hsub
  · intro s hs
    let x : P := ⟨s, Submodule.subset_span hs⟩
    refine ⟨e.equivFun x, ?_⟩
    change (∑ i, e.equivFun x i • (e i).1) = s
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using
      congrArg Subtype.val (e.sum_equivFun x)

private theorem candidate_search_isSome {d : ℕ} (S : Finset (Coord d)) :
    ((basisCandidates d).find? fun q => decide (q.Valid S)).isSome := by
  rw [List.find?_isSome]
  obtain ⟨q, hqmem, hqvalid⟩ := exists_valid_candidate S
  exact ⟨q, hqmem, decide_eq_true hqvalid⟩

private theorem get_find?_property {α : Type*} (l : List α) (p : α → Bool)
    (h : (l.find? p).isSome) : p ((l.find? p).get h) = true := by
  apply List.find?_some
  exact Option.eq_some_of_isSome h

/-- The first basis candidate accepted by the exhaustive, deterministic guard. -/
def selectedBasisCandidate {d : ℕ} (S : Finset (Coord d)) : BasisCandidate d :=
  ((basisCandidates d).find? fun q => decide (q.Valid S)).get
    (candidate_search_isSome S)

/-- The selected candidate satisfies all three executable basis guards. -/
theorem selectedBasisCandidate_valid {d : ℕ} (S : Finset (Coord d)) :
    (selectedBasisCandidate S).Valid S := by
  apply of_decide_eq_true
  exact get_find?_property (basisCandidates d)
    (fun q => decide (q.Valid S)) (candidate_search_isSome S)

private def candidateForward {d : ℕ} (S : Finset (Coord d)) :
    (Fin (selectedBasisCandidate S).r → F2) →ₗ[F2]
      Submodule.span F2 (S : Set (Coord d)) where
  toFun c := ⟨coefficientMap (selectedBasisCandidate S).vectors c, by
    rw [show coefficientMap (selectedBasisCandidate S).vectors c =
      ∑ i, c i • (selectedBasisCandidate S).vectors i from rfl]
    apply Submodule.sum_mem _
    intro i _hi
    apply Submodule.smul_mem
    exact (represented_iff_mem_span (S := S)).mp
      ((selectedBasisCandidate_valid S).1 i)⟩
  map_add' x y := by
    apply Subtype.ext
    exact (coefficientMap (selectedBasisCandidate S).vectors).map_add x y
  map_smul' a x := by
    apply Subtype.ext
    exact (coefficientMap (selectedBasisCandidate S).vectors).map_smul a x

private theorem candidateForward_injective {d : ℕ} (S : Finset (Coord d)) :
    Function.Injective (candidateForward S) := by
  intro x y hxy
  apply (selectedBasisCandidate_valid S).2.1
  exact congrArg Subtype.val hxy

private theorem candidateForward_surjective {d : ℕ} (S : Finset (Coord d)) :
    Function.Surjective (candidateForward S) := by
  intro x
  have hle : Submodule.span F2 (S : Set (Coord d)) ≤
      LinearMap.range (coefficientMap (selectedBasisCandidate S).vectors) := by
    apply Submodule.span_le.mpr
    intro s hs
    have hsfin : s ∈ S := by simpa using hs
    obtain ⟨c, hc⟩ := (selectedBasisCandidate_valid S).2.2 s hsfin
    exact ⟨c, hc⟩
  obtain ⟨c, hc⟩ := hle x.property
  exact ⟨c, Subtype.ext hc⟩

private def inverseCoefficients {d : ℕ} (S : Finset (Coord d))
    (x : Submodule.span F2 (S : Set (Coord d))) :
    Fin (selectedBasisCandidate S).r → F2 :=
  let candidates := FinEnum.toList (Fin (selectedBasisCandidate S).r → F2)
  let found := candidates.find? fun c => decide (candidateForward S c = x)
  found.get (by
    rw [List.find?_isSome]
    obtain ⟨c, hc⟩ := candidateForward_surjective S x
    exact ⟨c, FinEnum.mem_toList c, decide_eq_true hc⟩)

private theorem foundCoefficients_correct {d : ℕ} (S : Finset (Coord d))
    (x : Submodule.span F2 (S : Set (Coord d)))
    (h : ((FinEnum.toList (Fin (selectedBasisCandidate S).r → F2)).find?
      fun c => decide (candidateForward S c = x)).isSome) :
    candidateForward S
      (((FinEnum.toList (Fin (selectedBasisCandidate S).r → F2)).find?
        fun c => decide (candidateForward S c = x)).get h) = x := by
  apply of_decide_eq_true
  exact get_find?_property
    (FinEnum.toList (Fin (selectedBasisCandidate S).r → F2))
    (fun c => decide (candidateForward S c = x)) h

private theorem candidateForward_inverseCoefficients {d : ℕ}
    (S : Finset (Coord d))
    (x : Submodule.span F2 (S : Set (Coord d))) :
    candidateForward S (inverseCoefficients S x) = x := by
  unfold inverseCoefficients
  apply foundCoefficients_correct

/-- Computed coordinates on a finite binary span, including the semantic rank
certificate forced by the explicit equivalence. -/
structure EffectiveSpanCoordinates {d : ℕ} (S : Finset (Coord d)) where
  r : ℕ
  equiv : (Fin r → F2) ≃ₗ[F2] Submodule.span F2 (S : Set (Coord d))
  rank_eq_finrank : r = Module.finrank F2 (Submodule.span F2 (S : Set (Coord d)))

/-- Deterministically compute the rank and explicit mutually inverse
coordinates of a finite binary coordinate span. -/
def effectiveSpanCoordinates {d : ℕ} (S : Finset (Coord d)) :
    EffectiveSpanCoordinates S where
  r := (selectedBasisCandidate S).r
  equiv := LinearEquiv.mk (candidateForward S) (inverseCoefficients S)
    (fun c => candidateForward_injective S
      (candidateForward_inverseCoefficients S (candidateForward S c)))
    (candidateForward_inverseCoefficients S)
  rank_eq_finrank := by
    rw [← (LinearEquiv.mk (candidateForward S) (inverseCoefficients S)
      (fun c => candidateForward_injective S
        (candidateForward_inverseCoefficients S (candidateForward S c)))
      (candidateForward_inverseCoefficients S)).finrank_eq]
    exact (Module.finrank_fin_fun (R := F2)
      (n := (selectedBasisCandidate S).r)).symm

/-! ## Executable and semantic rank regressions -/

/-- The empty zero-dimensional coordinate set has rank zero by the semantic
rank certificate, not by reducing the exhaustive search. -/
example : (effectiveSpanCoordinates (∅ : Finset (Coord 0))).r = 0 := by
  rw [(effectiveSpanCoordinates (∅ : Finset (Coord 0))).rank_eq_finrank]
  simp

/-- A zero-only input has zero-dimensional span. -/
example : (effectiveSpanCoordinates ({0} : Finset (Coord 2))).r = 0 := by
  rw [(effectiveSpanCoordinates ({0} : Finset (Coord 2))).rank_eq_finrank]
  simp

/-- A nonzero singleton in a larger ambient space has rank one. -/
example : (effectiveSpanCoordinates ({![1, 0]} : Finset (Coord 2))).r = 1 := by
  rw [(effectiveSpanCoordinates ({![1, 0]} : Finset (Coord 2))).rank_eq_finrank]
  rw [show (↑({![1, 0]} : Finset (Coord 2)) : Set (Coord 2)) =
    {![1, 0]} by simp]
  exact finrank_span_singleton (K := F2) (V := Coord 2)
    (show ![1, 0] ≠ (0 : Coord 2) by decide)

private theorem span_singleton_one_eq_top :
    Submodule.span F2 (↑({![1]} : Finset (Coord 1)) : Set (Coord 1)) = ⊤ := by
  apply (Submodule.eq_top_iff_forall_basis_mem
    (Pi.basisFun F2 (Fin 1))).mpr
  intro i
  rw [Pi.basisFun_apply]
  apply Submodule.subset_span
  fin_cases i
  decide

/-- Repeating a generator does not change the one-dimensional span. -/
example : (effectiveSpanCoordinates ({![1], ![1]} :
    Finset (Coord 1))).r = 1 := by
  rw [(effectiveSpanCoordinates ({![1], ![1]} :
    Finset (Coord 1))).rank_eq_finrank]
  rw [show (↑({![1], ![1]} : Finset (Coord 1)) : Set (Coord 1)) =
    ↑({![1]} : Finset (Coord 1)) by ext; simp]
  rw [span_singleton_one_eq_top, finrank_top, Module.finrank_fin_fun]

private theorem span_dependent_two_eq_top :
    Submodule.span F2
      (↑({![1, 0], ![0, 1], ![1, 1]} : Finset (Coord 2)) :
        Set (Coord 2)) = ⊤ := by
  apply (Submodule.eq_top_iff_forall_basis_mem
    (Pi.basisFun F2 (Fin 2))).mpr
  intro i
  rw [Pi.basisFun_apply]
  apply Submodule.subset_span
  fin_cases i <;> decide

/-- The dependent family `e₁, e₂, e₁ + e₂` has rank two. -/
example : (effectiveSpanCoordinates
    ({![1, 0], ![0, 1], ![1, 1]} : Finset (Coord 2))).r = 2 := by
  rw [(effectiveSpanCoordinates
    ({![1, 0], ![0, 1], ![1, 1]} : Finset (Coord 2))).rank_eq_finrank]
  rw [span_dependent_two_eq_top, finrank_top, Module.finrank_fin_fun]

private theorem span_standard_three_eq_top :
    Submodule.span F2
      (↑({![1, 0, 0], ![0, 1, 0], ![0, 0, 1]} : Finset (Coord 3)) :
        Set (Coord 3)) = ⊤ := by
  apply (Submodule.eq_top_iff_forall_basis_mem
    (Pi.basisFun F2 (Fin 3))).mpr
  intro i
  rw [Pi.basisFun_apply]
  apply Submodule.subset_span
  fin_cases i <;> decide

/-- The three standard coordinate vectors span all of `Coord 3`. -/
example : (effectiveSpanCoordinates
    ({![1, 0, 0], ![0, 1, 0], ![0, 0, 1]} : Finset (Coord 3))).r = 3 := by
  rw [(effectiveSpanCoordinates
    ({![1, 0, 0], ![0, 1, 0], ![0, 0, 1]} :
      Finset (Coord 3))).rank_eq_finrank]
  rw [span_standard_three_eq_top, finrank_top, Module.finrank_fin_fun]

-- Runtime evidence covers empty, zero-only, singleton, duplicate/dependent,
-- and full coordinate spans in dimensions zero through three.
#eval ((effectiveSpanCoordinates (∅ : Finset (Coord 0))).r,
  (effectiveSpanCoordinates ({0} : Finset (Coord 2))).r,
  (effectiveSpanCoordinates ({![1, 0]} : Finset (Coord 2))).r,
  (effectiveSpanCoordinates ({![1], ![1]} : Finset (Coord 1))).r,
  (effectiveSpanCoordinates
    ({![1, 0], ![0, 1], ![1, 1]} : Finset (Coord 2))).r,
  (effectiveSpanCoordinates
    ({![1, 0, 0], ![0, 1, 0], ![0, 0, 1]} : Finset (Coord 3))).r)

#check @effectiveSpanCoordinates

end BilinearComplexity.BinaryEffectiveSpanCoordinates
