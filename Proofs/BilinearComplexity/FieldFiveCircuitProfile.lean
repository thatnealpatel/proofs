import BilinearComplexity.FieldContextual
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

set_option autoImplicit false

open scoped BigOperators

namespace BilinearComplexity
namespace FieldFiveCircuitProfile

open FieldRankOne

variable {k : Type*} [Field k]

/-- The dimension of the span of a finite family. -/
noncomputable def familyRank {ι V : Type*} [AddCommGroup V] [Module k V]
    (v : ι → V) : ℕ :=
  Module.finrank k (Submodule.span k (Set.range v))

/-- The coordinate outer product of two vectors. -/
def outerProduct {b c : ℕ} (y : Fin b → k) (z : Fin c → k) :
    Fin b × Fin c → k :=
  fun p => y p.1 * z p.2

/-- The displayed coefficients form a relation among five pure coordinate tensors. -/
def IsProductRelation {a b c : ℕ} (x : Fin 5 → Fin a → k)
    (y : Fin 5 → Fin b → k) (z : Fin 5 → Fin c → k)
    (q : Fin 5 → k) : Prop :=
  ∑ i, q i • evalFactors 1 (x i) (y i) (z i) = 0

/-- The five evaluated pure tensors determined by three coordinate-factor families. -/
def productFamily {a b c : ℕ} (x : Fin 5 → Fin a → k)
    (y : Fin 5 → Fin b → k) (z : Fin 5 → Fin c → k) :
    Fin 5 → Tensor k a b c :=
  fun i => evalFactors 1 (x i) (y i) (z i)

/-- Every family obtained by deleting one index is linearly independent. -/
def EveryDeletionIndependent {V : Type*} [AddCommGroup V] [Module k V]
    (t : Fin 5 → V) : Prop :=
  ∀ d : Fin 5, LinearIndependent k (fun i : {i : Fin 5 // i ≠ d} => t i.1)

/-- A five-product family is minimally dependent when it has a nonzero relation and every
relation having a zero coefficient is the zero relation. -/
def IsMinimalFiveProductCircuit {a b c : ℕ} (x : Fin 5 → Fin a → k)
    (y : Fin 5 → Fin b → k) (z : Fin 5 → Fin c → k) : Prop :=
  (∃ q : Fin 5 → k, q ≠ 0 ∧ IsProductRelation x y z q) ∧
    ∀ q : Fin 5 → k, IsProductRelation x y z q → (∃ i, q i = 0) → q = 0

example {ι V : Type*} [AddCommGroup V] [Module k V] (v : ι → V) :
    familyRank (k := k) v = (Set.range v).finrank k := rfl

example : outerProduct (k := ℚ) (fun _ : Fin 1 => 2) (fun _ : Fin 1 => 3) (0, 0) = 6 := by
  norm_num [outerProduct]

example {a b c : ℕ} (x : Fin 5 → Fin a → k) (y : Fin 5 → Fin b → k)
    (z : Fin 5 → Fin c → k) (q : Fin 5 → k) :
    IsProductRelation x y z q ↔ ∑ i, q i • productFamily x y z i = 0 := Iff.rfl

example {a b c : ℕ} (x : Fin 5 → Fin a → k) (y : Fin 5 → Fin b → k)
    (z : Fin 5 → Fin c → k) (i : Fin 5) :
    productFamily x y z i = evalFactors 1 (x i) (y i) (z i) := rfl

/-- The zero-coefficient relation criterion is equivalent to linear independence after every
single-index deletion. -/
theorem vanishing_relation_iff_everyDeletionIndependent {V : Type*}
    [AddCommGroup V] [Module k V] (t : Fin 5 → V) :
    (∀ q : Fin 5 → k, (∑ i, q i • t i) = 0 →
      (∃ i, q i = 0) → q = 0) ↔ EveryDeletionIndependent (k := k) t := by
  classical
  have sum_extend (d : Fin 5) (coeff : {i : Fin 5 // i ≠ d} → k) :
      (∑ i, (if h : i ≠ d then coeff ⟨i, h⟩ else 0) • t i) =
        ∑ i, coeff i • t i := by
    let f : Fin 5 → V := fun i =>
      (if h : i ≠ d then coeff ⟨i, h⟩ else 0) • t i
    calc
      ∑ i, (if h : i ≠ d then coeff ⟨i, h⟩ else 0) • t i =
          (∑ i : {i : Fin 5 // i ≠ d}, f i) +
            ∑ i : {i : Fin 5 // ¬ i ≠ d}, f i := by
              exact (Fintype.sum_subtype_add_sum_subtype
                (fun i : Fin 5 => i ≠ d) f).symm
      _ = (∑ i, coeff i • t i) + 0 := by
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          simp only [f, dif_pos i.2]
        · apply Finset.sum_eq_zero
          intro i hi
          simp only [f, dif_neg i.2, zero_smul]
      _ = ∑ i, coeff i • t i := add_zero _
  constructor
  · intro h d
    rw [Fintype.linearIndependent_iff]
    intro coeff hcoeff i
    let extended : Fin 5 → k :=
      fun j => if hj : j ≠ d then coeff ⟨j, hj⟩ else 0
    have hextended : (∑ j, extended j • t j) = 0 := by
      rw [show (∑ j, extended j • t j) = ∑ j, coeff j • t j by
        simpa only [extended] using sum_extend d coeff]
      exact hcoeff
    have hzero : extended = 0 := h extended hextended ⟨d, by simp [extended]⟩
    have hi := congrFun hzero i.1
    simpa only [extended, dif_pos i.2, Pi.zero_apply] using hi
  · intro h q hq
    rintro ⟨d, hd⟩
    have hcoeffPoint : ∀ i : {i : Fin 5 // i ≠ d}, q i.1 = 0 := by
      apply (Fintype.linearIndependent_iff.mp (h d))
      change (∑ i : {i : Fin 5 // i ≠ d}, q i.1 • t i.1) = 0
      rw [← sum_extend d (fun i => q i.1)]
      have hext : (fun i : Fin 5 => if hi : i ≠ d then q i else 0) = q := by
        funext i
        by_cases hi : i = d
        · subst i
          simp only [ne_eq, not_true_eq_false, ↓reduceDIte, hd]
        · exact dif_pos hi
      change (∑ i, (if hi : i ≠ d then q i else 0) • t i) = 0
      calc
        _ = ∑ i, q i • t i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [congrFun hext i]
        _ = 0 := hq
    funext i
    by_cases hi : i = d
    · subst i
      exact hd
    · exact hcoeffPoint ⟨i, hi⟩

/-- Coefficient-kernel minimality is exactly nontrivial dependence together with linear
independence of every one-index deletion. -/
theorem minimalFiveProductCircuit_iff {a b c : ℕ} (x : Fin 5 → Fin a → k)
    (y : Fin 5 → Fin b → k) (z : Fin 5 → Fin c → k) :
    IsMinimalFiveProductCircuit x y z ↔
      (∃ q : Fin 5 → k, q ≠ 0 ∧ IsProductRelation x y z q) ∧
        EveryDeletionIndependent (k := k) (productFamily x y z) := by
  unfold IsMinimalFiveProductCircuit IsProductRelation productFamily
  rw [vanishing_relation_iff_everyDeletionIndependent]

/-- If every one-index deletion is independent, then every proper indexed subfamily is
independent, including the empty subfamily. -/
theorem EveryDeletionIndependent.linearIndependent_restrict {V : Type*}
    [AddCommGroup V] [Module k V] (t : Fin 5 → V)
    (h : EveryDeletionIndependent (k := k) t) (s : Set (Fin 5)) (hs : s ≠ Set.univ) :
    LinearIndependent k (fun i : s => t i.1) := by
  have hex : ∃ d : Fin 5, d ∉ s := by
    by_contra hnone
    push Not at hnone
    apply hs
    exact Set.eq_univ_of_forall hnone
  obtain ⟨d, hd⟩ := hex
  let f : s → {i : Fin 5 // i ≠ d} := fun i =>
    ⟨i.1, fun hi => hd (hi ▸ i.2)⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact congrArg (fun u : {i : Fin 5 // i ≠ d} => u.1) hij
  exact (h d).comp f hf

private theorem relation_pointwise {a b c : ℕ} {x : Fin 5 → Fin a → k}
    {y : Fin 5 → Fin b → k} {z : Fin 5 → Fin c → k} {q : Fin 5 → k}
    (h : IsProductRelation x y z q) :
    ∀ p j l, ∑ i, q i * x i p * y i j * z i l = 0 := by
  intro p j l
  have hp := congrFun (congrFun (congrFun h p) j) l
  calc
    _ = ∑ i, q i * (x i p * y i j * z i l) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 0 := by
      simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, evalFactors,
        one_mul, smul_eq_mul] using hp

private theorem linearIndependent_pair_iff {V : Type*} [AddCommGroup V] [Module k V]
    (u v : V) :
    LinearIndependent k ![u, v] ↔
      ∀ A B : k, A • u + B • v = 0 → A = 0 ∧ B = 0 :=
  LinearIndependent.pair_iff

private theorem exists_minor_ne_zero {n : ℕ} {u v : Fin n → k}
    (h : LinearIndependent k ![u, v]) :
    ∃ p q : Fin n, u p * v q - u q * v p ≠ 0 := by
  by_contra hminor
  push Not at hminor
  have hu : u ≠ 0 := by
    intro hu
    have hc := (linearIndependent_pair_iff u v).mp h 1 0
    have hz : (1 : k) • u + (0 : k) • v = 0 := by simp [hu]
    exact one_ne_zero (hc hz).1
  obtain ⟨p, hp⟩ : ∃ p, u p ≠ 0 := Function.ne_iff.mp hu
  have hrel : (-v p) • u + (u p) • v = 0 := by
    funext q
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    linear_combination hminor p q
  have hc := (linearIndependent_pair_iff u v).mp h (-v p) (u p) hrel
  exact hp hc.2

private theorem outer_diagonal_coeff_zero {b c : ℕ}
    {y y₀ y₁ : Fin b → k} {z z₀ z₁ : Fin c → k} {A B : k}
    (hy : LinearIndependent k ![y₀, y₁])
    (hz : LinearIndependent k ![z₀, z₁])
    (h : outerProduct y z =
      A • outerProduct y₀ z₀ + B • outerProduct y₁ z₁) :
    A = 0 ∨ B = 0 := by
  obtain ⟨p₀, p₁, hp⟩ := exists_minor_ne_zero hy
  obtain ⟨q₀, q₁, hq⟩ := exists_minor_ne_zero hz
  have hpure :
      outerProduct y z (p₀, q₀) * outerProduct y z (p₁, q₁) -
        outerProduct y z (p₀, q₁) * outerProduct y z (p₁, q₀) = 0 := by
    simp only [outerProduct]
    ring
  have hformula :
      A * B * (y₀ p₀ * y₁ p₁ - y₀ p₁ * y₁ p₀) *
          (z₀ q₀ * z₁ q₁ - z₀ q₁ * z₁ q₀) =
        outerProduct y z (p₀, q₀) * outerProduct y z (p₁, q₁) -
          outerProduct y z (p₀, q₁) * outerProduct y z (p₁, q₀) := by
    rw [h]
    simp only [Pi.add_apply, Pi.smul_apply, outerProduct, smul_eq_mul]
    ring
  have hab : A * B = 0 := by
    have hzero : (A * B) *
        ((y₀ p₀ * y₁ p₁ - y₀ p₁ * y₁ p₀) *
          (z₀ q₀ * z₁ q₁ - z₀ q₁ * z₁ q₀)) = 0 := by
      calc
        _ = A * B * (y₀ p₀ * y₁ p₁ - y₀ p₁ * y₁ p₀) *
            (z₀ q₀ * z₁ q₁ - z₀ q₁ * z₁ q₀) := by ring
        _ = 0 := hformula.trans hpure
    exact (mul_eq_zero.mp hzero).resolve_right (mul_ne_zero hp hq)
  exact mul_eq_zero.mp hab

private theorem outer_pair_linearIndependent {b c : ℕ}
    {y₀ y₁ : Fin b → k} {z₀ z₁ : Fin c → k}
    (hy : LinearIndependent k ![y₀, y₁]) (hz₀ : z₀ ≠ 0) (hz₁ : z₁ ≠ 0) :
    LinearIndependent k ![outerProduct y₀ z₀, outerProduct y₁ z₁] := by
  rw [linearIndependent_pair_iff]
  intro A B h
  obtain ⟨q₀, hq₀⟩ := Function.ne_iff.mp hz₀
  obtain ⟨q₁, hq₁⟩ := Function.ne_iff.mp hz₁
  have hA : A * z₀ q₀ = 0 := by
    have hv : (A * z₀ q₀) • y₀ + (B * z₁ q₀) • y₁ = 0 := by
      funext p
      have hp := congrFun h (p, q₀)
      change A * (y₀ p * z₀ q₀) + B * (y₁ p * z₁ q₀) = 0 at hp
      change A * z₀ q₀ * y₀ p + B * z₁ q₀ * y₁ p = 0
      linear_combination hp
    exact ((linearIndependent_pair_iff y₀ y₁).mp hy _ _ hv).1
  have hB : B * z₁ q₁ = 0 := by
    have hv : (A * z₀ q₁) • y₀ + (B * z₁ q₁) • y₁ = 0 := by
      funext p
      have hp := congrFun h (p, q₁)
      change A * (y₀ p * z₀ q₁) + B * (y₁ p * z₁ q₁) = 0 at hp
      change A * z₀ q₁ * y₀ p + B * z₁ q₁ * y₁ p = 0
      linear_combination hp
    exact ((linearIndependent_pair_iff y₀ y₁).mp hy _ _ hv).2
  exact ⟨(mul_eq_zero.mp hA).resolve_right hq₀,
    (mul_eq_zero.mp hB).resolve_right hq₁⟩

private theorem flatten_rank_le_five {A B : Type*} [Fintype A] [Fintype B]
    (x : Fin 5 → A → k) (w : Fin 5 → B → k) (q : Fin 5 → k)
    (hq : ∀ i, q i ≠ 0)
    (hrel : ∀ a b, ∑ i, q i * x i a * w i b = 0) :
    familyRank (k := k) x + familyRank (k := k) w ≤ 5 := by
  classical
  let X : Matrix A (Fin 5) k := fun a i => x i a
  let W : Matrix (Fin 5) B k := fun i b => q i * w i b
  have hXW : X * W = 0 := by
    ext a b
    change (∑ i, x i a * (q i * w i b)) = 0
    calc
      _ = ∑ i, q i * x i a * w i b := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := hrel a b
  have hXcol : X.col = x := by rfl
  have hWrow : W.row = fun i => q i • w i := by
    rfl
  have hspan : Submodule.span k (Set.range (fun i => q i • w i)) =
      Submodule.span k (Set.range w) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have hi : (q i)⁻¹ • (q i • w i) = w i := by
        rw [← mul_smul, inv_mul_cancel₀ (hq i), one_smul]
      rw [← hi]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hXrank : X.rank = familyRank (k := k) x := by
    rw [Matrix.rank_eq_finrank_span_cols, hXcol]
    rfl
  have hWrank : W.rank = familyRank (k := k) w := by
    rw [Matrix.rank_eq_finrank_span_row, hWrow, hspan]
    rfl
  rw [← hXrank, ← hWrank]
  exact Matrix.rank_add_rank_le_card_of_mul_eq_zero hXW

private theorem proportional_of_not_linearIndependent {V : Type*} [AddCommGroup V]
    [Module k V] {u v : V} (hu : u ≠ 0)
    (h : ¬ LinearIndependent k ![u, v]) : ∃ c : k, c • u = v := by
  rw [LinearIndependent.pair_iff' hu] at h
  simpa only [not_forall, not_not] using h

private theorem exists_family_pair_through {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module k V] (v : ι → V) (hv : ∀ i, v i ≠ 0)
    (i : ι) (hrank : 2 ≤ familyRank (k := k) v) :
    ∃ j, LinearIndependent k ![v i, v j] := by
  by_contra hnone
  push Not at hnone
  have hrange : Set.range v ⊆ Submodule.span k {v i} := by
    rintro _ ⟨j, rfl⟩
    obtain ⟨c, hc⟩ := proportional_of_not_linearIndependent (hv i) (hnone j)
    rw [← hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  have hspan : Submodule.span k (Set.range v) ≤ Submodule.span k {v i} :=
    Submodule.span_le.mpr hrange
  have hle := Submodule.finrank_mono hspan
  have hone : Module.finrank k (Submodule.span k {v i}) ≤ 1 := by
    convert finrank_span_le_card (R := k) ({v i} : Set V) using 1
    simp
  exact (not_lt_of_ge hrank) (by
    change Module.finrank k (Submodule.span k (Set.range v)) < 2
    exact lt_of_le_of_lt (hle.trans hone) (by omega))

private theorem exists_common_linearIndependent_pair {b c : ℕ}
    (y : Fin 5 → Fin b → k) (z : Fin 5 → Fin c → k)
    (hy0 : ∀ i, y i ≠ 0) (hz0 : ∀ i, z i ≠ 0)
    (hyRank : 2 ≤ familyRank (k := k) y)
    (hzRank : 2 ≤ familyRank (k := k) z) :
    ∃ s t, LinearIndependent k ![y s, y t] ∧
      LinearIndependent k ![z s, z t] := by
  obtain ⟨j, hyj⟩ := exists_family_pair_through y hy0 0 hyRank
  by_cases hzj : LinearIndependent k ![z 0, z j]
  · exact ⟨0, j, hyj, hzj⟩
  obtain ⟨m, hzm⟩ := exists_family_pair_through z hz0 0 hzRank
  by_cases hym : LinearIndependent k ![y 0, y m]
  · exact ⟨0, m, hym, hzm⟩
  obtain ⟨cy, hcy⟩ := proportional_of_not_linearIndependent (hy0 0) hym
  obtain ⟨cz, hcz⟩ := proportional_of_not_linearIndependent (hz0 0) hzj
  have cy0 : cy ≠ 0 := by
    intro hzero
    apply hy0 m
    rw [← hcy, hzero, zero_smul]
  have cz0 : cz ≠ 0 := by
    intro hzero
    apply hz0 j
    rw [← hcz, hzero, zero_smul]
  refine ⟨j, m, ?_, ?_⟩
  · rw [← hcy, linearIndependent_pair_iff]
    intro A B hAB
    have hbase : (B * cy) • y 0 + A • y j = 0 := by
      calc
        _ = A • y j + B • (cy • y 0) := by
          rw [smul_smul]
          module
        _ = 0 := hAB
    have hc := (linearIndependent_pair_iff (y 0) (y j)).mp hyj _ _ hbase
    exact ⟨hc.2, (mul_eq_zero.mp hc.1).resolve_right cy0⟩
  · rw [← hcz, linearIndependent_pair_iff]
    intro A B hAB
    have hbase : (A * cz) • z 0 + B • z m = 0 := by
      calc
        _ = A • (cz • z 0) + B • z m := by rw [smul_smul]
        _ = 0 := hAB
    have hc := (linearIndependent_pair_iff (z 0) (z m)).mp hzm _ _ hbase
    exact ⟨(mul_eq_zero.mp hc.1).resolve_right cz0, hc.2⟩

private theorem span_family_eq_span_pair_of_rank_le_two {V : Type*}
    [AddCommGroup V] [Module k V] (w : Fin 5 → V) (s t : Fin 5)
    (hst : LinearIndependent k ![w s, w t])
    (hrank : familyRank (k := k) w ≤ 2) :
    Submodule.span k (Set.range w) =
      Submodule.span k (Set.range ![w s, w t]) := by
  let S := Submodule.span k (Set.range w)
  let P := Submodule.span k (Set.range ![w s, w t])
  letI : Module.Finite k S :=
    Module.Finite.span_of_finite k (Set.finite_range w)
  letI : Module.Finite k P :=
    Module.Finite.span_of_finite k (Set.finite_range ![w s, w t])
  have hPS : P ≤ S := by
    apply Submodule.span_mono
    rintro v ⟨i, rfl⟩
    fin_cases i
    · exact ⟨s, rfl⟩
    · exact ⟨t, rfl⟩
  have hP : Module.finrank k P = 2 := by
    simpa only [P, Fintype.card_fin] using finrank_span_eq_card hst
  have hEq : P = S := by
    apply Submodule.eq_of_le_of_finrank_le hPS
    rw [hP]
    exact hrank
  exact hEq.symm

private theorem mem_span_pair_iff {V : Type*} [AddCommGroup V] [Module k V]
    {u v x : V} : x ∈ Submodule.span k (Set.range ![u, v]) ↔
    ∃ A B : k, x = A • u + B • v := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c 0, c 1, by simpa only [Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one] using hc.symm⟩
  · rintro ⟨A, B, h⟩
    refine ⟨![A, B], ?_⟩
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using h.symm

private theorem two_ray_contradiction {a b c : ℕ}
    (x : Fin 5 → Fin a → k) (y : Fin 5 → Fin b → k) (z : Fin 5 → Fin c → k)
    (hy0 : ∀ i, y i ≠ 0) (hz0 : ∀ i, z i ≠ 0)
    (q : Fin 5 → k) (hqall : ∀ i, q i ≠ 0)
    (hq : IsProductRelation x y z q)
    (hminimal : ∀ r : Fin 5 → k, IsProductRelation x y z r →
      (∃ i, r i = 0) → r = 0)
    (hpairRank : familyRank (k := k) (fun i => outerProduct (y i) (z i)) ≤ 2)
    (hyRank : 2 ≤ familyRank (k := k) y)
    (hzRank : 2 ≤ familyRank (k := k) z) : False := by
  classical
  let w : Fin 5 → (Fin b × Fin c → k) := fun i => outerProduct (y i) (z i)
  obtain ⟨s, t, hyst, hzst⟩ :=
    exists_common_linearIndependent_pair y z hy0 hz0 hyRank hzRank
  have hwst : LinearIndependent k ![w s, w t] :=
    outer_pair_linearIndependent hyst (hz0 s) (hz0 t)
  have hspan : Submodule.span k (Set.range w) =
      Submodule.span k (Set.range ![w s, w t]) :=
    span_family_eq_span_pair_of_rank_le_two w s t hwst hpairRank
  have hex : ∀ i, ∃ A B : k, w i = A • w s + B • w t := by
    intro i
    rw [← mem_span_pair_iff, ← hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  choose α β hrepr using hex
  have haxis : ∀ i, α i = 0 ∨ β i = 0 := by
    intro i
    exact outer_diagonal_coeff_zero hyst hzst (hrepr i)
  have hβs : β s = 0 := by
    have hsrel : (α s - 1) • w s + β s • w t = 0 := by
      calc
        _ = (α s • w s + β s • w t) - w s := by module
        _ = 0 := by rw [← hrepr s]; simp
    exact ((linearIndependent_pair_iff (w s) (w t)).mp hwst _ _ hsrel).2
  have hβt : β t = 1 := by
    have htrel : α t • w s + (β t - 1) • w t = 0 := by
      calc
        _ = (α t • w s + β t • w t) - w t := by module
        _ = 0 := by rw [← hrepr t]; simp
    exact sub_eq_zero.mp ((linearIndependent_pair_iff (w s) (w t)).mp
      hwst _ _ htrel).2
  have hflat (p : Fin a) : ∑ i, (q i * x i p) • w i = 0 := by
    funext jl
    rcases jl with ⟨j, l⟩
    have hp := relation_pointwise hq p j l
    change (∑ i, (q i * x i p) * w i (j, l)) = 0
    calc
      _ = ∑ i, q i * x i p * y i j * z i l := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [w, outerProduct]
        ring
      _ = 0 := hp
  have hA : ∀ p : Fin a, ∑ i, q i * x i p * α i = 0 := by
    intro p
    let A := ∑ i, q i * x i p * α i
    let B := ∑ i, q i * x i p * β i
    have hpairs : A • w s + B • w t = 0 := by
      calc
        _ = ∑ i, (q i * x i p) • (α i • w s + β i • w t) := by
          dsimp only [A, B]
          rw [Finset.sum_smul, Finset.sum_smul, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          simp only [smul_add, smul_smul]
        _ = ∑ i, (q i * x i p) • w i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hrepr i]
        _ = 0 := hflat p
    exact ((linearIndependent_pair_iff (w s) (w t)).mp hwst A B hpairs).1
  let r : Fin 5 → k := fun i => if β i = 0 then q i else 0
  have hr : IsProductRelation x y z r := by
    apply funext
    intro p
    apply funext
    intro j
    apply funext
    intro l
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, evalFactors,
      one_mul, smul_eq_mul]
    calc
      ∑ i, r i * (x i p * y i j * z i l) =
          ∑ i, (q i * x i p * α i) * w s (j, l) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hiRep := congrFun (hrepr i) (j, l)
        simp only [w, outerProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hiRep
        by_cases hβ : β i = 0
        · simp only [r, if_pos hβ]
          calc
            q i * (x i p * y i j * z i l) =
                q i * x i p * (y i j * z i l) := by ring
            _ = q i * x i p *
                (α i * (y s j * z s l) + β i * (y t j * z t l)) := by rw [hiRep]
            _ = q i * x i p * α i * w s (j, l) := by
              simp only [hβ, w, outerProduct]
              ring
        · have hα : α i = 0 := (haxis i).resolve_right hβ
          simp only [r, if_neg hβ, zero_mul, hα, mul_zero]
      _ = (∑ i, q i * x i p * α i) * w s (j, l) := by rw [Finset.sum_mul]
      _ = 0 := by rw [hA p, zero_mul]
  have hrs : r s ≠ 0 := by simp only [r, if_pos hβs]; exact hqall s
  have hrt : r t = 0 := by simp [r, hβt]
  have hrzero := hminimal r hr ⟨t, hrt⟩
  exact hrs (congrFun hrzero s)

private theorem not_linearIndependent_of_familyRank_le_one {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module k V] (v : ι → V)
    (hrank : familyRank (k := k) v ≤ 1) (i j : ι) :
    ¬ LinearIndependent k ![v i, v j] := by
  intro hij
  let S := Submodule.span k (Set.range v)
  let P := Submodule.span k (Set.range ![v i, v j])
  letI : Module.Finite k S :=
    Module.Finite.span_of_finite k (Set.finite_range v)
  letI : Module.Finite k P :=
    Module.Finite.span_of_finite k (Set.finite_range ![v i, v j])
  have hPS : P ≤ S := by
    apply Submodule.span_mono
    rintro _ ⟨r, rfl⟩
    fin_cases r
    · exact ⟨i, rfl⟩
    · exact ⟨j, rfl⟩
  have hle := Submodule.finrank_mono hPS
  have hP : Module.finrank k P = 2 := by
    simpa only [P, Fintype.card_fin] using finrank_span_eq_card hij
  have : 2 ≤ familyRank (k := k) v := by
    change 2 ≤ Module.finrank k S
    rw [← hP]
    exact hle
  omega

private theorem common_nonzero_coordinate_of_rank_le_one {b : ℕ}
    (y : Fin 5 → Fin b → k) (hy0 : ∀ i, y i ≠ 0)
    (hrank : familyRank (k := k) y ≤ 1) :
    ∃ j : Fin b, ∀ i, y i j ≠ 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp (hy0 0)
  refine ⟨j, ?_⟩
  intro i
  have hdep := not_linearIndependent_of_familyRank_le_one y hrank 0 i
  obtain ⟨c, hc⟩ := proportional_of_not_linearIndependent (hy0 0) hdep
  have hc0 : c ≠ 0 := by
    intro hzero
    apply hy0 i
    rw [← hc, hzero, zero_smul]
  have hcoord := congrFun hc j
  rw [Pi.smul_apply, smul_eq_mul] at hcoord
  rw [← hcoord]
  exact mul_ne_zero hc0 hj

private theorem contraction_flatten_rank_le_five {a b c : ℕ}
    (x : Fin 5 → Fin a → k) (y : Fin 5 → Fin b → k) (z : Fin 5 → Fin c → k)
    (hy0 : ∀ i, y i ≠ 0) (q : Fin 5 → k) (hqall : ∀ i, q i ≠ 0)
    (hrel : IsProductRelation x y z q)
    (hyRank : familyRank (k := k) y ≤ 1) :
    familyRank (k := k) x + familyRank (k := k) z ≤ 5 := by
  obtain ⟨j, hj⟩ := common_nonzero_coordinate_of_rank_le_one y hy0 hyRank
  let q' : Fin 5 → k := fun i => q i * y i j
  have hq' : ∀ i, q' i ≠ 0 := fun i => mul_ne_zero (hqall i) (hj i)
  apply flatten_rank_le_five x z q' hq'
  intro p l
  have hp := relation_pointwise hrel p j l
  calc
    ∑ i, q' i * x i p * z i l = ∑ i, q i * x i p * y i j * z i l := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [q']
      ring
    _ = 0 := hp

private theorem high_first_rank_sum_le_six {a b c : ℕ}
    (x : Fin 5 → Fin a → k) (y : Fin 5 → Fin b → k) (z : Fin 5 → Fin c → k)
    (hy0 : ∀ i, y i ≠ 0) (hz0 : ∀ i, z i ≠ 0)
    (q : Fin 5 → k) (hqall : ∀ i, q i ≠ 0)
    (hrel : IsProductRelation x y z q)
    (hminimal : ∀ r : Fin 5 → k, IsProductRelation x y z r →
      (∃ i, r i = 0) → r = 0)
    (hxRank : 3 ≤ familyRank (k := k) x) :
    familyRank (k := k) x + familyRank (k := k) y +
      familyRank (k := k) z ≤ 6 := by
  have hflat : familyRank (k := k) x +
      familyRank (k := k) (fun i => outerProduct (y i) (z i)) ≤ 5 := by
    apply flatten_rank_le_five x (fun i => outerProduct (y i) (z i)) q hqall
    intro p jl
    rcases jl with ⟨j, l⟩
    have hp := relation_pointwise hrel p j l
    calc
      ∑ i, q i * x i p * outerProduct (y i) (z i) (j, l) =
          ∑ i, q i * x i p * y i j * z i l := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [outerProduct]
        ring
      _ = 0 := hp
  have hpair : familyRank (k := k) (fun i => outerProduct (y i) (z i)) ≤ 2 := by
    omega
  by_cases hy2 : 2 ≤ familyRank (k := k) y
  · by_cases hz2 : 2 ≤ familyRank (k := k) z
    · exact (two_ray_contradiction x y z hy0 hz0 q hqall hrel hminimal
        hpair hy2 hz2).elim
    · have hz1 : familyRank (k := k) z ≤ 1 := by omega
      have hcontract := contraction_flatten_rank_le_five x z y hz0 q hqall
        (by
          apply funext
          intro p
          apply funext
          intro l
          apply funext
          intro j
          have hp := relation_pointwise hrel p j l
          simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, evalFactors,
            one_mul, smul_eq_mul]
          calc
            ∑ i, q i * (x i p * z i l * y i j) =
                ∑ i, q i * x i p * y i j * z i l := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = 0 := hp)
        hz1
      omega
  · have hy1 : familyRank (k := k) y ≤ 1 := by omega
    have hcontract := contraction_flatten_rank_le_five x y z hy0 q hqall hrel hy1
    omega

private theorem relation_swap_first_second {a b c : ℕ}
    {x : Fin 5 → Fin a → k} {y : Fin 5 → Fin b → k} {z : Fin 5 → Fin c → k}
    {q : Fin 5 → k} (h : IsProductRelation x y z q) :
    IsProductRelation y x z q := by
  apply funext
  intro j
  apply funext
  intro p
  apply funext
  intro l
  have hp := relation_pointwise h p j l
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, evalFactors,
    one_mul, smul_eq_mul]
  calc
    ∑ i, q i * (y i j * x i p * z i l) =
        ∑ i, q i * x i p * y i j * z i l := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 0 := hp

private theorem relation_rotate {a b c : ℕ}
    {x : Fin 5 → Fin a → k} {y : Fin 5 → Fin b → k} {z : Fin 5 → Fin c → k}
    {q : Fin 5 → k} (h : IsProductRelation x y z q) :
    IsProductRelation z x y q := by
  apply funext
  intro l
  apply funext
  intro p
  apply funext
  intro j
  have hp := relation_pointwise h p j l
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, evalFactors,
    one_mul, smul_eq_mul]
  calc
    ∑ i, q i * (z i l * x i p * y i j) =
        ∑ i, q i * x i p * y i j * z i l := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 0 := hp

/-- Five nonzero pure coordinate tensors forming a minimal dependence have total factor-span
rank at most six over every field. -/
theorem factorRank_sum_le_six {a b c : ℕ}
    (x : Fin 5 → Fin a → k) (y : Fin 5 → Fin b → k) (z : Fin 5 → Fin c → k)
    (hx0 : ∀ i, x i ≠ 0) (hy0 : ∀ i, y i ≠ 0) (hz0 : ∀ i, z i ≠ 0)
    (hminimal : IsMinimalFiveProductCircuit x y z) :
    familyRank (k := k) x + familyRank (k := k) y +
      familyRank (k := k) z ≤ 6 := by
  obtain ⟨q, hq, hrel⟩ := hminimal.1
  have hqall : ∀ i, q i ≠ 0 := by
    intro i hi
    exact hq (hminimal.2 q hrel ⟨i, hi⟩)
  by_cases hx3 : 3 ≤ familyRank (k := k) x
  · exact high_first_rank_sum_le_six x y z hy0 hz0 q hqall hrel hminimal.2 hx3
  by_cases hy3 : 3 ≤ familyRank (k := k) y
  · have hswap : IsMinimalFiveProductCircuit y x z := by
      constructor
      · exact ⟨q, hq, relation_swap_first_second hrel⟩
      · intro r hr hzero
        exact hminimal.2 r (relation_swap_first_second hr) hzero
    have hbound := high_first_rank_sum_le_six y x z hx0 hz0 q hqall
      (relation_swap_first_second hrel) hswap.2 hy3
    omega
  by_cases hz3 : 3 ≤ familyRank (k := k) z
  · have hrot : IsMinimalFiveProductCircuit z x y := by
      constructor
      · exact ⟨q, hq, relation_rotate hrel⟩
      · intro r hr hzero
        have hback : IsProductRelation x y z r :=
          relation_rotate (relation_rotate hr)
        exact hminimal.2 r hback hzero
    have hbound := high_first_rank_sum_le_six z x y hx0 hy0 q hqall
      (relation_rotate hrel) hrot.2 hz3
    omega
  omega

/-- A coefficient-minimal dependence of five tensors has tensor-family span rank exactly four. -/
theorem productFamilyRank_eq_four {a b c : ℕ}
    (x : Fin 5 → Fin a → k) (y : Fin 5 → Fin b → k) (z : Fin 5 → Fin c → k)
    (hminimal : IsMinimalFiveProductCircuit x y z) :
    familyRank (k := k) (productFamily x y z) = 4 := by
  let t := productFamily x y z
  have hdeleted : EveryDeletionIndependent (k := k) t :=
    (minimalFiveProductCircuit_iff x y z).mp hminimal |>.2
  let D : Submodule k (Tensor k a b c) :=
    Submodule.span k (Set.range (fun i : {i : Fin 5 // i ≠ 0} => t i.1))
  let S : Submodule k (Tensor k a b c) := Submodule.span k (Set.range t)
  have hDS : D ≤ S := by
    apply Submodule.span_mono
    rintro v ⟨i, rfl⟩
    exact Set.mem_range_self i.1
  have hD : Module.finrank k D = 4 := by
    rw [show D = Submodule.span k
      (Set.range (fun i : {i : Fin 5 // i ≠ 0} => t i.1)) from rfl,
      finrank_span_eq_card (hdeleted 0)]
    decide
  have hlower : 4 ≤ familyRank (k := k) t := by
    change 4 ≤ Module.finrank k S
    rw [← hD]
    exact Submodule.finrank_mono hDS
  have hnotLI : ¬LinearIndependent k t := by
    intro hLI
    obtain ⟨q, hq, hrel⟩ := hminimal.1
    have hsum : ∑ i, q i • t i = 0 := hrel
    have hqzero : ∀ i, q i = 0 :=
      (Fintype.linearIndependent_iff.mp hLI) q hsum
    apply hq
    funext i
    exact hqzero i
  have hupperFive : familyRank (k := k) t ≤ 5 := by
    simpa only [familyRank, Set.finrank, Fintype.card_fin] using
      (finrank_range_le_card (R := k) t)
  have hneFive : familyRank (k := k) t ≠ 5 := by
    intro heq
    apply hnotLI
    rw [linearIndependent_iff_card_eq_finrank_span]
    simpa only [familyRank, Set.finrank, Fintype.card_fin] using heq.symm
  change familyRank (k := k) t = 4
  omega

private theorem factor_expansion {a : ℕ} (x : Fin 5 → Fin a → k) :
    ∃ (basisVec : Fin (familyRank (k := k) x) → Fin a → k)
      (coeff : Fin 5 → Fin (familyRank (k := k) x) → k),
      ∀ i p, ∑ u, coeff i u * basisVec u p = x i p := by
  let X : Submodule k (Fin a → k) := Submodule.span k (Set.range x)
  let bx := Module.finBasis k X
  let xSub : Fin 5 → X := fun i => ⟨x i, Submodule.subset_span (Set.mem_range_self i)⟩
  refine ⟨fun u => (bx u).1, fun i u => bx.repr (xSub i) u, ?_⟩
  intro i p
  have h := congrArg Subtype.val (bx.sum_repr (xSub i))
  have hp := congrFun h p
  change (∑ u : Fin (Module.finrank k X),
    bx.repr (xSub i) u * (bx u).1 p) = x i p
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, xSub] using hp

/-- The span rank of a pure-tensor family is at most the product of its three factor-span ranks.
This uses only expansion in factor-span bases, not independence of their tensor products. -/
theorem productFamilyRank_le_factorRank_product {a b c : ℕ}
    (x : Fin 5 → Fin a → k) (y : Fin 5 → Fin b → k) (z : Fin 5 → Fin c → k) :
    familyRank (k := k) (productFamily x y z) ≤
      familyRank (k := k) x * familyRank (k := k) y * familyRank (k := k) z := by
  classical
  obtain ⟨bx, cx, hx⟩ := factor_expansion x
  obtain ⟨by', cy, hy⟩ := factor_expansion y
  obtain ⟨bz, cz, hz⟩ := factor_expansion z
  let I := Fin (familyRank (k := k) x) × Fin (familyRank (k := k) y) ×
    Fin (familyRank (k := k) z)
  let v : I → Tensor k a b c := fun p => evalFactors 1 (bx p.1) (by' p.2.1) (bz p.2.2)
  let L := Fintype.linearCombination k v
  have hmem (i : Fin 5) : productFamily x y z i ∈ L.range := by
    refine LinearMap.mem_range.mpr ⟨fun p => cx i p.1 * cy i p.2.1 * cz i p.2.2, ?_⟩
    funext p j l
    simp only [L, Fintype.linearCombination_apply, v, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, evalFactors, one_mul, productFamily,
      I, Fintype.sum_prod_type]
    calc
      (∑ u, ∑ w, ∑ s,
        (cx i u * cy i w * cz i s) * (bx u p * by' w j * bz s l)) =
          (∑ u, cx i u * bx u p) * (∑ w, cy i w * by' w j) *
            ∑ s, cz i s * bz s l := by
        simp only [mul_assoc, Finset.sum_mul]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro w hw
        apply Finset.sum_congr rfl
        intro s hs
        ring
      _ = x i p * y i j * z i l := by rw [hx, hy, hz]
  have hspan : Submodule.span k (Set.range (productFamily x y z)) ≤ L.range := by
    apply Submodule.span_le.mpr
    rintro v' ⟨i, rfl⟩
    exact hmem i
  calc
    familyRank (k := k) (productFamily x y z) ≤ Module.finrank k L.range :=
      Submodule.finrank_mono hspan
    _ ≤ Module.finrank k (I → k) := L.finrank_range_le
    _ = familyRank (k := k) x * familyRank (k := k) y * familyRank (k := k) z := by
      simp only [Module.finrank_pi, I, Fintype.card_prod, Fintype.card_fin, mul_assoc]

/-- The product of the factor-span ranks of a coefficient-minimal five-product circuit is
at least four. -/
theorem four_le_factorRank_product {a b c : ℕ}
    (x : Fin 5 → Fin a → k) (y : Fin 5 → Fin b → k) (z : Fin 5 → Fin c → k)
    (hminimal : IsMinimalFiveProductCircuit x y z) :
    4 ≤ familyRank (k := k) x * familyRank (k := k) y * familyRank (k := k) z := by
  rw [← productFamilyRank_eq_four x y z hminimal]
  exact productFamilyRank_le_factorRank_product x y z

/-- A family containing a nonzero vector has positive span rank. -/
theorem one_le_familyRank {a : ℕ} (x : Fin 5 → Fin a → k) (hx : x 0 ≠ 0) :
    1 ≤ familyRank (k := k) x := by
  have hspan : Submodule.span k {x 0} ≤ Submodule.span k (Set.range x) := by
    apply Submodule.span_mono
    intro v hv
    obtain rfl := Set.mem_singleton_iff.mp hv
    exact Set.mem_range_self 0
  have hsingle : Module.finrank k (Submodule.span k {x 0}) = 1 :=
    finrank_span_singleton hx
  rw [← hsingle]
  exact Submodule.finrank_mono hspan

private theorem profile_of_bounds (r s t : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hsum : r + s + t ≤ 6) (hprod : 4 ≤ r * s * t) :
    [r, s, t].Perm [4, 1, 1] ∨ [r, s, t].Perm [3, 2, 1] ∨
      [r, s, t].Perm [2, 2, 1] ∨ [r, s, t].Perm [2, 2, 2] := by
  have hr4 : r ≤ 4 := by omega
  have hs4 : s ≤ 4 := by omega
  have ht4 : t ≤ 4 := by omega
  interval_cases r <;> interval_cases s <;> interval_cases t <;>
    first | omega | decide

/-- Over every field, the factor-span ranks of a nonzero minimal five-product circuit have,
up to mode permutation, one of the four profiles `411`, `321`, `221`, or `222`. -/
theorem factorRank_profile {a b c : ℕ}
    (x : Fin 5 → Fin a → k) (y : Fin 5 → Fin b → k) (z : Fin 5 → Fin c → k)
    (hx0 : ∀ i, x i ≠ 0) (hy0 : ∀ i, y i ≠ 0) (hz0 : ∀ i, z i ≠ 0)
    (hminimal : IsMinimalFiveProductCircuit x y z) :
    [familyRank (k := k) x, familyRank (k := k) y, familyRank (k := k) z].Perm [4, 1, 1] ∨
    [familyRank (k := k) x, familyRank (k := k) y, familyRank (k := k) z].Perm [3, 2, 1] ∨
    [familyRank (k := k) x, familyRank (k := k) y, familyRank (k := k) z].Perm [2, 2, 1] ∨
    [familyRank (k := k) x, familyRank (k := k) y, familyRank (k := k) z].Perm [2, 2, 2] := by
  have hxpos := one_le_familyRank x (hx0 0)
  have hypos := one_le_familyRank y (hy0 0)
  have hzpos := one_le_familyRank z (hz0 0)
  have hsum := factorRank_sum_le_six x y z hx0 hy0 hz0 hminimal
  have hprod := four_le_factorRank_product x y z hminimal
  exact profile_of_bounds _ _ _ hxpos hypos hzpos hsum hprod

namespace F3Fixture

open FieldContextual.F3Profile221

/-- First-factor coordinates for the genuine ternary five-circuit fixture. The coefficients `2`
on the third and fourth tensors are absorbed into this factor. -/
def first : Fin 5 → Fin 2 → F3 :=
  ![e0, e1, (2 : F3) • e0, (2 : F3) • e1, e0 + e1]

/-- Second-factor coordinates for the genuine ternary five-circuit fixture. -/
def second : Fin 5 → Fin 2 → F3 :=
  ![e0, e1, e1, e0, e0 + e1]

/-- Third-factor coordinates for the genuine ternary five-circuit fixture. -/
def third : Fin 5 → Fin 1 → F3 := fun _ => unit

example : first 0 = e0 := rfl
example : first 2 = (2 : F3) • e0 := rfl
example : second 3 = e0 := rfl
example : third 4 = unit := rfl

/-- Every displayed factor of the ternary fixture is nonzero. -/
theorem factors_nonzero :
    (∀ i, first i ≠ 0) ∧ (∀ i, second i ≠ 0) ∧ (∀ i, third i ≠ 0) := by
  constructor
  · intro i
    fin_cases i <;> decide
  constructor
  · intro i
    fin_cases i <;> decide
  · intro i
    fin_cases i <;> decide

/-- The coordinate factors evaluate to the existing ordered ternary fixture family
`(A, B, 2C, 2D, J)`. -/
theorem productFamily_eq_fixtureFamily :
    productFamily first second third = fixtureFamily := by
  funext i p j l
  fin_cases i <;> fin_cases p <;> fin_cases j <;> fin_cases l <;> decide

/-- The displayed ternary factors form a genuine coefficient-minimal five-product circuit. -/
theorem isMinimalFiveProductCircuit :
    IsMinimalFiveProductCircuit first second third := by
  change
    (∃ q : Fin 5 → F3, q ≠ 0 ∧
      ∑ i, q i • productFamily first second third i = 0) ∧
    ∀ q : Fin 5 → F3, (∑ i, q i • productFamily first second third i = 0) →
      (∃ i, q i = 0) → q = 0
  rw [productFamily_eq_fixtureFamily]
  exact fixture_is_circuit

example : (∀ i, first i ≠ 0) ∧ (∀ i, second i ≠ 0) ∧ (∀ i, third i ≠ 0) ∧
    IsMinimalFiveProductCircuit first second third :=
  ⟨factors_nonzero.1, factors_nonzero.2.1, factors_nonzero.2.2, isMinimalFiveProductCircuit⟩

/-- The ternary fixture has the signed relation `(1,1,2,2,2)`, not a binary subset relation. -/
theorem signed_relation : IsProductRelation first second third fixtureSigned := by
  change ∑ i, fixtureSigned i • productFamily first second third i = 0
  rw [productFamily_eq_fixtureFamily]
  exact fixtureSigned_relation

/-- The arbitrary-field rank-sum theorem specializes to the genuine nonbinary `ZMod 3`
coefficient-minimal fixture. -/
theorem factorRank_sum_le_six :
    familyRank (k := F3) first + familyRank (k := F3) second +
      familyRank (k := F3) third ≤ 6 := by
  exact FieldFiveCircuitProfile.factorRank_sum_le_six first second third
    factors_nonzero.1 factors_nonzero.2.1 factors_nonzero.2.2
    isMinimalFiveProductCircuit

/-- The factor-span ranks of the actual ternary fixture are exactly `(2,2,1)`. -/
theorem factorRanks_eq_221 :
    familyRank (k := F3) first = 2 ∧ familyRank (k := F3) second = 2 ∧
      familyRank (k := F3) third = 1 := by
  have hr : familyRank (k := F3) first ≤ 2 := by
    have h := Submodule.finrank_le (Submodule.span F3 (Set.range first))
    simpa only [familyRank, Module.finrank_pi, Fintype.card_fin] using h
  have hs : familyRank (k := F3) second ≤ 2 := by
    have h := Submodule.finrank_le (Submodule.span F3 (Set.range second))
    simpa only [familyRank, Module.finrank_pi, Fintype.card_fin] using h
  have ht : familyRank (k := F3) third = 1 := by
    have hle : familyRank (k := F3) third ≤ 1 := by
      have h := Submodule.finrank_le (Submodule.span F3 (Set.range third))
      simpa only [familyRank, Module.finrank_pi, Fintype.card_fin] using h
    have hpos := one_le_familyRank third (factors_nonzero.2.2 0)
    omega
  have hprod := four_le_factorRank_product first second third isMinimalFiveProductCircuit
  rw [ht, mul_one] at hprod
  have hmul : familyRank (k := F3) first * familyRank (k := F3) second ≤ 4 := by
    exact Nat.mul_le_mul hr hs
  have hr2 : familyRank (k := F3) first = 2 := by nlinarith
  have hs2 : familyRank (k := F3) second = 2 := by nlinarith
  exact ⟨hr2, hs2, ht⟩

end F3Fixture

#check @vanishing_relation_iff_everyDeletionIndependent
#check @minimalFiveProductCircuit_iff
#check @EveryDeletionIndependent.linearIndependent_restrict
#check @factorRank_sum_le_six
#check @productFamilyRank_eq_four
#check @productFamilyRank_le_factorRank_product
#check @four_le_factorRank_product
#check @one_le_familyRank
#check @factorRank_profile
#check @F3Fixture.factors_nonzero
#check @F3Fixture.productFamily_eq_fixtureFamily
#check @F3Fixture.isMinimalFiveProductCircuit
#check @F3Fixture.signed_relation
#check @F3Fixture.factorRank_sum_le_six
#check @F3Fixture.factorRanks_eq_221

#print axioms vanishing_relation_iff_everyDeletionIndependent
#print axioms minimalFiveProductCircuit_iff
#print axioms EveryDeletionIndependent.linearIndependent_restrict
#print axioms factorRank_sum_le_six
#print axioms productFamilyRank_eq_four
#print axioms productFamilyRank_le_factorRank_product
#print axioms four_le_factorRank_product
#print axioms one_le_familyRank
#print axioms factorRank_profile
#print axioms F3Fixture.factors_nonzero
#print axioms F3Fixture.productFamily_eq_fixtureFamily
#print axioms F3Fixture.isMinimalFiveProductCircuit
#print axioms F3Fixture.signed_relation
#print axioms F3Fixture.factorRank_sum_le_six
#print axioms F3Fixture.factorRanks_eq_221

end FieldFiveCircuitProfile
end BilinearComplexity
