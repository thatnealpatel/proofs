import BilinearComplexity.FiveCircuit
import BilinearComplexity.PairTripleSpan

set_option autoImplicit false

open scoped BigOperators

/-!
# Binary five-circuit profile inequality

This module proves the direct coordinate endpoint for five distinct nonzero
binary pure tensors in a two-equals-three relation.  Its public consequences
bound the three factor-span ranks, express the equivalent positive-rank
inequality, and classify the resulting unordered rank profiles.

The proof is coordinate-linear algebra over `ZMod 2`.  It introduces no move,
graph, certificate, or scheme-search infrastructure.

AI disclosure: produced with AI assistance (see `Proofs/README`).
-/

namespace BilinearComplexity

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem two_mode_cancellation_finrank_le
    {ι : Type*} [Fintype ι] {b c : ℕ}
    (u : ι → Fin b → ZMod 2) (v : ι → Fin c → ZMod 2)
    (hzero : ∀ j k, ∑ i, u i j * v i k = 0) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range u)) +
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range v)) ≤
      Fintype.card ι := by
  classical
  let U : Matrix (Fin b) ι (ZMod 2) := fun j i => u i j
  let V : Matrix ι (Fin c) (ZMod 2) := fun i k => v i k
  have hUV : U * V = 0 := by
    ext j k
    change (∑ i, u i j * v i k) = 0
    exact hzero j k
  have hUcol : U.col = u := by
    funext i j
    rfl
  have hUrank : U.rank =
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range u)) := by
    rw [Matrix.rank_eq_finrank_span_cols, hUcol]
  have hVcol : V.transpose.col = v := by
    funext i k
    rfl
  have hVrank : V.rank =
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range v)) := by
    rw [← Matrix.rank_transpose V, Matrix.rank_eq_finrank_span_cols, hVcol]
  rw [← hUrank, ← hVrank]
  exact Matrix.rank_add_rank_le_card_of_mul_eq_zero hUV

private theorem finrank_sup_add_one_le_of_common_nonzero
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (P Q : Submodule K V) [FiniteDimensional K P] [FiniteDimensional K Q]
    {x : V} (hxP : x ∈ P) (hxQ : x ∈ Q) (hx : x ≠ 0) :
    Module.finrank K (P ⊔ Q : Submodule K V) + 1 ≤
      Module.finrank K P + Module.finrank K Q := by
  have hxInf : x ∈ (P ⊓ Q : Submodule K V) := ⟨hxP, hxQ⟩
  have hInf : (P ⊓ Q : Submodule K V) ≠ ⊥ := by
    intro hbot
    apply hx
    have hxBot : x ∈ (⊥ : Submodule K V) := by
      rw [← hbot]
      exact hxInf
    simpa using hxBot
  have hOne : 1 ≤ Module.finrank K (P ⊓ Q : Submodule K V) :=
    Submodule.one_le_finrank_iff.mpr hInf
  rw [← Submodule.finrank_sup_add_finrank_inf_eq P Q]
  exact Nat.add_le_add_left hOne _

private theorem cancellation_with_singleton_finrank_le
    {ι : Type*} [Fintype ι] {b c : ℕ}
    (u : ι → Fin b → ZMod 2) (v : ι → Fin c → ZMod 2)
    (u₀ : Fin b → ZMod 2) (v₀ : Fin c → ZMod 2)
    (hzero : ∀ j k, (∑ i, u i j * v i k) + u₀ j * v₀ k = 0) :
    Module.finrank (ZMod 2)
          (Submodule.span (ZMod 2) (Set.range u ∪ {u₀})) +
        Module.finrank (ZMod 2)
          (Submodule.span (ZMod 2) (Set.range v ∪ {v₀})) ≤
      Fintype.card ι + 1 := by
  classical
  let u' : ι ⊕ Unit → Fin b → ZMod 2 := Sum.elim u (fun _ => u₀)
  let v' : ι ⊕ Unit → Fin c → ZMod 2 := Sum.elim v (fun _ => v₀)
  have hzero' : ∀ j k, ∑ i, u' i j * v' i k = 0 := by
    intro j k
    rw [Fintype.sum_sum_type]
    simpa only [u', v', Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique] using
      hzero j k
  have huRange : Set.range u' = Set.range u ∪ {u₀} := by
    ext z
    simp [u']
  have hvRange : Set.range v' = Set.range v ∪ {v₀} := by
    ext z
    simp [v']
  have hbound := two_mode_cancellation_finrank_le u' v' hzero'
  rw [huRange, hvRange] at hbound
  simpa only [Fintype.card_sum, Fintype.card_unit] using hbound

private theorem f2_finrank_two_range_profile
    {ι : Type*} [Fintype ι] {a : ℕ} (u : ι → Fin a → ZMod 2)
    (hu : ∀ i, u i ≠ 0)
    (hdim : Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range u)) = 2) :
    ∃ i₀ i₁ : ι, i₀ ≠ i₁ ∧
      LinearIndependent (ZMod 2) ![u i₀, u i₁] ∧
      ∀ i, u i = u i₀ ∨ u i = u i₁ ∨ u i = u i₀ + u i₁ := by
  classical
  have hbasis := Submodule.exists_fun_fin_finrank_span_eq
    (K := ZMod 2) (s := Set.range u)
  rw [hdim] at hbasis
  obtain ⟨f, hfRange, hfSpan, hfLI⟩ := hbasis
  obtain ⟨i₀, hi₀⟩ := hfRange 0
  obtain ⟨i₁, hi₁⟩ := hfRange 1
  have hfamily : (![u i₀, u i₁] : Fin 2 → Fin a → ZMod 2) = f := by
    funext q
    fin_cases q
    · exact hi₀
    · exact hi₁
  have hpair : LinearIndependent (ZMod 2) ![u i₀, u i₁] := by
    rw [hfamily]
    exact hfLI
  have hne : i₀ ≠ i₁ := by
    intro heq
    subst i₁
    have hzero : (1 : ZMod 2) • u i₀ + (1 : ZMod 2) • u i₀ = 0 := by
      simpa only [one_smul] using PairTripleSpan.add_self_eq_zero_f2 (u i₀)
    have hone := (hpair.eq_zero_of_pair hzero).1
    exact one_ne_zero hone
  refine ⟨i₀, i₁, hne, hpair, ?_⟩
  intro i
  have hui : u i ∈ Submodule.span (ZMod 2) (Set.range u) :=
    Submodule.subset_span (Set.mem_range_self i)
  rw [← hfSpan, Submodule.mem_span_range_iff_exists_fun] at hui
  obtain ⟨coeff, hcoeff⟩ := hui
  rw [Fin.sum_univ_two, ← hi₀, ← hi₁] at hcoeff
  rcases PairTripleSpan.scalar_eq_zero_or_one (coeff 0) with hzero | hone <;>
    rcases PairTripleSpan.scalar_eq_zero_or_one (coeff 1) with hzero' | hone'
  · have huiZero : u i = 0 := by
      simpa only [hzero, hzero', zero_smul, zero_add] using hcoeff.symm
    exact (hu i huiZero).elim
  · exact Or.inr (Or.inl (by
      simpa only [hzero, hone', zero_smul, one_smul, zero_add] using hcoeff.symm))
  · exact Or.inl (by
      simpa only [hone, hzero', one_smul, zero_smul, add_zero] using hcoeff.symm)
  · exact Or.inr (Or.inr (by
      simpa only [hone, hone', one_smul] using hcoeff.symm))

private theorem three_fiber_sums_eq
    {a b c : ℕ} (x y : Fin a → ZMod 2)
    (A B C : Fin b → Fin c → ZMod 2)
    (hxy : LinearIndependent (ZMod 2) ![x, y])
    (hrel : ∀ p j k,
      x p * A j k + y p * B j k + (x p + y p) * C j k = 0) :
    A = C ∧ B = C := by
  have hentry : ∀ j k, A j k = C j k ∧ B j k = C j k := by
    intro j k
    have hcoeff :
        (A j k + C j k) • x + (B j k + C j k) • y = 0 := by
      funext p
      change (A j k + C j k) * x p + (B j k + C j k) * y p = 0
      calc
        (A j k + C j k) * x p + (B j k + C j k) * y p =
            x p * A j k + y p * B j k + (x p + y p) * C j k := by ring
        _ = 0 := hrel p j k
    obtain ⟨hAC, hBC⟩ := hxy.eq_zero_of_pair hcoeff
    exact ⟨(PairTripleSpan.add_eq_zero_iff_eq_f2 _ _).mp hAC,
      (PairTripleSpan.add_eq_zero_iff_eq_f2 _ _).mp hBC⟩
  constructor <;> funext j k
  · exact (hentry j k).1
  · exact (hentry j k).2

private theorem matrix_sum_ne_zero_of_minimal_constant_fiber
    {ι : Type*} [Fintype ι] [DecidableEq ι] {a b c : ℕ}
    (u : ι → Fin a → ZMod 2) (v : ι → Fin b → ZMod 2)
    (w : ι → Fin c → ZMod 2) (S : Finset ι) (x : Fin a → ZMod 2)
    (hMinimal : ∀ T : Finset ι,
      (∀ p j k, ∑ i ∈ T, u i p * v i j * w i k = 0) →
        T = ∅ ∨ T = Finset.univ)
    (hS : S.Nonempty) (hProper : S ≠ Finset.univ)
    (hConstant : ∀ i ∈ S, u i = x) :
    (fun j k => ∑ i ∈ S, v i j * w i k) ≠ 0 := by
  intro hMatrix
  have hzero : ∀ p j k, ∑ i ∈ S, u i p * v i j * w i k = 0 := by
    intro p j k
    calc
      (∑ i ∈ S, u i p * v i j * w i k) =
          ∑ i ∈ S, x p * (v i j * w i k) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hConstant i hi]
            ring
      _ = x p * ∑ i ∈ S, v i j * w i k := by
        rw [Finset.mul_sum]
      _ = 0 := by
        have hentry : (∑ i ∈ S, v i j * w i k) = 0 := by
          simpa using congrFun (congrFun hMatrix j) k
        rw [hentry, mul_zero]
  rcases hMinimal S hzero with hEmpty | hUniv
  · exact (hS.ne_empty hEmpty).elim
  · exact hProper hUniv

private theorem fiber_nonempty_of_matrix_sum_ne_zero
    {ι : Type*} [DecidableEq ι] {b c : ℕ}
    (v : ι → Fin b → ZMod 2) (w : ι → Fin c → ZMod 2) (S : Finset ι)
    (h : (fun j k => ∑ i ∈ S, v i j * w i k) ≠ 0) :
    S.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hEmpty
  apply h
  rw [hEmpty]
  funext j k
  simp

private theorem three_one_one_finrank_le_four
    {b c : ℕ} (u : Fin 3 → Fin b → ZMod 2) (v : Fin 3 → Fin c → ZMod 2)
    (u₀ u₁ : Fin b → ZMod 2) (v₀ v₁ : Fin c → ZMod 2)
    (hu₀ : u₀ ≠ 0) (hu₁ : u₁ ≠ 0) (hv₀ : v₀ ≠ 0) (hv₁ : v₁ ≠ 0)
    (hzero : ∀ j k, (∑ i, u i j * v i k) + u₀ j * v₀ k = 0)
    (hSingletons : ∀ j k, u₀ j * v₀ k = u₁ j * v₁ k) :
    Module.finrank (ZMod 2)
          (Submodule.span (ZMod 2) (Set.range u ∪ {u₀, u₁})) +
        Module.finrank (ZMod 2)
          (Submodule.span (ZMod 2) (Set.range v ∪ {v₀, v₁})) ≤ 4 := by
  have hOuter : Matrix.vecMulVec u₀ v₀ = Matrix.vecMulVec u₁ v₁ := by
    ext j k
    exact hSingletons j k
  obtain ⟨hu, hv⟩ := PairTripleSpan.vecMulVec_eq_vecMulVec
    hu₀ hv₀ hu₁ hv₁ hOuter
  subst u₁
  subst v₁
  have huSet : Set.range u ∪ {u₀, u₀} = Set.range u ∪ {u₀} := by
    rw [Set.pair_eq_singleton]
  have hvSet : Set.range v ∪ {v₀, v₀} = Set.range v ∪ {v₀} := by
    rw [Set.pair_eq_singleton]
  rw [huSet, hvSet]
  simpa only [Fintype.card_fin] using
    cancellation_with_singleton_finrank_le u v u₀ v₀ hzero

private theorem two_two_one_finrank_le_four
    {b c : ℕ}
    (uA uB : Fin 2 → Fin b → ZMod 2)
    (vA vB : Fin 2 → Fin c → ZMod 2)
    (u₀ : Fin b → ZMod 2) (v₀ : Fin c → ZMod 2)
    (hu₀ : u₀ ≠ 0) (hv₀ : v₀ ≠ 0)
    (hA : ∀ j k, (∑ i, uA i j * vA i k) + u₀ j * v₀ k = 0)
    (hB : ∀ j k, (∑ i, uB i j * vB i k) + u₀ j * v₀ k = 0) :
    Module.finrank (ZMod 2)
          ((Submodule.span (ZMod 2) (Set.range uA ∪ {u₀})) ⊔
            Submodule.span (ZMod 2) (Set.range uB ∪ {u₀}) :
            Submodule (ZMod 2) (Fin b → ZMod 2)) +
        Module.finrank (ZMod 2)
          ((Submodule.span (ZMod 2) (Set.range vA ∪ {v₀})) ⊔
            Submodule.span (ZMod 2) (Set.range vB ∪ {v₀}) :
            Submodule (ZMod 2) (Fin c → ZMod 2)) ≤ 4 := by
  let Pu := Submodule.span (ZMod 2) (Set.range uA ∪ {u₀})
  let Qu := Submodule.span (ZMod 2) (Set.range uB ∪ {u₀})
  let Pv := Submodule.span (ZMod 2) (Set.range vA ∪ {v₀})
  let Qv := Submodule.span (ZMod 2) (Set.range vB ∪ {v₀})
  have hLocalA : Module.finrank (ZMod 2) Pu + Module.finrank (ZMod 2) Pv ≤ 3 := by
    simpa only [Pu, Pv, Fintype.card_fin] using
      cancellation_with_singleton_finrank_le uA vA u₀ v₀ hA
  have hLocalB : Module.finrank (ZMod 2) Qu + Module.finrank (ZMod 2) Qv ≤ 3 := by
    simpa only [Qu, Qv, Fintype.card_fin] using
      cancellation_with_singleton_finrank_le uB vB u₀ v₀ hB
  have huPu : u₀ ∈ Pu := by
    apply Submodule.subset_span
    exact Set.mem_union_right _ (Set.mem_singleton u₀)
  have huQu : u₀ ∈ Qu := by
    apply Submodule.subset_span
    exact Set.mem_union_right _ (Set.mem_singleton u₀)
  have hvPv : v₀ ∈ Pv := by
    apply Submodule.subset_span
    exact Set.mem_union_right _ (Set.mem_singleton v₀)
  have hvQv : v₀ ∈ Qv := by
    apply Submodule.subset_span
    exact Set.mem_union_right _ (Set.mem_singleton v₀)
  have hOverlapU : Module.finrank (ZMod 2)
        (Pu ⊔ Qu : Submodule (ZMod 2) (Fin b → ZMod 2)) + 1 ≤
      Module.finrank (ZMod 2) Pu + Module.finrank (ZMod 2) Qu :=
    finrank_sup_add_one_le_of_common_nonzero Pu Qu huPu huQu hu₀
  have hOverlapV : Module.finrank (ZMod 2)
        (Pv ⊔ Qv : Submodule (ZMod 2) (Fin c → ZMod 2)) + 1 ≤
      Module.finrank (ZMod 2) Pv + Module.finrank (ZMod 2) Qv :=
    finrank_sup_add_one_le_of_common_nonzero Pv Qv hvPv hvQv hv₀
  change Module.finrank (ZMod 2)
        (Pu ⊔ Qu : Submodule (ZMod 2) (Fin b → ZMod 2)) +
      Module.finrank (ZMod 2)
        (Pv ⊔ Qv : Submodule (ZMod 2) (Fin c → ZMod 2)) ≤ 4
  omega

private theorem three_positive_sum_five
    {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hsum : p + q + r = 5) :
    (p = 3 ∧ q = 1 ∧ r = 1) ∨
    (p = 1 ∧ q = 3 ∧ r = 1) ∨
    (p = 1 ∧ q = 1 ∧ r = 3) ∨
    (p = 2 ∧ q = 2 ∧ r = 1) ∨
    (p = 2 ∧ q = 1 ∧ r = 2) ∨
    (p = 1 ∧ q = 2 ∧ r = 2) := by
  omega

private theorem finrank_span_range_le_two_of_tail_mem_pair_span
    {a : ℕ} (u : Fin 5 → Fin a → ZMod 2)
    (h : ∀ i : Fin 3, u i.succ.succ ∈
      Submodule.span (ZMod 2) ({u 0, u 1} : Set (Fin a → ZMod 2))) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range u)) ≤ 2 := by
  classical
  let P := Submodule.span (ZMod 2) ({u 0, u 1} : Set (Fin a → ZMod 2))
  have hrange : Set.range u ⊆ P := by
    rintro z ⟨i, rfl⟩
    fin_cases i
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · simpa [P] using h 0
    · simpa [P] using h 1
    · simpa [P] using h 2
  calc
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range u)) ≤
        Module.finrank (ZMod 2) P :=
      Submodule.finrank_mono (Submodule.span_le.mpr hrange)
    _ ≤ 2 := by
      dsimp only [P]
      calc
        Module.finrank (ZMod 2)
            (Submodule.span (ZMod 2) ({u 0, u 1} : Set (Fin a → ZMod 2))) ≤
            ({u 0, u 1} : Set (Fin a → ZMod 2)).toFinset.card :=
          finrank_span_le_card _
        _ ≤ 2 := by
          simpa only [Set.toFinset_insert, Set.toFinset_singleton] using
            (Finset.card_le_two : ({u 0, u 1} :
              Finset (Fin a → ZMod 2)).card ≤ 2)

private theorem selected_mode_finrank_one_profile_le_six
    {a b c : ℕ}
    (u : Fin 5 → Fin a → ZMod 2)
    (v : Fin 5 → Fin b → ZMod 2)
    (w : Fin 5 → Fin c → ZMod 2)
    (hu : ∀ i, u i ≠ 0)
    (hzero : ∀ p j k, ∑ i, u i p * v i j * w i k = 0)
    (hdim : Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range u)) = 1) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range u)) +
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range v)) +
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range w)) ≤ 6 := by
  classical
  let P := Submodule.span (ZMod 2) (Set.range u)
  have hu0P : u 0 ∈ P := Submodule.subset_span (Set.mem_range_self 0)
  have hP : P = Submodule.span (ZMod 2) ({u 0} : Set (Fin a → ZMod 2)) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdim hu0P (hu 0)
  have hconst : ∀ i, u i = u 0 := by
    intro i
    have huiP : u i ∈ P := Submodule.subset_span (Set.mem_range_self i)
    rw [hP, Submodule.mem_span_singleton] at huiP
    obtain ⟨r, hr⟩ := huiP
    rcases PairTripleSpan.scalar_eq_zero_or_one r with rfl | rfl
    · simp only [zero_smul] at hr
      exact (hu i hr.symm).elim
    · simpa only [one_smul] using hr.symm
  obtain ⟨p, hp⟩ := PairTripleSpan.exists_apply_ne_zero (hu 0)
  have hpone : u 0 p = 1 := PairTripleSpan.eq_one_of_ne_zero hp
  have hmatrix : ∀ j k, ∑ i, v i j * w i k = 0 := by
    intro j k
    simpa only [hconst, hpone, one_mul] using hzero p j k
  have hvw := two_mode_cancellation_finrank_le v w hmatrix
  have hvw' : Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range v)) +
      Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range w)) ≤ 5 := by
    simpa only [Fintype.card_fin] using hvw
  rw [hdim]
  omega

private theorem three_one_one_finset_finrank_le_four
    {b c : ℕ} (v : Fin 5 → Fin b → ZMod 2)
    (w : Fin 5 → Fin c → ZMod 2)
    (S T R : Finset (Fin 5))
    (hcover : (S ∪ T) ∪ R = Finset.univ)
    (hScard : S.card = 3) (hTcard : T.card = 1) (hRcard : R.card = 1)
    (hv : ∀ i, v i ≠ 0) (hw : ∀ i, w i ≠ 0)
    (heqST : ∀ j k, (∑ i ∈ S, v i j * w i k) =
      ∑ i ∈ T, v i j * w i k)
    (heqSR : ∀ j k, (∑ i ∈ S, v i j * w i k) =
      ∑ i ∈ R, v i j * w i k) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range v)) +
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range w)) ≤ 4 := by
  classical
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hTcard
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hRcard
  subst T
  subst R
  let eS : Fin 3 ≃ S :=
    (Equiv.cast (congrArg Fin hScard.symm)).trans S.equivFin.symm
  let vS : Fin 3 → Fin b → ZMod 2 := fun q => v (eS q)
  let wS : Fin 3 → Fin c → ZMod 2 := fun q => w (eS q)
  have hsumS : ∀ j k, (∑ q, vS q j * wS q k) =
      ∑ i ∈ S, v i j * w i k := by
    intro j k
    calc
      (∑ q, vS q j * wS q k) =
          ∑ q : S, v q j * w q k := eS.sum_comp (fun q : S => v q j * w q k)
      _ = ∑ i ∈ S, v i j * w i k := by
        change (∑ i ∈ S.attach, v i j * w i k) = _
        exact Finset.sum_attach S (fun i => v i j * w i k)
  have hRangeVS : Set.range vS = v '' (S : Set (Fin 5)) := by
    ext z
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨eS q, (eS q).property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨eS.symm ⟨i, hi⟩, ?_⟩
      simp only [vS, eS.apply_symm_apply]
  have hRangeWS : Set.range wS = w '' (S : Set (Fin 5)) := by
    ext z
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨eS q, (eS q).property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨eS.symm ⟨i, hi⟩, ?_⟩
      simp only [wS, eS.apply_symm_apply]
  have hRangeV : Set.range v = Set.range vS ∪ {v t, v r} := by
    rw [hRangeVS]
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      have hi : i ∈ (S ∪ {t}) ∪ {r} := by rw [hcover]; simp
      simp only [Finset.mem_union, Finset.mem_singleton] at hi
      rcases hi with (hiS | rfl) | rfl
      · exact Or.inl ⟨i, hiS, rfl⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rintro (⟨i, -, rfl⟩ | rfl | rfl)
      all_goals exact ⟨_, rfl⟩
  have hRangeW : Set.range w = Set.range wS ∪ {w t, w r} := by
    rw [hRangeWS]
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      have hi : i ∈ (S ∪ {t}) ∪ {r} := by rw [hcover]; simp
      simp only [Finset.mem_union, Finset.mem_singleton] at hi
      rcases hi with (hiS | rfl) | rfl
      · exact Or.inl ⟨i, hiS, rfl⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rintro (⟨i, -, rfl⟩ | rfl | rfl)
      all_goals exact ⟨_, rfl⟩
  have hzeroLocal : ∀ j k,
      (∑ q, vS q j * wS q k) + v t j * w t k = 0 := by
    intro j k
    apply (PairTripleSpan.add_eq_zero_iff_eq_f2 _ _).mpr
    rw [hsumS]
    simpa only [Finset.sum_singleton] using heqST j k
  have hSingletons : ∀ j k, v t j * w t k = v r j * w r k := by
    intro j k
    have heq := (heqST j k).symm.trans (heqSR j k)
    simpa only [Finset.sum_singleton] using heq
  have hlocal := three_one_one_finrank_le_four vS wS
    (v t) (v r) (w t) (w r) (hv t) (hv r) (hw t) (hw r)
    hzeroLocal hSingletons
  rw [← hRangeV, ← hRangeW] at hlocal
  exact hlocal

private theorem two_two_one_finset_finrank_le_four
    {b c : ℕ} (v : Fin 5 → Fin b → ZMod 2)
    (w : Fin 5 → Fin c → ZMod 2)
    (S T R : Finset (Fin 5))
    (hcover : (S ∪ T) ∪ R = Finset.univ)
    (hScard : S.card = 2) (hTcard : T.card = 2) (hRcard : R.card = 1)
    (hv : ∀ i, v i ≠ 0) (hw : ∀ i, w i ≠ 0)
    (heqSR : ∀ j k, (∑ i ∈ S, v i j * w i k) =
      ∑ i ∈ R, v i j * w i k)
    (heqTR : ∀ j k, (∑ i ∈ T, v i j * w i k) =
      ∑ i ∈ R, v i j * w i k) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range v)) +
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range w)) ≤ 4 := by
  classical
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hRcard
  subst R
  let eS : Fin 2 ≃ S :=
    (Equiv.cast (congrArg Fin hScard.symm)).trans S.equivFin.symm
  let eT : Fin 2 ≃ T :=
    (Equiv.cast (congrArg Fin hTcard.symm)).trans T.equivFin.symm
  let vS : Fin 2 → Fin b → ZMod 2 := fun q => v (eS q)
  let wS : Fin 2 → Fin c → ZMod 2 := fun q => w (eS q)
  let vT : Fin 2 → Fin b → ZMod 2 := fun q => v (eT q)
  let wT : Fin 2 → Fin c → ZMod 2 := fun q => w (eT q)
  have hsumS : ∀ j k, (∑ q, vS q j * wS q k) =
      ∑ i ∈ S, v i j * w i k := by
    intro j k
    calc
      (∑ q, vS q j * wS q k) =
          ∑ q : S, v q j * w q k := eS.sum_comp (fun q : S => v q j * w q k)
      _ = ∑ i ∈ S, v i j * w i k := by
        change (∑ i ∈ S.attach, v i j * w i k) = _
        exact Finset.sum_attach S (fun i => v i j * w i k)
  have hsumT : ∀ j k, (∑ q, vT q j * wT q k) =
      ∑ i ∈ T, v i j * w i k := by
    intro j k
    calc
      (∑ q, vT q j * wT q k) =
          ∑ q : T, v q j * w q k := eT.sum_comp (fun q : T => v q j * w q k)
      _ = ∑ i ∈ T, v i j * w i k := by
        change (∑ i ∈ T.attach, v i j * w i k) = _
        exact Finset.sum_attach T (fun i => v i j * w i k)
  have hRangeVS : Set.range vS = v '' (S : Set (Fin 5)) := by
    ext z
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨eS q, (eS q).property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨eS.symm ⟨i, hi⟩, ?_⟩
      simp only [vS, eS.apply_symm_apply]
  have hRangeWS : Set.range wS = w '' (S : Set (Fin 5)) := by
    ext z
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨eS q, (eS q).property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨eS.symm ⟨i, hi⟩, ?_⟩
      simp only [wS, eS.apply_symm_apply]
  have hRangeVT : Set.range vT = v '' (T : Set (Fin 5)) := by
    ext z
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨eT q, (eT q).property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨eT.symm ⟨i, hi⟩, ?_⟩
      simp only [vT, eT.apply_symm_apply]
  have hRangeWT : Set.range wT = w '' (T : Set (Fin 5)) := by
    ext z
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨eT q, (eT q).property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨eT.symm ⟨i, hi⟩, ?_⟩
      simp only [wT, eT.apply_symm_apply]
  have hRangeV : Set.range v =
      (Set.range vS ∪ {v r}) ∪ (Set.range vT ∪ {v r}) := by
    rw [hRangeVS, hRangeVT]
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      have hi : i ∈ (S ∪ T) ∪ {r} := by rw [hcover]; simp
      simp only [Finset.mem_union, Finset.mem_singleton] at hi
      rcases hi with (hiS | hiT) | rfl
      · exact Or.inl (Or.inl ⟨i, hiS, rfl⟩)
      · exact Or.inr (Or.inl ⟨i, hiT, rfl⟩)
      · exact Or.inl (Or.inr rfl)
    · rintro ((⟨i, -, rfl⟩ | rfl) | ⟨i, -, rfl⟩ | rfl)
      all_goals exact ⟨_, rfl⟩
  have hRangeW : Set.range w =
      (Set.range wS ∪ {w r}) ∪ (Set.range wT ∪ {w r}) := by
    rw [hRangeWS, hRangeWT]
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      have hi : i ∈ (S ∪ T) ∪ {r} := by rw [hcover]; simp
      simp only [Finset.mem_union, Finset.mem_singleton] at hi
      rcases hi with (hiS | hiT) | rfl
      · exact Or.inl (Or.inl ⟨i, hiS, rfl⟩)
      · exact Or.inr (Or.inl ⟨i, hiT, rfl⟩)
      · exact Or.inl (Or.inr rfl)
    · rintro ((⟨i, -, rfl⟩ | rfl) | ⟨i, -, rfl⟩ | rfl)
      all_goals exact ⟨_, rfl⟩
  have hzeroS : ∀ j k,
      (∑ q, vS q j * wS q k) + v r j * w r k = 0 := by
    intro j k
    apply (PairTripleSpan.add_eq_zero_iff_eq_f2 _ _).mpr
    rw [hsumS]
    simpa only [Finset.sum_singleton] using heqSR j k
  have hzeroT : ∀ j k,
      (∑ q, vT q j * wT q k) + v r j * w r k = 0 := by
    intro j k
    apply (PairTripleSpan.add_eq_zero_iff_eq_f2 _ _).mpr
    rw [hsumT]
    simpa only [Finset.sum_singleton] using heqTR j k
  have hlocal := two_two_one_finrank_le_four vS vT wS wT
    (v r) (w r) (hv r) (hw r) hzeroS hzeroT
  rw [← Submodule.span_union, ← Submodule.span_union,
    ← hRangeV, ← hRangeW] at hlocal
  exact hlocal

private theorem selected_mode_finrank_two_complementary_le_four
    {a b c : ℕ}
    (u : Fin 5 → Fin a → ZMod 2)
    (v : Fin 5 → Fin b → ZMod 2)
    (w : Fin 5 → Fin c → ZMod 2)
    (hu : ∀ i, u i ≠ 0) (hv : ∀ i, v i ≠ 0) (hw : ∀ i, w i ≠ 0)
    (hzero : ∀ p j k, ∑ i, u i p * v i j * w i k = 0)
    (hMinimal : ∀ T : Finset (Fin 5),
      (∀ p j k, ∑ i ∈ T, u i p * v i j * w i k = 0) →
        T = ∅ ∨ T = Finset.univ)
    (hdim : Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range u)) = 2) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range v)) +
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range w)) ≤ 4 := by
  classical
  obtain ⟨i₀, i₁, hi₀₁, hLI, hprofile⟩ :=
    f2_finrank_two_range_profile u hu hdim
  let x := u i₀
  let y := u i₁
  have hx : x ≠ 0 := hu i₀
  have hy : y ≠ 0 := hu i₁
  have hxy : x ≠ y := by
    intro h
    have hsum : (1 : ZMod 2) • x + (1 : ZMod 2) • y = 0 := by
      simpa only [one_smul, h] using PairTripleSpan.add_self_eq_zero_f2 y
    exact one_ne_zero (hLI.eq_zero_of_pair hsum).1
  have hxxy : x ≠ x + y := by
    intro h
    have hcancel : x + 0 = x + y := by simpa only [add_zero] using h
    exact hy (add_left_cancel hcancel).symm
  have hyxy : y ≠ x + y := by
    intro h
    have hcancel : y + 0 = y + x := by
      simpa only [add_zero, add_comm] using h
    exact hx (add_left_cancel hcancel).symm
  let A : Finset (Fin 5) := Finset.univ.filter fun i => u i = x
  let B : Finset (Fin 5) := Finset.univ.filter fun i => u i = y
  let C : Finset (Fin 5) := Finset.univ.filter fun i => u i = x + y
  have hmemA {i : Fin 5} : i ∈ A ↔ u i = x := by simp [A]
  have hmemB {i : Fin 5} : i ∈ B ↔ u i = y := by simp [B]
  have hmemC {i : Fin 5} : i ∈ C ↔ u i = x + y := by simp [C]
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro i hiA hiB
    exact hxy ((hmemA.mp hiA).symm.trans (hmemB.mp hiB))
  have hAC : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro i hiA hiC
    exact hxxy ((hmemA.mp hiA).symm.trans (hmemC.mp hiC))
  have hBC : Disjoint B C := by
    rw [Finset.disjoint_left]
    intro i hiB hiC
    exact hyxy ((hmemB.mp hiB).symm.trans (hmemC.mp hiC))
  have hABC : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_left]
    intro i hiAB hiC
    rcases Finset.mem_union.mp hiAB with hiA | hiB
    · exact (Finset.disjoint_left.mp hAC) hiA hiC
    · exact (Finset.disjoint_left.mp hBC) hiB hiC
  have hcover : (A ∪ B) ∪ C = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    rcases hprofile i with hi | hi | hi
    · exact Or.inl (Or.inl (hmemA.mpr hi))
    · exact Or.inl (Or.inr (hmemB.mpr hi))
    · exact Or.inr (hmemC.mpr hi)
  have hAne : A.Nonempty := ⟨i₀, hmemA.mpr rfl⟩
  have hBne : B.Nonempty := ⟨i₁, hmemB.mpr rfl⟩
  have hAproper : A ≠ Finset.univ := by
    intro hA
    have hi₁A : i₁ ∈ A := by rw [hA]; simp
    exact hxy (hmemA.mp hi₁A).symm
  let MA : Fin b → Fin c → ZMod 2 := fun j k => ∑ i ∈ A, v i j * w i k
  let MB : Fin b → Fin c → ZMod 2 := fun j k => ∑ i ∈ B, v i j * w i k
  let MC : Fin b → Fin c → ZMod 2 := fun j k => ∑ i ∈ C, v i j * w i k
  have hgrouped : ∀ p j k,
      x p * MA j k + y p * MB j k + (x p + y p) * MC j k = 0 := by
    intro p j k
    have hsumA : x p * MA j k = ∑ i ∈ A, u i p * v i j * w i k := by
      dsimp only [MA]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hmemA.mp hi]
      ring
    have hsumB : y p * MB j k = ∑ i ∈ B, u i p * v i j * w i k := by
      dsimp only [MB]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hmemB.mp hi]
      ring
    have hsumC : (x p + y p) * MC j k =
        ∑ i ∈ C, u i p * v i j * w i k := by
      dsimp only [MC]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hmemC.mp hi]
      simp only [Pi.add_apply]
      ring
    calc
      x p * MA j k + y p * MB j k + (x p + y p) * MC j k =
          (∑ i ∈ A, u i p * v i j * w i k) +
            (∑ i ∈ B, u i p * v i j * w i k) +
              ∑ i ∈ C, u i p * v i j * w i k := by
        rw [hsumA, hsumB, hsumC]
      _ = ∑ i ∈ (A ∪ B) ∪ C, u i p * v i j * w i k := by
        rw [Finset.sum_union hABC, Finset.sum_union hAB]
      _ = 0 := by
        rw [hcover]
        exact hzero p j k
  obtain ⟨hMAC, hMBC⟩ := three_fiber_sums_eq x y MA MB MC hLI hgrouped
  have hMAne : MA ≠ 0 := by
    apply matrix_sum_ne_zero_of_minimal_constant_fiber u v w A x
      hMinimal hAne hAproper
    intro i hi
    exact hmemA.mp hi
  have hMCne : MC ≠ 0 := by
    intro hMC
    exact hMAne (hMAC.trans hMC)
  have hMBne : MB ≠ 0 := by
    intro hMB
    exact hMCne (hMBC.symm.trans hMB)
  have hCne : C.Nonempty :=
    fiber_nonempty_of_matrix_sum_ne_zero v w C hMCne
  have hBne' : B.Nonempty :=
    fiber_nonempty_of_matrix_sum_ne_zero v w B hMBne
  have hcards : A.card + B.card + C.card = 5 := by
    calc
      A.card + B.card + C.card = (A ∪ B).card + C.card := by
        rw [Finset.card_union_of_disjoint hAB]
      _ = ((A ∪ B) ∪ C).card := by
        rw [Finset.card_union_of_disjoint hABC]
      _ = 5 := by rw [hcover]; simp
  have hshapes := three_positive_sum_five
    (Finset.card_pos.mpr hAne) (Finset.card_pos.mpr hBne')
      (Finset.card_pos.mpr hCne) hcards
  have heqAC : ∀ j k, (∑ i ∈ A, v i j * w i k) =
      ∑ i ∈ C, v i j * w i k := by
    intro j k
    exact congrFun (congrFun hMAC j) k
  have heqBC : ∀ j k, (∑ i ∈ B, v i j * w i k) =
      ∑ i ∈ C, v i j * w i k := by
    intro j k
    exact congrFun (congrFun hMBC j) k
  have heqAB : ∀ j k, (∑ i ∈ A, v i j * w i k) =
      ∑ i ∈ B, v i j * w i k := by
    intro j k
    exact (heqAC j k).trans (heqBC j k).symm
  have hcoverBAC : (B ∪ A) ∪ C = Finset.univ := by
    simpa only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hcover
  have hcoverCAB : (C ∪ A) ∪ B = Finset.univ := by
    simpa only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hcover
  have hcoverACB : (A ∪ C) ∪ B = Finset.univ := by
    simpa only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hcover
  have hcoverBCA : (B ∪ C) ∪ A = Finset.univ := by
    simpa only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hcover
  rcases hshapes with h311 | h131 | h113 | h221 | h212 | h122
  · exact three_one_one_finset_finrank_le_four v w A B C hcover
      h311.1 h311.2.1 h311.2.2 hv hw heqAB heqAC
  · exact three_one_one_finset_finrank_le_four v w B A C hcoverBAC
      h131.2.1 h131.1 h131.2.2 hv hw (fun j k => (heqAB j k).symm) heqBC
  · exact three_one_one_finset_finrank_le_four v w C A B hcoverCAB
      h113.2.2 h113.1 h113.2.1 hv hw
      (fun j k => (heqAC j k).symm) (fun j k => (heqBC j k).symm)
  · exact two_two_one_finset_finrank_le_four v w A B C hcover
      h221.1 h221.2.1 h221.2.2 hv hw heqAC heqBC
  · exact two_two_one_finset_finrank_le_four v w A C B hcoverACB
      h212.1 h212.2.2 h212.2.1 hv hw heqAB (fun j k => (heqBC j k).symm)
  · exact two_two_one_finset_finrank_le_four v w B C A hcoverBCA
      h122.2.1 h122.2.2 h122.1 hv hw (fun j k => (heqAB j k).symm)
      (fun j k => (heqAC j k).symm)

private theorem selected_mode_profile_finrank_le_six
    {a b c : ℕ}
    (u : Fin 5 → Fin a → ZMod 2)
    (v : Fin 5 → Fin b → ZMod 2)
    (w : Fin 5 → Fin c → ZMod 2)
    (hu : ∀ i, u i ≠ 0) (hv : ∀ i, v i ≠ 0) (hw : ∀ i, w i ≠ 0)
    (hzero : ∀ p j k, ∑ i, u i p * v i j * w i k = 0)
    (hMinimal : ∀ T : Finset (Fin 5),
      (∀ p j k, ∑ i ∈ T, u i p * v i j * w i k = 0) →
        T = ∅ ∨ T = Finset.univ)
    (hdim : Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range u)) ≤ 2) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range u)) +
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range v)) +
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range w)) ≤ 6 := by
  classical
  have hspanNe : Submodule.span (ZMod 2) (Set.range u) ≠ ⊥ := by
    intro hbot
    have hu0mem : u 0 ∈ Submodule.span (ZMod 2) (Set.range u) :=
      Submodule.subset_span (Set.mem_range_self 0)
    rw [hbot] at hu0mem
    exact hu 0 (by simpa using hu0mem)
  have hpos : 1 ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range u)) :=
    Submodule.one_le_finrank_iff.mpr hspanNe
  have hrank : Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range u)) = 1 ∨
      Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range u)) = 2 := by
    omega
  rcases hrank with hrankOne | hrankTwo
  · exact selected_mode_finrank_one_profile_le_six u v w hu hzero hrankOne
  · have hcomp := selected_mode_finrank_two_complementary_le_four
      u v w hu hv hw hzero hMinimal hrankTwo
    rw [hrankTwo]
    omega

/-- Five distinct nonzero pure binary coordinate tensors in a two-equals-three
relation have total factor-span rank at most six. -/
theorem pair_triple_profile_finrank_le_six
    {a b c : ℕ}
    (U : Fin 5 → Fin a → ZMod 2)
    (V : Fin 5 → Fin b → ZMod 2)
    (W : Fin 5 → Fin c → ZMod 2)
    (hnz : ∀ i, triad (U i) (V i) (W i) ≠ 0)
    (hinj : Function.Injective fun i => triad (U i) (V i) (W i))
    (hsum : triad (U 0) (V 0) (W 0) + triad (U 1) (V 1) (W 1) =
      triad (U 2) (V 2) (W 2) + triad (U 3) (V 3) (W 3) +
        triad (U 4) (V 4) (W 4)) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range U)) +
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range V)) +
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range W)) ≤ 6 := by
  classical
  let value : Fin 5 → Tensor (ZMod 2) a b c :=
    fun i => triad (U i) (V i) (W i)
  have htotal : ∑ i, value i = 0 := by
    calc
      (∑ i, value i) = (value 0 + value 1) + (value 2 + value 3 + value 4) := by
        simp only [Fin.sum_univ_succ]
        abel
      _ = (value 2 + value 3 + value 4) + (value 2 + value 3 + value 4) := by
        rw [show value 0 + value 1 = value 2 + value 3 + value 4 by
          simpa only [value] using hsum]
      _ = 0 := PairTripleSpan.add_self_eq_zero_f2 _
  have hzero : ∀ p j k, ∑ i, U i p * V i j * W i k = 0 := by
    intro p j k
    have hentry := congrFun (congrFun (congrFun htotal p) j) k
    simpa only [Finset.sum_apply, value, triad, Pi.zero_apply] using hentry
  have hCycle : BinaryCircuit.BinaryCycle value Finset.univ := by
    simpa [BinaryCircuit.BinaryCycle, BinaryCircuit.evaluation] using htotal
  have hCircuit : BinaryCircuit.Circuit value Finset.univ :=
    BinaryCircuit.circuit_of_binaryCycle_card_five
      hCycle (by simp) (fun i _ => hnz i)
        (fun _ _ _ _ heq => hinj (by simpa only [value] using heq))
  have hMinimal : ∀ T : Finset (Fin 5),
      (∀ p j k, ∑ i ∈ T, U i p * V i j * W i k = 0) →
        T = ∅ ∨ T = Finset.univ := by
    intro T hTzero
    by_cases hTempty : T = ∅
    · exact Or.inl hTempty
    · right
      by_contra hTuniv
      have hTproper : T ⊂ (Finset.univ : Finset (Fin 5)) :=
        Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ T, hTuniv⟩
      have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hTempty
      have hTCycle : BinaryCircuit.BinaryCycle value T := by
        rw [BinaryCircuit.BinaryCycle, BinaryCircuit.evaluation]
        ext p j k
        simpa only [Finset.sum_apply, value, triad, Pi.zero_apply] using hTzero p j k
      exact hCircuit.2.2 T hTproper hTne hTCycle
  have hfac : ∀ i, U i ≠ 0 ∧ V i ≠ 0 ∧ W i ≠ 0 :=
    fun i => PairTripleSpan.factors_ne_zero_of_triad_ne_zero (hnz i)
  rcases PairTripleSpan.pair_triple_span_drop U V W hnz hinj hsum with
    hU | hV | hW
  · have hUdim := finrank_span_range_le_two_of_tail_mem_pair_span U hU
    exact selected_mode_profile_finrank_le_six U V W
      (fun i => (hfac i).1) (fun i => (hfac i).2.1) (fun i => (hfac i).2.2)
      hzero hMinimal hUdim
  · have hVdim := finrank_span_range_le_two_of_tail_mem_pair_span V hV
    have hzeroV : ∀ j p k, ∑ i, V i j * U i p * W i k = 0 := by
      intro j p k
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hzero p j k
    have hMinimalV : ∀ T : Finset (Fin 5),
        (∀ j p k, ∑ i ∈ T, V i j * U i p * W i k = 0) →
          T = ∅ ∨ T = Finset.univ := by
      intro T hT
      apply hMinimal T
      intro p j k
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hT j p k
    have hbound := selected_mode_profile_finrank_le_six V U W
      (fun i => (hfac i).2.1) (fun i => (hfac i).1) (fun i => (hfac i).2.2)
      hzeroV hMinimalV hVdim
    omega
  · have hWdim := finrank_span_range_le_two_of_tail_mem_pair_span W hW
    have hzeroW : ∀ k p j, ∑ i, W i k * U i p * V i j = 0 := by
      intro k p j
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hzero p j k
    have hMinimalW : ∀ T : Finset (Fin 5),
        (∀ k p j, ∑ i ∈ T, W i k * U i p * V i j = 0) →
          T = ∅ ∨ T = Finset.univ := by
      intro T hT
      apply hMinimal T
      intro p j k
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hT k p j
    have hbound := selected_mode_profile_finrank_le_six W U V
      (fun i => (hfac i).2.2) (fun i => (hfac i).1) (fun i => (hfac i).2.1)
      hzeroW hMinimalW hWdim
    omega

private theorem finrank_span_range_pos_of_value_ne_zero
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : ι → V) (i : ι) (hi : f i ≠ 0) :
    0 < Module.finrank K (Submodule.span K (Set.range f)) := by
  have hspan : Submodule.span K (Set.range f) ≠ ⊥ := by
    intro hbot
    have hmem : f i ∈ Submodule.span K (Set.range f) :=
      Submodule.subset_span (Set.mem_range_self i)
    rw [hbot] at hmem
    exact hi (by simpa using hmem)
  exact Submodule.one_le_finrank_iff.mpr hspan

/-- One nonzero pure tensor forces all three factor-family spans to have positive
rank. -/
theorem pair_triple_factor_span_finrank_pos
    {a b c : ℕ}
    (U : Fin 5 → Fin a → ZMod 2)
    (V : Fin 5 → Fin b → ZMod 2)
    (W : Fin 5 → Fin c → ZMod 2)
    (hnz : ∃ i, triad (U i) (V i) (W i) ≠ 0) :
    0 < Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range U)) ∧
      0 < Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range V)) ∧
      0 < Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range W)) := by
  obtain ⟨i, hi⟩ := hnz
  have hfac := PairTripleSpan.factors_ne_zero_of_triad_ne_zero hi
  exact ⟨finrank_span_range_pos_of_value_ne_zero U i hfac.1,
    finrank_span_range_pos_of_value_ne_zero V i hfac.2.1,
    finrank_span_range_pos_of_value_ne_zero W i hfac.2.2⟩

/-- For a five-term binary pure-tensor circuit, subtracting one from each
positive factor-span rank gives total excess at most three. -/
theorem pair_triple_profile_sub_one_sum_le_three
    {a b c : ℕ}
    (U : Fin 5 → Fin a → ZMod 2)
    (V : Fin 5 → Fin b → ZMod 2)
    (W : Fin 5 → Fin c → ZMod 2)
    (hnz : ∀ i, triad (U i) (V i) (W i) ≠ 0)
    (hinj : Function.Injective fun i => triad (U i) (V i) (W i))
    (hsum : triad (U 0) (V 0) (W 0) + triad (U 1) (V 1) (W 1) =
      triad (U 2) (V 2) (W 2) + triad (U 3) (V 3) (W 3) +
        triad (U 4) (V 4) (W 4)) :
    (Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range U)) - 1) +
        (Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range V)) - 1) +
        (Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range W)) - 1) ≤ 3 := by
  have hpos := pair_triple_factor_span_finrank_pos U V W ⟨0, hnz 0⟩
  have hbound := pair_triple_profile_finrank_le_six U V W hnz hinj hsum
  omega

private theorem fin_four_linear_independent_of_fin_five_circuit
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (value : Fin 5 → V)
    (hCircuit : BinaryCircuit.Circuit value Finset.univ) :
    LinearIndependent (ZMod 2) (fun i : Fin 4 => value i.castSucc) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hsum q
  by_contra hgq
  let support : Finset (Fin 4) := Finset.univ.filter fun i => g i ≠ 0
  let T : Finset (Fin 5) := support.map Fin.castSuccEmb
  have hqSupport : q ∈ support := by simp [support, hgq]
  have hTNonempty : T.Nonempty := by
    exact ⟨q.castSucc, Finset.mem_map.mpr ⟨q, hqSupport, rfl⟩⟩
  have hTProper : T ⊂ (Finset.univ : Finset (Fin 5)) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ T, ?_⟩
    intro hTuniv
    have hTCard : T.card = 5 := by rw [hTuniv]; simp
    have hTCardLe : T.card ≤ 4 := by
      calc
        T.card = support.card := Finset.card_map Fin.castSuccEmb
        _ ≤ Fintype.card (Fin 4) := Finset.card_le_univ support
        _ = 4 := Fintype.card_fin 4
    omega
  have hsumSupport : ∑ i ∈ support, value i.castSucc = 0 := by
    calc
      (∑ i ∈ support, value i.castSucc) =
          ∑ i ∈ support, g i • value i.castSucc := by
        apply Finset.sum_congr rfl
        intro i hi
        have hgi : g i ≠ 0 := by simpa [support] using hi
        rw [PairTripleSpan.eq_one_of_ne_zero hgi, one_smul]
      _ = ∑ i, g i • value i.castSucc := by
        exact Finset.sum_subset (s₁ := support) (s₂ := Finset.univ)
          (Finset.filter_subset _ _) (by
            intro i _ hi
            simp only [support, Finset.mem_filter, Finset.mem_univ, true_and,
              not_not] at hi
            rw [hi, zero_smul])
      _ = 0 := hsum
  have hTCycle : BinaryCircuit.BinaryCycle value T := by
    rw [BinaryCircuit.BinaryCycle, BinaryCircuit.evaluation]
    rw [Finset.sum_map]
    exact hsumSupport
  exact hCircuit.2.2 T hTProper hTNonempty hTCycle

private theorem finrank_span_range_ge_four_of_fin_five_circuit
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (value : Fin 5 → V)
    (hCircuit : BinaryCircuit.Circuit value Finset.univ) :
    4 ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range value)) := by
  let firstFour : Fin 4 → V := fun i => value i.castSucc
  have hLI : LinearIndependent (ZMod 2) firstFour :=
    fin_four_linear_independent_of_fin_five_circuit value hCircuit
  calc
    4 = Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range firstFour)) := by
      rw [finrank_span_eq_card hLI, Fintype.card_fin]
    _ ≤ Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range value)) := by
      apply Submodule.finrank_mono
      apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨i.castSucc, rfl⟩

private theorem family_constant_of_finrank_span_range_eq_one
    {a : ℕ} (u : Fin 5 → Fin a → ZMod 2)
    (hu : ∀ i, u i ≠ 0)
    (hdim : Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range u)) = 1) :
    ∀ i, u i = u 0 := by
  let P := Submodule.span (ZMod 2) (Set.range u)
  have hu0P : u 0 ∈ P := Submodule.subset_span (Set.mem_range_self 0)
  have hP : P = Submodule.span (ZMod 2) ({u 0} : Set (Fin a → ZMod 2)) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdim hu0P (hu 0)
  intro i
  have huiP : u i ∈ P := Submodule.subset_span (Set.mem_range_self i)
  rw [hP, Submodule.mem_span_singleton] at huiP
  obtain ⟨r, hr⟩ := huiP
  rcases PairTripleSpan.scalar_eq_zero_or_one r with rfl | rfl
  · simp only [zero_smul] at hr
    exact (hu i hr.symm).elim
  · simpa only [one_smul] using hr.symm

private theorem first_rank_ge_four_of_second_third_rank_one
    {a b c : ℕ}
    (U : Fin 5 → Fin a → ZMod 2)
    (V : Fin 5 → Fin b → ZMod 2)
    (W : Fin 5 → Fin c → ZMod 2)
    (hnz : ∀ i, triad (U i) (V i) (W i) ≠ 0)
    (hinj : Function.Injective fun i => triad (U i) (V i) (W i))
    (hsum : triad (U 0) (V 0) (W 0) + triad (U 1) (V 1) (W 1) =
      triad (U 2) (V 2) (W 2) + triad (U 3) (V 3) (W 3) +
        triad (U 4) (V 4) (W 4))
    (hVdim : Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range V)) = 1)
    (hWdim : Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range W)) = 1) :
    4 ≤ Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range U)) := by
  classical
  have hfac : ∀ i, U i ≠ 0 ∧ V i ≠ 0 ∧ W i ≠ 0 :=
    fun i => PairTripleSpan.factors_ne_zero_of_triad_ne_zero (hnz i)
  have hVconst := family_constant_of_finrank_span_range_eq_one V
    (fun i => (hfac i).2.1) hVdim
  have hWconst := family_constant_of_finrank_span_range_eq_one W
    (fun i => (hfac i).2.2) hWdim
  obtain ⟨j, hj⟩ := PairTripleSpan.exists_apply_ne_zero ((hfac 0).2.1)
  obtain ⟨k, hk⟩ := PairTripleSpan.exists_apply_ne_zero ((hfac 0).2.2)
  have hjOne : V 0 j = 1 := PairTripleSpan.eq_one_of_ne_zero hj
  have hkOne : W 0 k = 1 := PairTripleSpan.eq_one_of_ne_zero hk
  have hUrel : U 0 + U 1 = U 2 + U 3 + U 4 := by
    funext p
    have hentry := congrFun (congrFun (congrFun hsum p) j) k
    simpa only [triad, Pi.add_apply, hVconst, hWconst, hjOne, hkOne,
      mul_one] using hentry
  have hUtotal : ∑ i, U i = 0 := by
    calc
      (∑ i, U i) = (U 0 + U 1) + (U 2 + U 3 + U 4) := by
        simp only [Fin.sum_univ_succ]
        abel
      _ = (U 2 + U 3 + U 4) + (U 2 + U 3 + U 4) := by rw [hUrel]
      _ = 0 := PairTripleSpan.add_self_eq_zero_f2 _
  have hUinj : Function.Injective U := by
    intro i i' hii'
    apply hinj
    simp only [hii', hVconst i, hVconst i', hWconst i, hWconst i']
  have hCycle : BinaryCircuit.BinaryCycle U Finset.univ := by
    simpa [BinaryCircuit.BinaryCycle, BinaryCircuit.evaluation] using hUtotal
  have hCircuit : BinaryCircuit.Circuit U Finset.univ :=
    BinaryCircuit.circuit_of_binaryCycle_card_five hCycle (by simp)
      (fun i _ => (hfac i).1)
      (fun _ _ _ _ heq => hUinj heq)
  exact finrank_span_range_ge_four_of_fin_five_circuit U hCircuit

private theorem positive_sum_le_six_profiles
    {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hsum : p + q + r ≤ 6)
    (hpFour : q = 1 → r = 1 → 4 ≤ p)
    (hqFour : p = 1 → r = 1 → 4 ≤ q)
    (hrFour : p = 1 → q = 1 → 4 ≤ r) :
    [p, q, r].Perm [2, 2, 1] ∨ [p, q, r].Perm [3, 2, 1] ∨
      [p, q, r].Perm [2, 2, 2] ∨ [p, q, r].Perm [4, 1, 1] := by
  have hpLe : p ≤ 4 := by omega
  have hqLe : q ≤ 4 := by omega
  have hrLe : r ≤ 4 := by omega
  interval_cases p <;> interval_cases q <;> interval_cases r
  all_goals norm_num at *
  all_goals decide

/-- The unordered factor-span rank profile of a five-term binary pure-tensor
circuit is `221`, `321`, `222`, or `411`.  `List.Perm` makes the statement
independent of the order of the three tensor modes. -/
theorem pair_triple_profile_classification
    {a b c : ℕ}
    (U : Fin 5 → Fin a → ZMod 2)
    (V : Fin 5 → Fin b → ZMod 2)
    (W : Fin 5 → Fin c → ZMod 2)
    (hnz : ∀ i, triad (U i) (V i) (W i) ≠ 0)
    (hinj : Function.Injective fun i => triad (U i) (V i) (W i))
    (hsum : triad (U 0) (V 0) (W 0) + triad (U 1) (V 1) (W 1) =
      triad (U 2) (V 2) (W 2) + triad (U 3) (V 3) (W 3) +
        triad (U 4) (V 4) (W 4)) :
    let rU := Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range U))
    let rV := Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range V))
    let rW := Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range W))
    [rU, rV, rW].Perm [2, 2, 1] ∨ [rU, rV, rW].Perm [3, 2, 1] ∨
      [rU, rV, rW].Perm [2, 2, 2] ∨ [rU, rV, rW].Perm [4, 1, 1] := by
  dsimp only
  have hpos := pair_triple_factor_span_finrank_pos U V W ⟨0, hnz 0⟩
  have hbound := pair_triple_profile_finrank_le_six U V W hnz hinj hsum
  have hUFour
      (hVOne : Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range V)) = 1)
      (hWOne : Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range W)) = 1) :
      4 ≤ Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range U)) :=
    first_rank_ge_four_of_second_third_rank_one U V W hnz hinj hsum hVOne hWOne
  have hnzVU : ∀ i, triad (V i) (U i) (W i) ≠ 0 := by
    intro i hzero
    apply hnz i
    ext p j k
    have hentry := congrFun (congrFun (congrFun hzero j) p) k
    simpa [triad, mul_assoc, mul_left_comm, mul_comm] using hentry
  have hinjVU : Function.Injective fun i => triad (V i) (U i) (W i) := by
    intro i i' heq
    apply hinj
    ext p j k
    have hentry := congrFun (congrFun (congrFun heq j) p) k
    simpa [triad, mul_assoc, mul_left_comm, mul_comm] using hentry
  have hsumVU : triad (V 0) (U 0) (W 0) + triad (V 1) (U 1) (W 1) =
      triad (V 2) (U 2) (W 2) + triad (V 3) (U 3) (W 3) +
        triad (V 4) (U 4) (W 4) := by
    ext j p k
    have hentry := congrFun (congrFun (congrFun hsum p) j) k
    simpa [triad, mul_assoc, mul_left_comm, mul_comm] using hentry
  have hVFour
      (hUOne : Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range U)) = 1)
      (hWOne : Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range W)) = 1) :
      4 ≤ Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range V)) :=
    first_rank_ge_four_of_second_third_rank_one V U W hnzVU hinjVU hsumVU
      hUOne hWOne
  have hnzWUV : ∀ i, triad (W i) (U i) (V i) ≠ 0 := by
    intro i hzero
    apply hnz i
    ext p j k
    have hentry := congrFun (congrFun (congrFun hzero k) p) j
    simpa [triad, mul_assoc, mul_left_comm, mul_comm] using hentry
  have hinjWUV : Function.Injective fun i => triad (W i) (U i) (V i) := by
    intro i i' heq
    apply hinj
    ext p j k
    have hentry := congrFun (congrFun (congrFun heq k) p) j
    simpa [triad, mul_assoc, mul_left_comm, mul_comm] using hentry
  have hsumWUV : triad (W 0) (U 0) (V 0) + triad (W 1) (U 1) (V 1) =
      triad (W 2) (U 2) (V 2) + triad (W 3) (U 3) (V 3) +
        triad (W 4) (U 4) (V 4) := by
    ext k p j
    have hentry := congrFun (congrFun (congrFun hsum p) j) k
    simpa [triad, mul_assoc, mul_left_comm, mul_comm] using hentry
  have hWFour
      (hUOne : Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range U)) = 1)
      (hVOne : Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range V)) = 1) :
      4 ≤ Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range W)) :=
    first_rank_ge_four_of_second_third_rank_one W U V hnzWUV hinjWUV hsumWUV
      hUOne hVOne
  exact positive_sum_le_six_profiles hpos.1 hpos.2.1 hpos.2.2 hbound
    hUFour hVFour hWFour

/-- If every coordinate factor space has dimension at most three, the `411`
case is impossible, so the unordered profile is `221`, `321`, or `222`. -/
theorem pair_triple_profile_classification_of_ambient_le_three
    {a b c : ℕ}
    (U : Fin 5 → Fin a → ZMod 2)
    (V : Fin 5 → Fin b → ZMod 2)
    (W : Fin 5 → Fin c → ZMod 2)
    (hnz : ∀ i, triad (U i) (V i) (W i) ≠ 0)
    (hinj : Function.Injective fun i => triad (U i) (V i) (W i))
    (hsum : triad (U 0) (V 0) (W 0) + triad (U 1) (V 1) (W 1) =
      triad (U 2) (V 2) (W 2) + triad (U 3) (V 3) (W 3) +
        triad (U 4) (V 4) (W 4))
    (ha : a ≤ 3) (hb : b ≤ 3) (hc : c ≤ 3) :
    let rU := Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range U))
    let rV := Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range V))
    let rW := Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range W))
    [rU, rV, rW].Perm [2, 2, 1] ∨ [rU, rV, rW].Perm [3, 2, 1] ∨
      [rU, rV, rW].Perm [2, 2, 2] := by
  dsimp only
  have hprofiles := pair_triple_profile_classification U V W hnz hinj hsum
  dsimp only at hprofiles
  rcases hprofiles with h221 | h321 | h222 | h411
  · exact Or.inl h221
  · exact Or.inr (Or.inl h321)
  · exact Or.inr (Or.inr h222)
  · have hUleA : Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range U)) ≤ a := by
      simpa only [Module.finrank_fin_fun] using
        Submodule.finrank_le (Submodule.span (ZMod 2) (Set.range U))
    have hVleB : Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range V)) ≤ b := by
      simpa only [Module.finrank_fin_fun] using
        Submodule.finrank_le (Submodule.span (ZMod 2) (Set.range V))
    have hWleC : Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range W)) ≤ c := by
      simpa only [Module.finrank_fin_fun] using
        Submodule.finrank_le (Submodule.span (ZMod 2) (Set.range W))
    have hmem : 4 ∈ [
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range U)),
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range V)),
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range W))] :=
      h411.mem_iff.mpr (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    omega

end BilinearComplexity
