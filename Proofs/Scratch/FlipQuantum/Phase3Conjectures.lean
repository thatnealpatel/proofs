/-
  Scratch/FlipQuantum/Phase3Conjectures — an honest proposition interface for
  flip-graph connectivity and rank-search questions.

  The definitions in this file name conjectural properties; they do not assert
  them.  Each graph-level property explicitly requires a positive, inhabited
  level, and each predecessor-rank statement guards natural-number subtraction.
-/
import Scratch.FlipQuantum.Phase2Algebra

set_option autoImplicit false

namespace BilinearComplexity.FlipQuantum

namespace Scheme

variable {k : Type*} [Field k] {a b c : ℕ}

/-- `ConnectivityConjecture T r` says that the positive, inhabited level `r`
of the exact flip graph for `T` is connected: any two `GraphVertex` schemes are
joined by `Reachable`, whose chains consist of `Flip` edges.  This is a named
proposition, not a claim that every level is connected. -/
def ConnectivityConjecture (T : BilinearComplexity.Tensor k a b c)
    (r : ℕ) : Prop :=
  0 < r ∧
    (∃ S : Scheme k a b c r, S.GraphVertex T) ∧
    ∀ S R : Scheme k a b c r,
      S.GraphVertex T → R.GraphVertex T → S.Reachable T R

/-- `DensityConjecture T r` says that every flip-connected component of the
positive, inhabited level `r` contains a `Reducible` graph vertex.  Thus a
same-level search from any exact `GraphVertex` can reach a certified reduction
opportunity.  No probability distribution or finite-search bound is asserted. -/
def DensityConjecture (T : BilinearComplexity.Tensor k a b c)
    (r : ℕ) : Prop :=
  0 < r ∧
    (∃ S : Scheme k a b c r, S.GraphVertex T) ∧
    ∀ S : Scheme k a b c r, S.GraphVertex T →
      ∃ R : Scheme k a b c r, S.Reachable T R ∧ R.Reducible T

/-- `MatrixRankConjecture k a b c r` records the concrete conjecture that the
nonempty matrix-multiplication tensor `⟨a,b,c⟩` has rank exactly `r`, expressed
only through the established `RankLE` API.  Positivity of all dimensions avoids
empty tensor modes, and `0 < r` makes the predecessor `r - 1` nondegenerate. -/
def MatrixRankConjecture (k : Type*) [CommSemiring k] (a b c r : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < r ∧
    BilinearComplexity.RankLE (BilinearComplexity.matMulTensor k a b c) r ∧
    ¬BilinearComplexity.RankLE
      (BilinearComplexity.matMulTensor k a b c) (r - 1)

/-- `RankSearchConjecture T r` is the completeness conjecture for flip search
at a positive, inhabited level: `T` has an `(r - 1)`-term decomposition exactly
when every level-`r` flip component contains a reachable `Reducible` vertex.
The forward implication is the conjectural search assertion; the reverse
implication is compatible with `Reducible.rankLE_pred`. -/
def RankSearchConjecture (T : BilinearComplexity.Tensor k a b c)
    (r : ℕ) : Prop :=
  0 < r ∧
    (∃ S : Scheme k a b c r, S.GraphVertex T) ∧
    (BilinearComplexity.RankLE T (r - 1) ↔ DensityConjecture T r)

end Scheme

/-! Ground checks: the interfaces have concrete models, including a jointly
satisfiable rank-search instance at a nonminimal level. -/

example :
    Scheme.ConnectivityConjecture
      (BilinearComplexity.matMulTensor (ZMod 2) 1 1 1) 1 := by
  let S₀ : Scheme (ZMod 2) 1 1 1 1 :=
    ⟨fun _ => (fun _ => 1, fun _ => 1, fun _ => 1)⟩
  have hS₀ : S₀.GraphVertex
      (BilinearComplexity.matMulTensor (ZMod 2) 1 1 1) := by
    refine ⟨by omega, ?_, ?_, ?_⟩
    · funext i j l
      rw [BilinearComplexity.matMulTensor_apply,
        if_pos ⟨Subsingleton.elim _ _, Subsingleton.elim _ _,
          Subsingleton.elim _ _⟩]
      simp [Scheme.sumTensor, S₀, BilinearComplexity.TriadData.eval,
        BilinearComplexity.triad]
    · intro s hzero
      have hone := congrFun (congrFun (congrFun hzero 0) 0) 0
      norm_num [S₀, BilinearComplexity.TriadData.eval,
        BilinearComplexity.triad] at hone
    · intro x y _hxy
      exact Subsingleton.elim x y
  refine ⟨by omega, ⟨S₀, hS₀⟩, ?_⟩
  intro S R hS hR
  have heqOne (x : ZMod 2) (hx : x ≠ 0) : x = 1 := by
    have hval : x.val ≠ 0 := by simpa using hx
    have hxval : x.val = 1 := by
      have hlt := ZMod.val_lt x
      omega
    exact (ZMod.val_eq_one (by omega) x).mp hxval
  have hunit : ∀ (Q : Scheme (ZMod 2) 1 1 1 1),
      Q.GraphVertex (BilinearComplexity.matMulTensor (ZMod 2) 1 1 1) →
      Q.term 0 = (fun _ => 1, fun _ => 1, fun _ => 1) := by
    intro Q hQ
    have hx : (Q.term 0).1 0 ≠ 0 := by
      intro hxzero
      apply hQ.2.2.1 0
      funext i j l
      fin_cases i
      fin_cases j
      fin_cases l
      simp [BilinearComplexity.TriadData.eval, BilinearComplexity.triad, hxzero]
    have hy : (Q.term 0).2.1 0 ≠ 0 := by
      intro hyzero
      apply hQ.2.2.1 0
      funext i j l
      fin_cases i
      fin_cases j
      fin_cases l
      simp [BilinearComplexity.TriadData.eval, BilinearComplexity.triad, hyzero]
    have hz : (Q.term 0).2.2 0 ≠ 0 := by
      intro hzzero
      apply hQ.2.2.1 0
      funext i j l
      fin_cases i
      fin_cases j
      fin_cases l
      simp [BilinearComplexity.TriadData.eval, BilinearComplexity.triad, hzzero]
    apply Prod.ext
    · funext i
      fin_cases i
      exact heqOne _ hx
    · apply Prod.ext
      · funext j
        fin_cases j
        exact heqOne _ hy
      · funext l
        fin_cases l
        exact heqOne _ hz
  have hSR : S = R := by
    have hterms : S.term = R.term := by
      funext s
      fin_cases s
      exact (hunit S hS).trans (hunit R hR).symm
    cases S with
    | mk termS =>
        cases R with
        | mk termR =>
            cases hterms
            rfl
  subst R
  exact Scheme.reachable_refl hS

example :
    Scheme.MatrixRankConjecture ℚ 1 1 1 1 := by
  refine ⟨by omega, by omega, by omega, by omega,
    BilinearComplexity.rankLE_matMulTensor_one ℚ, ?_⟩
  intro hzero
  have hle := BilinearComplexity.rank_le_of_rankLE hzero
  rw [BilinearComplexity.rank_matMulTensor_one ℚ] at hle
  omega

example :
    Scheme.DensityConjecture
        (BilinearComplexity.matMulTensor ℚ 1 1 1) 2 ∧
      Scheme.RankSearchConjecture
        (BilinearComplexity.matMulTensor ℚ 1 1 1) 2 := by
  let S₀ : Scheme ℚ 1 1 1 2 :=
    ⟨fun s => (fun _ => 1, fun _ => 1,
      fun _ => if s = 0 then 2 else -1)⟩
  have hS₀ : S₀.GraphVertex
      (BilinearComplexity.matMulTensor ℚ 1 1 1) := by
    refine ⟨by omega, ?_, ?_, ?_⟩
    · funext i j l
      rw [BilinearComplexity.matMulTensor_apply,
        if_pos ⟨Subsingleton.elim _ _, Subsingleton.elim _ _,
          Subsingleton.elim _ _⟩]
      norm_num [Scheme.sumTensor, S₀, Fin.sum_univ_two,
        BilinearComplexity.TriadData.eval, BilinearComplexity.triad]
    · intro s hzero
      fin_cases s
      · have htwo := congrFun (congrFun (congrFun hzero 0) 0) 0
        norm_num [S₀, BilinearComplexity.TriadData.eval,
          BilinearComplexity.triad] at htwo
      · have hneg := congrFun (congrFun (congrFun hzero 0) 0) 0
        norm_num [S₀, BilinearComplexity.TriadData.eval,
          BilinearComplexity.triad] at hneg
    · intro x y hxy
      fin_cases x <;> fin_cases y
      · rfl
      · have hentry := congrFun (congrFun (congrFun hxy 0) 0) 0
        norm_num [S₀, BilinearComplexity.TriadData.eval,
          BilinearComplexity.triad] at hentry
      · have hentry := congrFun (congrFun (congrFun hxy 0) 0) 0
        norm_num [S₀, BilinearComplexity.TriadData.eval,
          BilinearComplexity.triad] at hentry
      · rfl
  have hdensity : Scheme.DensityConjecture
      (BilinearComplexity.matMulTensor ℚ 1 1 1) 2 := by
    refine ⟨by omega, ⟨S₀, hS₀⟩, ?_⟩
    intro S hS
    refine ⟨S, Scheme.reachable_refl hS, ?_⟩
    have hfirst : ∀ s : Fin 2, (S.term s).1 0 ≠ 0 := by
      intro s hs
      apply hS.2.2.1 s
      funext i j l
      fin_cases i
      fin_cases j
      fin_cases l
      simp [BilinearComplexity.TriadData.eval, BilinearComplexity.triad, hs]
    refine ⟨hS, Or.inl ?_⟩
    let I : Finset (Fin 2) := Finset.univ
    refine ⟨I, Finset.univ_nonempty, ?_, ?_⟩
    · refine ⟨0, Finset.mem_univ _, ?_⟩
      intro i _hi
      let q : ℚ := (S.term i).1 0 / (S.term 0).1 0
      refine ⟨q, div_ne_zero (hfirst i) (hfirst 0), ?_⟩
      funext x
      rw [show x = 0 by omega]
      simpa only [q, Pi.smul_apply, smul_eq_mul] using
        (div_mul_cancel₀ ((S.term i).1 0) (hfirst 0)).symm
    · intro hli
      have hcard : Fintype.card {i : Fin 2 // i ∈ I} ≤
          Module.finrank ℚ (Fin 1 → ℚ) :=
        hli.fintype_card_le_finrank
      norm_num [I, Module.finrank_pi] at hcard
  refine ⟨hdensity, by
    refine ⟨by omega, ⟨S₀, hS₀⟩, ?_⟩
    constructor
    · intro _hpred
      exact hdensity
    · intro _hdense
      simpa using BilinearComplexity.rankLE_matMulTensor_one ℚ⟩

#check @Scheme.ConnectivityConjecture
#check @Scheme.DensityConjecture
#check @Scheme.MatrixRankConjecture
#check @Scheme.RankSearchConjecture

#print axioms Scheme.ConnectivityConjecture
#print axioms Scheme.DensityConjecture
#print axioms Scheme.MatrixRankConjecture
#print axioms Scheme.RankSearchConjecture

end BilinearComplexity.FlipQuantum
