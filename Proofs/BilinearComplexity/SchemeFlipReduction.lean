import BilinearComplexity.SchemeReplacement
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace BilinearComplexity
namespace Scheme
namespace FlipReduction

open Replacement

variable {k : Type*} {a b c r : ℕ}

/-- The two-term scheme whose operational slots are the two displayed triads. -/
def pairScheme (t₀ t₁ : TriadData k a b c) : Scheme k a b c 2 :=
  ⟨fun s => if s = 0 then t₀ else t₁⟩

/-- Selecting both slots of a pair scheme gives the sum of its two evaluated triads. -/
theorem selectedTensor_pairScheme_univ [CommSemiring k]
    (t₀ t₁ : TriadData k a b c) :
    Replacement.selectedTensor (pairScheme t₀ t₁) Finset.univ =
      t₀.eval + t₁.eval := by
  funext i j l
  simp [Replacement.selectedTensor, pairScheme, TriadData.eval, triad,
    Fin.sum_univ_two]

/-- The inserted tensor of a two-element list is the sum of its two evaluations. -/
theorem insertedTensor_pair [CommSemiring k] (t₀ t₁ : TriadData k a b c) :
    Replacement.insertedTensor [t₀, t₁] = t₀.eval + t₁.eval := by
  funext i j l
  simp [Replacement.insertedTensor, TriadData.eval, triad]

/-- Selecting two distinct ambient slots gives their evaluations in the stated slot order. -/
theorem selectedTensor_pairSlots [CommSemiring k] (S : Scheme k a b c r)
    (s₀ s₁ : Fin r) (hslots : s₀ ≠ s₁) :
    Replacement.selectedTensor S {s₀, s₁} =
      (S.term s₀).eval + (S.term s₁).eval := by
  simp [Replacement.selectedTensor, hslots]

/-- The represented tensor of a two-slot scheme is its slot-zero evaluation followed by
its slot-one evaluation. -/
theorem sumTensor_two [CommSemiring k] (S : Scheme k a b c 2) :
    S.sumTensor = (S.term 0).eval + (S.term 1).eval := by
  funext i j l
  simp [Scheme.sumTensor, TriadData.eval, triad, Fin.sum_univ_two]

/-- The first-position ordinary shear of a pair sharing its first factor. -/
def flipFirstPair [Ring k] (u : Fin a → k) (v₀ v₁ : Fin b → k)
    (w₀ w₁ : Fin c → k) (q : k) : List (TriadData k a b c) :=
  [(u, v₀ + q • v₁, w₀), (u, v₁, w₁ - q • w₀)]

/-- The second-position ordinary shear of a pair sharing its second factor. -/
def flipSecondPair [Ring k] (u₀ u₁ : Fin a → k) (v : Fin b → k)
    (w₀ w₁ : Fin c → k) (q : k) : List (TriadData k a b c) :=
  [(u₀ + q • u₁, v, w₀), (u₁, v, w₁ - q • w₀)]

/-- The third-position ordinary shear of a pair sharing its third factor. -/
def flipThirdPair [Ring k] (u₀ u₁ : Fin a → k) (v₀ v₁ : Fin b → k)
    (w : Fin c → k) (q : k) : List (TriadData k a b c) :=
  [(u₀ + q • u₁, v₀, w), (u₁, v₁ - q • v₀, w)]

/-- The first ordinary flip is an exact two-slot local replacement certificate. -/
def firstFlipCertificate [CommRing k] (u : Fin a → k) (v₀ v₁ : Fin b → k)
    (w₀ w₁ : Fin c → k) (q : k) :
    Replacement.Certificate (pairScheme (u, v₀, w₀) (u, v₁, w₁)) where
  removed := Finset.univ
  inserted := flipFirstPair u v₀ v₁ w₀ w₁ q
  local_eq := by
    rw [selectedTensor_pairScheme_univ, flipFirstPair, insertedTensor_pair]
    funext i j l
    simp only [TriadData.eval, triad, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    ring

/-- The second ordinary flip is an exact two-slot local replacement certificate. -/
def secondFlipCertificate [CommRing k] (u₀ u₁ : Fin a → k) (v : Fin b → k)
    (w₀ w₁ : Fin c → k) (q : k) :
    Replacement.Certificate (pairScheme (u₀, v, w₀) (u₁, v, w₁)) where
  removed := Finset.univ
  inserted := flipSecondPair u₀ u₁ v w₀ w₁ q
  local_eq := by
    rw [selectedTensor_pairScheme_univ, flipSecondPair, insertedTensor_pair]
    funext i j l
    simp only [TriadData.eval, triad, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    ring

/-- The third ordinary flip is an exact two-slot local replacement certificate. -/
def thirdFlipCertificate [CommRing k] (u₀ u₁ : Fin a → k) (v₀ v₁ : Fin b → k)
    (w : Fin c → k) (q : k) :
    Replacement.Certificate (pairScheme (u₀, v₀, w) (u₁, v₁, w)) where
  removed := Finset.univ
  inserted := flipThirdPair u₀ u₁ v₀ v₁ w q
  local_eq := by
    rw [selectedTensor_pairScheme_univ, flipThirdPair, insertedTensor_pair]
    funext i j l
    simp only [TriadData.eval, triad, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    ring

/-- Replaying the first flip certificate preserves the represented tensor. -/
theorem firstFlip_output_sumTensor [CommRing k] (u : Fin a → k)
    (v₀ v₁ : Fin b → k) (w₀ w₁ : Fin c → k) (q : k) :
    (firstFlipCertificate u v₀ v₁ w₀ w₁ q).output.sumTensor =
      (pairScheme (u, v₀, w₀) (u, v₁, w₁)).sumTensor :=
  (firstFlipCertificate u v₀ v₁ w₀ w₁ q).sumTensor_eq

/-- Replaying the second flip certificate preserves the represented tensor. -/
theorem secondFlip_output_sumTensor [CommRing k] (u₀ u₁ : Fin a → k)
    (v : Fin b → k) (w₀ w₁ : Fin c → k) (q : k) :
    (secondFlipCertificate u₀ u₁ v w₀ w₁ q).output.sumTensor =
      (pairScheme (u₀, v, w₀) (u₁, v, w₁)).sumTensor :=
  (secondFlipCertificate u₀ u₁ v w₀ w₁ q).sumTensor_eq

/-- Replaying the third flip certificate preserves the represented tensor. -/
theorem thirdFlip_output_sumTensor [CommRing k] (u₀ u₁ : Fin a → k)
    (v₀ v₁ : Fin b → k) (w : Fin c → k) (q : k) :
    (thirdFlipCertificate u₀ u₁ v₀ v₁ w q).output.sumTensor =
      (pairScheme (u₀, v₀, w) (u₁, v₁, w)).sumTensor :=
  (thirdFlipCertificate u₀ u₁ v₀ v₁ w q).sumTensor_eq

/-- The inverse first flip, with coefficient `-q`, is itself a local certificate. -/
def inverseFirstFlipCertificate [CommRing k] (u : Fin a → k)
    (v₀ v₁ : Fin b → k) (w₀ w₁ : Fin c → k) (q : k) :
    Replacement.Certificate
      (pairScheme (u, v₀ + q • v₁, w₀) (u, v₁, w₁ - q • w₀)) where
  removed := Finset.univ
  inserted := [(u, v₀, w₀), (u, v₁, w₁)]
  local_eq := by
    rw [selectedTensor_pairScheme_univ, insertedTensor_pair]
    funext i j l
    simp only [TriadData.eval, triad, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    ring

/-- The inverse second flip, with coefficient `-q`, is itself a local certificate. -/
def inverseSecondFlipCertificate [CommRing k] (u₀ u₁ : Fin a → k)
    (v : Fin b → k) (w₀ w₁ : Fin c → k) (q : k) :
    Replacement.Certificate
      (pairScheme (u₀ + q • u₁, v, w₀) (u₁, v, w₁ - q • w₀)) where
  removed := Finset.univ
  inserted := [(u₀, v, w₀), (u₁, v, w₁)]
  local_eq := by
    rw [selectedTensor_pairScheme_univ, insertedTensor_pair]
    funext i j l
    simp only [TriadData.eval, triad, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    ring

/-- The inverse third flip, with coefficient `-q`, is itself a local certificate. -/
def inverseThirdFlipCertificate [CommRing k] (u₀ u₁ : Fin a → k)
    (v₀ v₁ : Fin b → k) (w : Fin c → k) (q : k) :
    Replacement.Certificate
      (pairScheme (u₀ + q • u₁, v₀, w) (u₁, v₁ - q • v₀, w)) where
  removed := Finset.univ
  inserted := [(u₀, v₀, w), (u₁, v₁, w)]
  local_eq := by
    rw [selectedTensor_pairScheme_univ, insertedTensor_pair]
    funext i j l
    simp only [TriadData.eval, triad, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    ring

/-- Replaying the inverse first flip certificate preserves the represented tensor. -/
theorem inverseFirstFlip_output_sumTensor [CommRing k] (u : Fin a → k)
    (v₀ v₁ : Fin b → k) (w₀ w₁ : Fin c → k) (q : k) :
    (inverseFirstFlipCertificate u v₀ v₁ w₀ w₁ q).output.sumTensor =
      (pairScheme (u, v₀ + q • v₁, w₀) (u, v₁, w₁ - q • w₀)).sumTensor :=
  (inverseFirstFlipCertificate u v₀ v₁ w₀ w₁ q).sumTensor_eq

/-- Replaying the inverse second flip certificate preserves the represented tensor. -/
theorem inverseSecondFlip_output_sumTensor [CommRing k] (u₀ u₁ : Fin a → k)
    (v : Fin b → k) (w₀ w₁ : Fin c → k) (q : k) :
    (inverseSecondFlipCertificate u₀ u₁ v w₀ w₁ q).output.sumTensor =
      (pairScheme (u₀ + q • u₁, v, w₀) (u₁, v, w₁ - q • w₀)).sumTensor :=
  (inverseSecondFlipCertificate u₀ u₁ v w₀ w₁ q).sumTensor_eq

/-- Replaying the inverse third flip certificate preserves the represented tensor. -/
theorem inverseThirdFlip_output_sumTensor [CommRing k] (u₀ u₁ : Fin a → k)
    (v₀ v₁ : Fin b → k) (w : Fin c → k) (q : k) :
    (inverseThirdFlipCertificate u₀ u₁ v₀ v₁ w q).output.sumTensor =
      (pairScheme (u₀ + q • u₁, v₀, w) (u₁, v₁ - q • v₀, w)).sumTensor :=
  (inverseThirdFlipCertificate u₀ u₁ v₀ v₁ w q).sumTensor_eq

/-- Nonzero projective equality records a nonzero scalar refactorization. -/
def ProjectivelyEqual [Field k] {ι : Type*} (x y : ι → k) : Prop :=
  ∃ q : k, q ≠ 0 ∧ y = q • x

/-- A two-scalar gauge change of a triad, compensated in its third factor. -/
def refactor [Field k] (t : TriadData k a b c) (q p : k) :
    TriadData k a b c :=
  (q • t.1, p • t.2.1, (q * p)⁻¹ • t.2.2)

/-- A nonzero two-scalar refactorization leaves the evaluated rank-one tensor unchanged. -/
theorem eval_refactor [Field k] (t : TriadData k a b c) (q p : k)
    (hq : q ≠ 0) (hp : p ≠ 0) : (refactor t q p).eval = t.eval := by
  funext i j l
  simp only [refactor, TriadData.eval, triad, Pi.smul_apply, smul_eq_mul]
  field_simp

/-- Two schemes have equal evaluated tensors term by term; this relation deliberately does
not assert gauge or projective equivalence of their stored factors. -/
def SameTensors [CommSemiring k] (S R : Scheme k a b c r) : Prop :=
  ∀ s, (S.term s).eval = (R.term s).eval

/-- Termwise tensor equality implies equality of the represented tensor. -/
theorem SameTensors.sumTensor_eq [CommSemiring k] {S R : Scheme k a b c r}
    (h : SameTensors S R) : S.sumTensor = R.sumTensor :=
  Scheme.sumTensor_eq_of_eval_eq h

/-- An explicit projective refactorization changes every stored triad only by two nonzero
scalars and the compensating inverse scalar in the third factor. -/
structure ProjectiveRefactorization [Field k] (S R : Scheme k a b c r) where
  /-- First-factor scale in each ordered slot. -/
  firstScale : Fin r → k
  /-- Second-factor scale in each ordered slot. -/
  secondScale : Fin r → k
  /-- Every first-factor scale is nonzero. -/
  firstScale_ne_zero : ∀ s, firstScale s ≠ 0
  /-- Every second-factor scale is nonzero. -/
  secondScale_ne_zero : ∀ s, secondScale s ≠ 0
  /-- The target factors are exactly the prescribed compensated refactorizations. -/
  term_eq : ∀ s, R.term s = refactor (S.term s) (firstScale s) (secondScale s)

/-- The identity scales give an explicit projective refactorization of a scheme to itself. -/
def ProjectiveRefactorization.refl [Field k] (S : Scheme k a b c r) :
    ProjectiveRefactorization S S where
  firstScale := fun _ => 1
  secondScale := fun _ => 1
  firstScale_ne_zero := fun _ => one_ne_zero
  secondScale_ne_zero := fun _ => one_ne_zero
  term_eq := by
    intro s
    simp [refactor]

/-- An explicit projective refactorization has equal evaluated tensors term by term. -/
theorem ProjectiveRefactorization.sameTensors [Field k] {S R : Scheme k a b c r}
    (h : ProjectiveRefactorization S R) : SameTensors S R := by
  intro s
  rw [h.term_eq s]
  exact (eval_refactor (S.term s) (h.firstScale s) (h.secondScale s)
    (h.firstScale_ne_zero s) (h.secondScale_ne_zero s)).symm

/-- Identity projective refactorization has the intended termwise tensor semantics. -/
example [Field k] (S : Scheme k a b c r) :
    SameTensors S S :=
  (ProjectiveRefactorization.refl S).sameTensors

/-- A factor position in a rank-one triad. -/
inductive FactorPosition
  | first
  | second
  | third
  deriving DecidableEq, Repr

/-- Read one of the three factors of a triad as a vector in the corresponding mode. -/
def factorAt (p : FactorPosition) (t : TriadData k a b c) :
    match p with
    | .first => Fin a → k
    | .second => Fin b → k
    | .third => Fin c → k :=
  match p with
  | .first => t.1
  | .second => t.2.1
  | .third => t.2.2

/-- A two-term scheme repeats a nonzero factor at a selected position. -/
def RepeatedNonzeroFactor [Ring k] (S : Scheme k a b c 2)
    (p : FactorPosition) : Prop :=
  match p with
  | .first => (S.term 0).1 ≠ 0 ∧ (S.term 0).1 = (S.term 1).1
  | .second => (S.term 0).2.1 ≠ 0 ∧ (S.term 0).2.1 = (S.term 1).2.1
  | .third => (S.term 0).2.2 ≠ 0 ∧ (S.term 0).2.2 = (S.term 1).2.2

/-- Apply an ordinary shear to the two slots of a scheme in the selected shared mode. -/
def flipPair [Ring k] (S : Scheme k a b c 2) (p : FactorPosition) (q : k) :
    Scheme k a b c 2 :=
  let t₀ := S.term 0
  let t₁ := S.term 1
  match p with
  | .first => pairScheme (t₀.1, t₀.2.1 + q • t₁.2.1, t₀.2.2)
      (t₁.1, t₁.2.1, t₁.2.2 - q • t₀.2.2)
  | .second => pairScheme (t₀.1 + q • t₁.1, t₀.2.1, t₀.2.2)
      (t₁.1, t₁.2.1, t₁.2.2 - q • t₀.2.2)
  | .third => pairScheme (t₀.1 + q • t₁.1, t₀.2.1, t₀.2.2)
      (t₁.1, t₁.2.1 - q • t₀.2.1, t₁.2.2)

/-- A literal ordinary shear at a repeated factor preserves the two-term tensor. -/
theorem sumTensor_flipPair [Field k] (S : Scheme k a b c 2)
    (p : FactorPosition) (q : k) (hrep : RepeatedNonzeroFactor S p) :
    (flipPair S p q).sumTensor = S.sumTensor := by
  cases p with
  | first =>
      funext i j l
      have hshared := congrFun hrep.2 i
      simp only [Scheme.sumTensor, TriadData.eval, triad, flipPair, pairScheme,
        Fin.isValue, Fin.sum_univ_two, ↓reduceIte, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, one_ne_zero, Pi.sub_apply]
      rw [← hshared]
      ring
  | second =>
      funext i j l
      have hshared := congrFun hrep.2 j
      simp only [Scheme.sumTensor, TriadData.eval, triad, flipPair, pairScheme,
        Fin.isValue, Prod.mk.eta, Fin.sum_univ_two, ↓reduceIte, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, one_ne_zero, Pi.sub_apply]
      rw [← hshared]
      ring
  | third =>
      funext i j l
      have hshared := congrFun hrep.2 l
      simp only [Scheme.sumTensor, TriadData.eval, triad, flipPair, pairScheme,
        Fin.isValue, Prod.mk.eta, Fin.sum_univ_two, ↓reduceIte, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, one_ne_zero, Pi.sub_apply]
      rw [← hshared]
      ring

/-- A nonzero evaluated rank-one tensor has three nonzero stored factors. -/
theorem TriadData.factors_ne_zero_of_eval_ne_zero [Field k]
    (t : TriadData k a b c) (h : t.eval ≠ 0) :
    t.1 ≠ 0 ∧ t.2.1 ≠ 0 ∧ t.2.2 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    apply h
    funext i j l
    simp [TriadData.eval, triad, hzero]
  · intro hzero
    apply h
    funext i j l
    simp [TriadData.eval, triad, hzero]
  · intro hzero
    apply h
    funext i j l
    simp [TriadData.eval, triad, hzero]

/-- Tensor preservation of a nonzero two-term shear forces the selected source factor to be
literally repeated. This converse makes ordinary-flip legality independent of the search index. -/
theorem repeatedNonzeroFactor_of_sumTensor_flipPair_eq [Field k]
    (S : Scheme k a b c 2) (p : FactorPosition) (q : k) (hq : q ≠ 0)
    (hnz : ∀ s, (S.term s).eval ≠ 0)
    (hsum : (flipPair S p q).sumTensor = S.sumTensor) :
    RepeatedNonzeroFactor S p := by
  have hfac0 := TriadData.factors_ne_zero_of_eval_ne_zero (S.term 0) (hnz 0)
  have hfac1 := TriadData.factors_ne_zero_of_eval_ne_zero (S.term 1) (hnz 1)
  cases p with
  | first =>
      refine ⟨hfac0.1, ?_⟩
      obtain ⟨j, hv1⟩ := Function.ne_iff.mp hfac1.2.1
      obtain ⟨l, hw0⟩ := Function.ne_iff.mp hfac0.2.2
      simp only [Pi.zero_apply] at hv1 hw0
      funext i
      have hcoord := congrFun (congrFun (congrFun hsum i) j) l
      simp only [sumTensor, TriadData.eval, triad, flipPair, pairScheme, Fin.isValue,
        Fin.sum_univ_two, ↓reduceIte, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_ne_zero,
        Pi.sub_apply] at hcoord
      have hprod : q * ((S.term 0).1 i - (S.term 1).1 i) * (S.term 1).2.1 j *
          (S.term 0).2.2 l = 0 := by
        linear_combination hcoord
      rcases mul_eq_zero.mp hprod with hleft | hwl
      · rcases mul_eq_zero.mp hleft with hleft | hvj
        · rcases mul_eq_zero.mp hleft with hq0 | hdiff
          · exact (hq hq0).elim
          · exact sub_eq_zero.mp hdiff
        · exact (hv1 hvj).elim
      · exact (hw0 hwl).elim
  | second =>
      refine ⟨hfac0.2.1, ?_⟩
      obtain ⟨i, hu1⟩ := Function.ne_iff.mp hfac1.1
      obtain ⟨l, hw0⟩ := Function.ne_iff.mp hfac0.2.2
      simp only [Pi.zero_apply] at hu1 hw0
      funext j
      have hcoord := congrFun (congrFun (congrFun hsum i) j) l
      simp only [sumTensor, TriadData.eval, triad, flipPair, pairScheme, Fin.isValue,
        Fin.sum_univ_two, ↓reduceIte, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_ne_zero,
        Pi.sub_apply] at hcoord
      have hprod : q * (S.term 1).1 i * ((S.term 0).2.1 j - (S.term 1).2.1 j) *
          (S.term 0).2.2 l = 0 := by
        linear_combination hcoord
      rcases mul_eq_zero.mp hprod with hleft | hwl
      · rcases mul_eq_zero.mp hleft with hleft | hdiff
        · rcases mul_eq_zero.mp hleft with hq0 | hui
          · exact (hq hq0).elim
          · exact (hu1 hui).elim
        · exact sub_eq_zero.mp hdiff
      · exact (hw0 hwl).elim
  | third =>
      refine ⟨hfac0.2.2, ?_⟩
      obtain ⟨i, hu1⟩ := Function.ne_iff.mp hfac1.1
      obtain ⟨j, hv0⟩ := Function.ne_iff.mp hfac0.2.1
      simp only [Pi.zero_apply] at hu1 hv0
      funext l
      have hcoord := congrFun (congrFun (congrFun hsum i) j) l
      simp only [sumTensor, TriadData.eval, triad, flipPair, pairScheme, Fin.isValue,
        Fin.sum_univ_two, ↓reduceIte, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_ne_zero,
        Pi.sub_apply] at hcoord
      have hprod : q * (S.term 1).1 i * (S.term 0).2.1 j *
          ((S.term 0).2.2 l - (S.term 1).2.2 l) = 0 := by
        linear_combination hcoord
      rcases mul_eq_zero.mp hprod with hleft | hdiff
      · rcases mul_eq_zero.mp hleft with hleft | hvj
        · rcases mul_eq_zero.mp hleft with hq0 | hui
          · exact (hq hq0).elim
          · exact (hu1 hui).elim
        · exact (hv0 hvj).elim
      · exact sub_eq_zero.mp hdiff

/-- Applying the opposite shear in the same mode recovers the original pair. -/
theorem flipPair_neg [Field k] (S : Scheme k a b c 2)
    (p : FactorPosition) (q : k) :
    flipPair (flipPair S p q) p (-q) = S := by
  rcases S with ⟨term⟩
  cases p <;> change Scheme.mk _ = Scheme.mk term <;> congr 1 <;>
    funext s <;> fin_cases s <;> simp [flipPair, pairScheme]

/-- A deliberately narrow nontrivial ordinary flip between exactly two nonzero terms. Its
legality is stated independently by represented-tensor equality; the repeated position is a
derived theorem rather than a field supplied by the caller. -/
structure NontrivialOrdinaryTwoTermFlip [Field k]
    (S R : Scheme k a b c 2) where
  /-- The selected shear position. -/
  position : FactorPosition
  /-- The nonzero shear coefficient. -/
  coefficient : k
  /-- The shear coefficient is nonzero. -/
  coefficient_ne_zero : coefficient ≠ 0
  /-- The target is exactly the selected ordinary shear. -/
  target_eq : R = flipPair S position coefficient
  /-- The independently specified move preserves the represented tensor. -/
  tensor_eq : R.sumTensor = S.sumTensor
  /-- Both source term tensors are nonzero. -/
  source_term_ne_zero : ∀ s, (S.term s).eval ≠ 0
  /-- Both target term tensors are nonzero. -/
  target_term_ne_zero : ∀ s, (R.term s).eval ≠ 0
  /-- The move changes its stored two-term presentation. -/
  source_ne_target : S ≠ R

/-- Algebraic legality and source nondegeneracy force the selected factor to be repeated. -/
theorem NontrivialOrdinaryTwoTermFlip.repeated [Field k]
    {S R : Scheme k a b c 2} (h : NontrivialOrdinaryTwoTermFlip S R) :
    RepeatedNonzeroFactor S h.position := by
  apply repeatedNonzeroFactor_of_sumTensor_flipPair_eq S h.position h.coefficient
    h.coefficient_ne_zero h.source_term_ne_zero
  simpa only [h.target_eq] using h.tensor_eq

/-- The inverse of a nontrivial ordinary flip is the opposite shear in the same mode. -/
def NontrivialOrdinaryTwoTermFlip.symm [Field k]
    {S R : Scheme k a b c 2} (h : NontrivialOrdinaryTwoTermFlip S R) :
    NontrivialOrdinaryTwoTermFlip R S := by
  obtain ⟨p, q, hq, htarget, htensor, hsource, htargetNonzero, hne⟩ := h
  subst R
  refine
    { position := p
      coefficient := -q
      coefficient_ne_zero := neg_ne_zero.mpr hq
      target_eq := (flipPair_neg S p q).symm
      tensor_eq := htensor.symm
      source_term_ne_zero := htargetNonzero
      target_term_ne_zero := hsource
      source_ne_target := fun heq => hne heq.symm }

/-- A projective ordinary flip permits only explicit nonzero scalar refactorizations before and
after an independently legal literal flip. -/
structure ProjectiveOrdinaryTwoTermFlip [Field k]
    (S R : Scheme k a b c 2) where
  /-- A source refactorization. -/
  sourceRefactor : Scheme k a b c 2
  /-- A target refactorization. -/
  targetRefactor : Scheme k a b c 2
  /-- Exact nonzero scalar data for the source refactorization. -/
  source_projective : ProjectiveRefactorization S sourceRefactor
  /-- Exact nonzero scalar data for the target refactorization. -/
  target_projective : ProjectiveRefactorization R targetRefactor
  /-- The refactorized presentations are joined by a literal ordinary flip. -/
  ordinary : NontrivialOrdinaryTwoTermFlip sourceRefactor targetRefactor

/-- Every projective ordinary flip preserves the represented tensor. -/
theorem ProjectiveOrdinaryTwoTermFlip.sumTensor_eq [Field k]
    {S R : Scheme k a b c 2} (h : ProjectiveOrdinaryTwoTermFlip S R) :
    S.sumTensor = R.sumTensor := by
  have hflip : h.sourceRefactor.sumTensor = h.targetRefactor.sumTensor :=
    h.ordinary.tensor_eq.symm
  exact h.source_projective.sameTensors.sumTensor_eq.trans
    (hflip.trans h.target_projective.sameTensors.sumTensor_eq.symm)

/-- Reversing the independently legal ordinary flip and swapping the two explicit
refactorizations gives the inverse projective ordinary flip. -/
def ProjectiveOrdinaryTwoTermFlip.symm [Field k]
    {S R : Scheme k a b c 2} (h : ProjectiveOrdinaryTwoTermFlip S R) :
    ProjectiveOrdinaryTwoTermFlip R S where
  sourceRefactor := h.targetRefactor
  targetRefactor := h.sourceRefactor
  source_projective := h.target_projective
  target_projective := h.source_projective
  ordinary := h.ordinary.symm

/-- Package a projective ordinary two-term flip as a genuine local replacement at any two
distinct slots of an ambient scheme. The inserted list is deterministically ordered as target
slot zero followed by target slot one. -/
def ProjectiveOrdinaryTwoTermFlip.forwardCertificateAt [Field k]
    {A B : Scheme k a b c 2} (h : ProjectiveOrdinaryTwoTermFlip A B)
    (S : Scheme k a b c r) (s₀ s₁ : Fin r) (hslots : s₀ ≠ s₁)
    (hsource : pairScheme (S.term s₀) (S.term s₁) = A) :
    Replacement.Certificate S where
  removed := {s₀, s₁}
  inserted := [B.term 0, B.term 1]
  local_eq := by
    rw [selectedTensor_pairSlots S s₀ s₁ hslots, insertedTensor_pair]
    calc
      (S.term s₀).eval + (S.term s₁).eval =
          (pairScheme (S.term s₀) (S.term s₁)).sumTensor :=
        (sumTensor_two (pairScheme (S.term s₀) (S.term s₁))).symm
      _ = A.sumTensor := congrArg Scheme.sumTensor hsource
      _ = B.sumTensor := h.sumTensor_eq
      _ = (B.term 0).eval + (B.term 1).eval := sumTensor_two B

/-- Package the inverse of a projective ordinary two-term flip as a genuine local replacement
at any two distinct slots of an ambient target scheme. The inserted source terms retain the
original deterministic order zero then one. -/
def ProjectiveOrdinaryTwoTermFlip.inverseCertificateAt [Field k]
    {A B : Scheme k a b c 2} (h : ProjectiveOrdinaryTwoTermFlip A B)
    (R : Scheme k a b c r) (s₀ s₁ : Fin r) (hslots : s₀ ≠ s₁)
    (htarget : pairScheme (R.term s₀) (R.term s₁) = B) :
    Replacement.Certificate R :=
  h.symm.forwardCertificateAt R s₀ s₁ hslots htarget

/-- The forward ambient certificate removes exactly the two requested slots. -/
@[simp] theorem ProjectiveOrdinaryTwoTermFlip.forwardCertificateAt_removed [Field k]
    {A B : Scheme k a b c 2} (h : ProjectiveOrdinaryTwoTermFlip A B)
    (S : Scheme k a b c r) (s₀ s₁ : Fin r) (hslots : s₀ ≠ s₁)
    (hsource : pairScheme (S.term s₀) (S.term s₁) = A) :
    (h.forwardCertificateAt S s₀ s₁ hslots hsource).removed = {s₀, s₁} := rfl

/-- The forward ambient certificate inserts the target pair in slot order. -/
@[simp] theorem ProjectiveOrdinaryTwoTermFlip.forwardCertificateAt_inserted [Field k]
    {A B : Scheme k a b c 2} (h : ProjectiveOrdinaryTwoTermFlip A B)
    (S : Scheme k a b c r) (s₀ s₁ : Fin r) (hslots : s₀ ≠ s₁)
    (hsource : pairScheme (S.term s₀) (S.term s₁) = A) :
    (h.forwardCertificateAt S s₀ s₁ hslots hsource).inserted =
      [B.term 0, B.term 1] := rfl

/-- The inverse ambient certificate removes exactly the two requested target slots. -/
@[simp] theorem ProjectiveOrdinaryTwoTermFlip.inverseCertificateAt_removed [Field k]
    {A B : Scheme k a b c 2} (h : ProjectiveOrdinaryTwoTermFlip A B)
    (R : Scheme k a b c r) (s₀ s₁ : Fin r) (hslots : s₀ ≠ s₁)
    (htarget : pairScheme (R.term s₀) (R.term s₁) = B) :
    (h.inverseCertificateAt R s₀ s₁ hslots htarget).removed = {s₀, s₁} := rfl

/-- The inverse ambient certificate inserts the source pair in slot order. -/
@[simp] theorem ProjectiveOrdinaryTwoTermFlip.inverseCertificateAt_inserted [Field k]
    {A B : Scheme k a b c 2} (h : ProjectiveOrdinaryTwoTermFlip A B)
    (R : Scheme k a b c r) (s₀ s₁ : Fin r) (hslots : s₀ ≠ s₁)
    (htarget : pairScheme (R.term s₀) (R.term s₁) = B) :
    (h.inverseCertificateAt R s₀ s₁ hslots htarget).inserted =
      [A.term 0, A.term 1] := rfl

/-- The forward ambient certificate carries the exact local equality between the two removed
source slots and the deterministically ordered target pair. -/
theorem ProjectiveOrdinaryTwoTermFlip.forwardCertificateAt_local_eq [Field k]
    {A B : Scheme k a b c 2} (h : ProjectiveOrdinaryTwoTermFlip A B)
    (S : Scheme k a b c r) (s₀ s₁ : Fin r) (hslots : s₀ ≠ s₁)
    (hsource : pairScheme (S.term s₀) (S.term s₁) = A) :
    Replacement.selectedTensor S {s₀, s₁} =
      Replacement.insertedTensor [B.term 0, B.term 1] :=
  (h.forwardCertificateAt S s₀ s₁ hslots hsource).local_eq

/-- The inverse ambient certificate carries the exact local equality between the two removed
target slots and the deterministically ordered source pair. -/
theorem ProjectiveOrdinaryTwoTermFlip.inverseCertificateAt_local_eq [Field k]
    {A B : Scheme k a b c 2} (h : ProjectiveOrdinaryTwoTermFlip A B)
    (R : Scheme k a b c r) (s₀ s₁ : Fin r) (hslots : s₀ ≠ s₁)
    (htarget : pairScheme (R.term s₀) (R.term s₁) = B) :
    Replacement.selectedTensor R {s₀, s₁} =
      Replacement.insertedTensor [A.term 0, A.term 1] :=
  (h.inverseCertificateAt R s₀ s₁ hslots htarget).local_eq

/-- Replaying the forward ambient certificate preserves the full ambient tensor. -/
theorem ProjectiveOrdinaryTwoTermFlip.forwardCertificateAt_sumTensor_eq [Field k]
    {A B : Scheme k a b c 2} (h : ProjectiveOrdinaryTwoTermFlip A B)
    (S : Scheme k a b c r) (s₀ s₁ : Fin r) (hslots : s₀ ≠ s₁)
    (hsource : pairScheme (S.term s₀) (S.term s₁) = A) :
    (h.forwardCertificateAt S s₀ s₁ hslots hsource).output.sumTensor = S.sumTensor :=
  (h.forwardCertificateAt S s₀ s₁ hslots hsource).sumTensor_eq

/-- Replaying the inverse ambient certificate preserves the full ambient tensor. -/
theorem ProjectiveOrdinaryTwoTermFlip.inverseCertificateAt_sumTensor_eq [Field k]
    {A B : Scheme k a b c 2} (h : ProjectiveOrdinaryTwoTermFlip A B)
    (R : Scheme k a b c r) (s₀ s₁ : Fin r) (hslots : s₀ ≠ s₁)
    (htarget : pairScheme (R.term s₀) (R.term s₁) = B) :
    (h.inverseCertificateAt R s₀ s₁ hslots htarget).output.sumTensor = R.sumTensor :=
  (h.inverseCertificateAt R s₀ s₁ hslots htarget).sumTensor_eq

/-- A finite family spans exactly one line when all its vectors are scalar multiples
of one nonzero vector and at least one family member is nonzero. -/
def SpansOneDimensional {V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (x : Fin r → V) : Prop :=
  ∃ u : V, u ≠ 0 ∧ (∀ s, ∃ q : k, x s = q • u) ∧ ∃ s, x s ≠ 0

/-- A common first factor and dependent second factors give an explicit one-term elimination. -/
theorem rankLE_sum_scalar_shared_first_of_not_linearIndependent
    [Field k] (hr : 0 < r) (u : Fin a → k) (q : Fin r → k)
    (v : Fin r → Fin b → k) (w : Fin r → Fin c → k)
    (hdep : ¬ LinearIndependent k v) :
    RankLE (fun i j l => ∑ s, (q s • u) i * v s j * w s l) (r - 1) := by
  cases r with
  | zero => simp at hr
  | succ n =>
      rw [Fintype.linearIndependent_iff] at hdep
      push Not at hdep
      obtain ⟨g, hg, p, hgp⟩ := hdep
      let w' : Fin n → Fin c → k := fun t l =>
        q (p.succAbove t) * w (p.succAbove t) l -
          (g (p.succAbove t) / g p) * q p * w p l
      refine ⟨fun _ => u, fun t => v (p.succAbove t), w', ?_⟩
      funext i j l
      have hrel : (∑ s, g s * v s j) = 0 := by
        have hcoord := congrFun hg j
        simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Pi.zero_apply] using hcoord
      rw [Fin.sum_univ_succAbove (fun s => g s * v s j) p] at hrel
      have hpterm : g p * v p j =
          -(∑ t, g (p.succAbove t) * v (p.succAbove t) j) :=
        eq_neg_of_add_eq_zero_left hrel
      have hvp : v p j = ∑ t, -(g (p.succAbove t) / g p) *
          v (p.succAbove t) j := by
        calc
          v p j = (g p)⁻¹ * (g p * v p j) := by
            rw [← mul_assoc, inv_mul_cancel₀ hgp, one_mul]
          _ = (g p)⁻¹ * (-(∑ t, g (p.succAbove t) *
              v (p.succAbove t) j)) := by rw [hpterm]
          _ = ∑ t, -(g (p.succAbove t) / g p) *
              v (p.succAbove t) j := by
            rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro t _ht
            simp only [div_eq_mul_inv]
            ring
      rw [Fin.sum_univ_succAbove
        (fun s => (q s • u) i * v s j * w s l) p]
      simp only [Pi.smul_apply, smul_eq_mul, Nat.succ_sub_one]
      rw [hvp, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t _ht
      simp only [w']
      ring

/-- If one factor family spans one dimension and a second is dependent, the local
tensor has a decomposition with one fewer term. -/
theorem rankLE_sum_of_spansOneDimensional_of_not_linearIndependent
    [Field k] (hr : 0 < r) (x : Fin r → Fin a → k)
    (y : Fin r → Fin b → k) (z : Fin r → Fin c → k)
    (hx : SpansOneDimensional (k := k) x) (hy : ¬ LinearIndependent k y) :
    RankLE (fun i j l => ∑ s, x s i * y s j * z s l) (r - 1) := by
  obtain ⟨u, _hu, hmultiple, _hmember⟩ := hx
  let q : Fin r → k := fun s => Classical.choose (hmultiple s)
  have hq : ∀ s, x s = q s • u := fun s => Classical.choose_spec (hmultiple s)
  have hreduce := rankLE_sum_scalar_shared_first_of_not_linearIndependent
    (k := k) hr u q y z hy
  convert hreduce using 1
  funext i j l
  apply Finset.sum_congr rfl
  intro s _hs
  rw [hq s]

/-- If any one factor family spans one dimension and either of the other two factor
families is linearly dependent, the local tensor has a decomposition with one fewer term.
The six disjuncts explicitly cover every ordered pair of distinct factor positions. -/
theorem rankLE_sum_of_oneDimensional_factor_of_dependent_other
    [Field k] (hr : 0 < r) (x : Fin r → Fin a → k)
    (y : Fin r → Fin b → k) (z : Fin r → Fin c → k)
    (hpair :
      (SpansOneDimensional (k := k) x ∧ ¬ LinearIndependent k y) ∨
      (SpansOneDimensional (k := k) x ∧ ¬ LinearIndependent k z) ∨
      (SpansOneDimensional (k := k) y ∧ ¬ LinearIndependent k x) ∨
      (SpansOneDimensional (k := k) y ∧ ¬ LinearIndependent k z) ∨
      (SpansOneDimensional (k := k) z ∧ ¬ LinearIndependent k x) ∨
      (SpansOneDimensional (k := k) z ∧ ¬ LinearIndependent k y)) :
    RankLE (fun i j l => ∑ s, x s i * y s j * z s l) (r - 1) := by
  rcases hpair with hxy | hxz | hyx | hyz | hzx | hzy
  · exact rankLE_sum_of_spansOneDimensional_of_not_linearIndependent
      hr x y z hxy.1 hxy.2
  · obtain ⟨u, v, w, hsum⟩ :=
      rankLE_sum_of_spansOneDimensional_of_not_linearIndependent
        hr x z y hxz.1 hxz.2
    refine ⟨u, w, v, ?_⟩
    funext i j l
    have hcoord := congrFun (congrFun (congrFun hsum i) l) j
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hcoord
  · obtain ⟨u, v, w, hsum⟩ :=
      rankLE_sum_of_spansOneDimensional_of_not_linearIndependent
        hr y x z hyx.1 hyx.2
    refine ⟨v, u, w, ?_⟩
    funext i j l
    have hcoord := congrFun (congrFun (congrFun hsum j) i) l
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hcoord
  · obtain ⟨u, v, w, hsum⟩ :=
      rankLE_sum_of_spansOneDimensional_of_not_linearIndependent
        hr y z x hyz.1 hyz.2
    refine ⟨w, u, v, ?_⟩
    funext i j l
    have hcoord := congrFun (congrFun (congrFun hsum j) l) i
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hcoord
  · obtain ⟨u, v, w, hsum⟩ :=
      rankLE_sum_of_spansOneDimensional_of_not_linearIndependent
        hr z x y hzx.1 hzx.2
    refine ⟨v, w, u, ?_⟩
    funext i j l
    have hcoord := congrFun (congrFun (congrFun hsum l) i) j
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hcoord
  · obtain ⟨u, v, w, hsum⟩ :=
      rankLE_sum_of_spansOneDimensional_of_not_linearIndependent
        hr z y x hzy.1 hzy.2
    refine ⟨w, v, u, ?_⟩
    funext i j l
    have hcoord := congrFun (congrFun (congrFun hsum l) j) i
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hcoord

/-- The explicit F2 repeated-factor index checks exactly the three factor positions. -/
def repeatedFactorIndexF2 (S : Scheme (ZMod 2) a b c 2) : List FactorPosition :=
  (if (S.term 0).1 ≠ 0 ∧ (S.term 0).1 = (S.term 1).1 then [.first] else []) ++
  (if (S.term 0).2.1 ≠ 0 ∧ (S.term 0).2.1 = (S.term 1).2.1 then [.second] else []) ++
  (if (S.term 0).2.2 ≠ 0 ∧ (S.term 0).2.2 = (S.term 1).2.2 then [.third] else [])

/-- The unique nonzero scalar of `ZMod 2` is one. -/
theorem zmod2_eq_one_of_ne_zero (q : ZMod 2) (hq : q ≠ 0) : q = 1 := by
  fin_cases q
  · exact (hq rfl).elim
  · rfl

/-- Over `ZMod 2`, explicit nonzero projective refactorization data forces literal equality
of the stored schemes. -/
theorem ProjectiveRefactorization.eq_f2
    {S R : Scheme (ZMod 2) a b c r} (h : ProjectiveRefactorization S R) : R = S := by
  rcases S with ⟨S⟩
  rcases R with ⟨R⟩
  congr 1
  funext s
  have hq : h.firstScale s = 1 :=
    zmod2_eq_one_of_ne_zero (h.firstScale s) (h.firstScale_ne_zero s)
  have hp : h.secondScale s = 1 :=
    zmod2_eq_one_of_ne_zero (h.secondScale s) (h.secondScale_ne_zero s)
  have hterm : R s = refactor (S s) (h.firstScale s) (h.secondScale s) := h.term_eq s
  rw [hterm, hq, hp]
  simp [refactor]

/-- Over F2, nonzero projective equality is literal equality. -/
theorem projectivelyEqual_iff_eq_f2 {ι : Type*} (x y : ι → ZMod 2)
    (_hx : x ≠ 0) (hy : y ≠ 0) : ProjectivelyEqual x y ↔ x = y := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hqone : q = 1 := by
      fin_cases q
      · exact (hq rfl).elim
      · rfl
    simp only [hqone, one_smul]
  · intro hxy
    exact ⟨1, one_ne_zero, by simpa only [one_smul] using hxy.symm⟩

/-- The explicit F2 index contains exactly the algebraically legal repeated positions. -/
theorem mem_repeatedFactorIndexF2_iff (S : Scheme (ZMod 2) a b c 2)
    (p : FactorPosition) :
    p ∈ repeatedFactorIndexF2 S ↔ RepeatedNonzeroFactor S p := by
  cases p <;> simp [repeatedFactorIndexF2, RepeatedNonzeroFactor]

/-- Every nontrivial ordinary F2 two-term flip exposes a repeated nonzero
projective factor in one of the three positions. -/
theorem ordinaryTwoTermFlip_has_repeated_projective_factor_f2
    {S R : Scheme (ZMod 2) a b c 2}
    (h : NontrivialOrdinaryTwoTermFlip S R) :
    ((S.term 0).1 ≠ 0 ∧ (S.term 1).1 ≠ 0 ∧
      ProjectivelyEqual (S.term 0).1 (S.term 1).1) ∨
    ((S.term 0).2.1 ≠ 0 ∧ (S.term 1).2.1 ≠ 0 ∧
      ProjectivelyEqual (S.term 0).2.1 (S.term 1).2.1) ∨
    ((S.term 0).2.2 ≠ 0 ∧ (S.term 1).2.2 ≠ 0 ∧
      ProjectivelyEqual (S.term 0).2.2 (S.term 1).2.2) := by
  let hrep := h.repeated
  cases p : h.position with
  | first =>
      have hrep' : (S.term 0).1 ≠ 0 ∧ (S.term 0).1 = (S.term 1).1 := by
        simpa only [p, RepeatedNonzeroFactor] using hrep
      have hright : (S.term 1).1 ≠ 0 := fun hzero =>
        hrep'.1 (hrep'.2.trans hzero)
      left
      exact ⟨hrep'.1, hright,
        (projectivelyEqual_iff_eq_f2 _ _ hrep'.1 hright).mpr hrep'.2⟩
  | second =>
      have hrep' : (S.term 0).2.1 ≠ 0 ∧
          (S.term 0).2.1 = (S.term 1).2.1 := by
        simpa only [p, RepeatedNonzeroFactor] using hrep
      have hright : (S.term 1).2.1 ≠ 0 := fun hzero =>
        hrep'.1 (hrep'.2.trans hzero)
      right
      left
      exact ⟨hrep'.1, hright,
        (projectivelyEqual_iff_eq_f2 _ _ hrep'.1 hright).mpr hrep'.2⟩
  | third =>
      have hrep' : (S.term 0).2.2 ≠ 0 ∧
          (S.term 0).2.2 = (S.term 1).2.2 := by
        simpa only [p, RepeatedNonzeroFactor] using hrep
      have hright : (S.term 1).2.2 ≠ 0 := fun hzero =>
        hrep'.1 (hrep'.2.trans hzero)
      right
      right
      exact ⟨hrep'.1, hright,
        (projectivelyEqual_iff_eq_f2 _ _ hrep'.1 hright).mpr hrep'.2⟩

/-- Every algebraically legal ordinary F2 repeated-factor flip is returned by
the explicit repeated-factor enumeration. -/
theorem ordinaryTwoTermFlip_position_mem_index_f2
    {S R : Scheme (ZMod 2) a b c 2}
    (h : NontrivialOrdinaryTwoTermFlip S R) :
    h.position ∈ repeatedFactorIndexF2 S := by
  exact (mem_repeatedFactorIndexF2_iff S h.position).mpr h.repeated

/-- Every projective ordinary F2 two-term flip exposes a repeated nonzero projective factor
in its original source scheme. This is deliberately restricted to the projective ordinary
flip wrapper and says nothing about arbitrary replacement certificates. -/
theorem projectiveOrdinaryTwoTermFlip_has_repeated_projective_factor_f2
    {S R : Scheme (ZMod 2) a b c 2}
    (h : ProjectiveOrdinaryTwoTermFlip S R) :
    ((S.term 0).1 ≠ 0 ∧ (S.term 1).1 ≠ 0 ∧
      ProjectivelyEqual (S.term 0).1 (S.term 1).1) ∨
    ((S.term 0).2.1 ≠ 0 ∧ (S.term 1).2.1 ≠ 0 ∧
      ProjectivelyEqual (S.term 0).2.1 (S.term 1).2.1) ∨
    ((S.term 0).2.2 ≠ 0 ∧ (S.term 1).2.2 ≠ 0 ∧
      ProjectivelyEqual (S.term 0).2.2 (S.term 1).2.2) := by
  have hsource : h.sourceRefactor = S := h.source_projective.eq_f2
  simpa only [hsource] using
    ordinaryTwoTermFlip_has_repeated_projective_factor_f2 h.ordinary

/-- The literal ordinary position inside every projective ordinary F2 two-term flip occurs
in the complete repeated-factor index of its original source scheme. This theorem does not
classify arbitrary replacements. -/
theorem projectiveOrdinaryTwoTermFlip_position_mem_index_f2
    {S R : Scheme (ZMod 2) a b c 2}
    (h : ProjectiveOrdinaryTwoTermFlip S R) :
    h.ordinary.position ∈ repeatedFactorIndexF2 S := by
  have hsource : h.sourceRefactor = S := h.source_projective.eq_f2
  simpa only [hsource] using ordinaryTwoTermFlip_position_mem_index_f2 h.ordinary

namespace NonadjacentAmbientCertificate

/-- The first untouched rank-one term in the nonadjacent ambient fixture. -/
abbrev left : TriadData ℚ 1 1 1 :=
  ((fun _ => 2), (fun _ => 1), (fun _ => 1))

/-- The second untouched rank-one term in the nonadjacent ambient fixture. -/
abbrev middle : TriadData ℚ 1 1 1 :=
  ((fun _ => 3), (fun _ => 1), (fun _ => 1))

/-- The concrete ordinary source pair used by the nonadjacent ambient fixture. -/
abbrev sourcePair : Scheme ℚ 1 1 1 2 :=
  pairScheme ((fun _ => 1), (fun _ => 2), (fun _ => 5))
    ((fun _ => 1), (fun _ => 3), (fun _ => 7))

/-- The concrete ordinary target pair obtained by a nonzero first-factor shear. -/
abbrev targetPair : Scheme ℚ 1 1 1 2 :=
  flipPair sourcePair .first 4

/-- The concrete source pair has a nonzero repeated first factor. -/
theorem repeated : RepeatedNonzeroFactor sourcePair .first := by
  refine ⟨?_, rfl⟩
  intro hzero
  have hentry := congrFun hzero 0
  norm_num [sourcePair, pairScheme] at hentry

/-- The concrete source and target pairs form a nontrivial ordinary two-term flip. -/
def ordinary : NontrivialOrdinaryTwoTermFlip sourcePair targetPair := by
  refine
    { position := .first
      coefficient := 4
      coefficient_ne_zero := by decide
      target_eq := rfl
      tensor_eq := sumTensor_flipPair sourcePair .first 4 repeated
      source_term_ne_zero := ?_
      target_term_ne_zero := ?_
      source_ne_target := ?_ }
  · intro s hzero
    fin_cases s
    · have hentry := congrFun (congrFun (congrFun hzero 0) 0) 0
      norm_num [sourcePair, pairScheme, TriadData.eval, triad] at hentry
    · have hentry := congrFun (congrFun (congrFun hzero 0) 0) 0
      norm_num [sourcePair, pairScheme, TriadData.eval, triad] at hentry
  · intro s hzero
    fin_cases s
    · have hentry := congrFun (congrFun (congrFun hzero 0) 0) 0
      norm_num [targetPair, sourcePair, flipPair, pairScheme, TriadData.eval, triad] at hentry
    · have hentry := congrFun (congrFun (congrFun hzero 0) 0) 0
      norm_num [targetPair, sourcePair, flipPair, pairScheme, TriadData.eval, triad] at hentry
  · intro heq
    have hentry := congrArg (fun X => (X.term 0).2.1 0) heq
    norm_num [targetPair, sourcePair, flipPair, pairScheme] at hentry

/-- The concrete ordinary flip, regarded as a projective ordinary flip via reflexive
projective refactorizations at both ends. -/
def projective : ProjectiveOrdinaryTwoTermFlip sourcePair targetPair where
  sourceRefactor := sourcePair
  targetRefactor := targetPair
  source_projective := ProjectiveRefactorization.refl sourcePair
  target_projective := ProjectiveRefactorization.refl targetPair
  ordinary := ordinary

/-- The rank-four ambient source stores the selected source pair at slots one and three. -/
abbrev ambientSource : Scheme ℚ 1 1 1 4 :=
  ⟨![left, sourcePair.term 0, middle, sourcePair.term 1]⟩

/-- The rank-four ambient target stores the selected target pair at slots one and three. -/
abbrev ambientTarget : Scheme ℚ 1 1 1 4 :=
  ⟨![left, targetPair.term 0, middle, targetPair.term 1]⟩

/-- Selecting ambient source slots one and three recovers the concrete source pair. -/
theorem source_pair_slots :
    pairScheme (ambientSource.term 1) (ambientSource.term 3) = sourcePair := rfl

/-- Selecting ambient target slots one and three recovers the concrete target pair. -/
theorem target_pair_slots :
    pairScheme (ambientTarget.term 1) (ambientTarget.term 3) = targetPair := rfl

/-- The concrete forward certificate replaces nonadjacent ambient slots one and three. -/
abbrev forward : Replacement.Certificate ambientSource :=
  projective.forwardCertificateAt ambientSource 1 3 (by decide) source_pair_slots

/-- The concrete inverse certificate replaces nonadjacent ambient slots one and three. -/
abbrev inverse : Replacement.Certificate ambientTarget :=
  projective.inverseCertificateAt ambientTarget 1 3 (by decide) target_pair_slots

/-- The forward fixture removes exactly the two nonadjacent slots one and three. -/
theorem forward_removed : forward.removed = ({1, 3} : Finset (Fin 4)) := rfl

/-- The inverse fixture removes exactly the two nonadjacent slots one and three. -/
theorem inverse_removed : inverse.removed = ({1, 3} : Finset (Fin 4)) := rfl

/-- The forward fixture inserts the target terms in their original order. -/
theorem forward_inserted :
    forward.inserted = [targetPair.term 0, targetPair.term 1] := rfl

/-- The inverse fixture inserts the source terms in their original order. -/
theorem inverse_inserted :
    inverse.inserted = [sourcePair.term 0, sourcePair.term 1] := rfl

/-- The forward certificate retains ambient source slots zero and two, in that order. -/
theorem forward_survivors :
    let q₀ : Fin (4 - forward.removed.card) := ⟨0, by simp⟩
    let q₁ : Fin (4 - forward.removed.card) := ⟨1, by simp⟩
    forward.survivor q₀ = 0 ∧ forward.survivor q₁ = 2 := by
  dsimp only
  let q₀ : Fin (4 - forward.removed.card) := ⟨0, by simp⟩
  let q₁ : Fin (4 - forward.removed.card) := ⟨1, by simp⟩
  change forward.survivor q₀ = 0 ∧ forward.survivor q₁ = 2
  have hmono := forward.survivor_strictMono
    (show q₀ < q₁ by change 0 < 1; omega)
  have hnot₀ := forward.survivor_not_mem q₀
  have hnot₁ := forward.survivor_not_mem q₁
  change forward.survivor q₀ ∉ ({1, 3} : Finset (Fin 4)) at hnot₀
  change forward.survivor q₁ ∉ ({1, 3} : Finset (Fin 4)) at hnot₁
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot₀ hnot₁
  constructor <;> apply Fin.ext
  · change forward.survivor q₀ < forward.survivor q₁ at hmono
    omega
  · change forward.survivor q₀ < forward.survivor q₁ at hmono
    omega

/-- The inverse certificate retains ambient target slots zero and two, in that order. -/
theorem inverse_survivors :
    let q₀ : Fin (4 - inverse.removed.card) := ⟨0, by simp⟩
    let q₁ : Fin (4 - inverse.removed.card) := ⟨1, by simp⟩
    inverse.survivor q₀ = 0 ∧ inverse.survivor q₁ = 2 := by
  dsimp only
  let q₀ : Fin (4 - inverse.removed.card) := ⟨0, by simp⟩
  let q₁ : Fin (4 - inverse.removed.card) := ⟨1, by simp⟩
  change inverse.survivor q₀ = 0 ∧ inverse.survivor q₁ = 2
  have hmono := inverse.survivor_strictMono
    (show q₀ < q₁ by change 0 < 1; omega)
  have hnot₀ := inverse.survivor_not_mem q₀
  have hnot₁ := inverse.survivor_not_mem q₁
  change inverse.survivor q₀ ∉ ({1, 3} : Finset (Fin 4)) at hnot₀
  change inverse.survivor q₁ ∉ ({1, 3} : Finset (Fin 4)) at hnot₁
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot₀ hnot₁
  constructor <;> apply Fin.ext
  · change inverse.survivor q₀ < inverse.survivor q₁ at hmono
    omega
  · change inverse.survivor q₀ < inverse.survivor q₁ at hmono
    omega

/-- The forward output contains the two untouched terms as its survivor prefix. -/
theorem forward_untouched_survivors :
    let q₀ : Fin (4 - forward.removed.card) := ⟨0, by simp⟩
    let q₁ : Fin (4 - forward.removed.card) := ⟨1, by simp⟩
    forward.output.term (forward.survivorSlot q₀) = left ∧
      forward.output.term (forward.survivorSlot q₁) = middle := by
  dsimp only
  let q₀ : Fin (4 - forward.removed.card) := ⟨0, by simp⟩
  let q₁ : Fin (4 - forward.removed.card) := ⟨1, by simp⟩
  have hsurvivors := forward_survivors
  change forward.survivor q₀ = 0 ∧ forward.survivor q₁ = 2 at hsurvivors
  constructor
  · rw [forward.output_survivor_term, hsurvivors.1]
    rfl
  · rw [forward.output_survivor_term, hsurvivors.2]
    rfl

/-- The inverse output contains the two untouched terms as its survivor prefix. -/
theorem inverse_untouched_survivors :
    let q₀ : Fin (4 - inverse.removed.card) := ⟨0, by simp⟩
    let q₁ : Fin (4 - inverse.removed.card) := ⟨1, by simp⟩
    inverse.output.term (inverse.survivorSlot q₀) = left ∧
      inverse.output.term (inverse.survivorSlot q₁) = middle := by
  dsimp only
  let q₀ : Fin (4 - inverse.removed.card) := ⟨0, by simp⟩
  let q₁ : Fin (4 - inverse.removed.card) := ⟨1, by simp⟩
  have hsurvivors := inverse_survivors
  change inverse.survivor q₀ = 0 ∧ inverse.survivor q₁ = 2 at hsurvivors
  constructor
  · rw [inverse.output_survivor_term, hsurvivors.1]
    rfl
  · rw [inverse.output_survivor_term, hsurvivors.2]
    rfl

/-- Both concrete certificates have canonical output rank four. -/
theorem resultRanks : forward.resultRank = 4 ∧ inverse.resultRank = 4 := by decide

/-- Swapping canonical slots one and two interleaves the inserted terms with the survivors. -/
def endpointPermutation : Fin 4 ≃ Fin 4 := Equiv.swap 1 2

/-- The forward canonical output, indexed at its proved rank four. -/
def forwardCanonicalTerm (q : Fin 4) : TriadData ℚ 1 1 1 :=
  forward.output.term (Fin.cast resultRanks.1.symm q)

/-- The inverse canonical output, indexed at its proved rank four. -/
def inverseCanonicalTerm (q : Fin 4) : TriadData ℚ 1 1 1 :=
  inverse.output.term (Fin.cast resultRanks.2.symm q)

/-- The explicit slot swap carries the canonical forward output to the named interleaved target. -/
theorem forward_endpoint_eq :
    ∀ q, forwardCanonicalTerm (endpointPermutation.symm q) = ambientTarget.term q := by
  intro q
  change forward.output.term (Fin.cast resultRanks.1.symm (endpointPermutation.symm q)) =
    ambientTarget.term q
  let q₀ : Fin (4 - forward.removed.card) := ⟨0, by simp⟩
  let q₁ : Fin (4 - forward.removed.card) := ⟨1, by simp⟩
  let j₀ : Fin forward.inserted.length := ⟨0, by simp⟩
  let j₁ : Fin forward.inserted.length := ⟨1, by simp⟩
  have hs := forward_survivors
  change forward.survivor q₀ = 0 ∧ forward.survivor q₁ = 2 at hs
  fin_cases q
  all_goals simp only
  · calc
      _ = forward.output.term (forward.survivorSlot q₀) :=
        congrArg forward.output.term (Fin.ext (by rfl))
      _ = ambientSource.term (forward.survivor q₀) := forward.output_survivor_term q₀
      _ = _ := by rw [hs.1]; rfl
  · calc
      _ = forward.output.term (forward.insertedSlot j₀) :=
        congrArg forward.output.term (Fin.ext (by rfl))
      _ = forward.inserted.get j₀ := forward.output_inserted_term j₀
      _ = _ := rfl
  · calc
      _ = forward.output.term (forward.survivorSlot q₁) :=
        congrArg forward.output.term (Fin.ext (by rfl))
      _ = ambientSource.term (forward.survivor q₁) := forward.output_survivor_term q₁
      _ = _ := by rw [hs.2]; rfl
  · calc
      _ = forward.output.term (forward.insertedSlot j₁) :=
        congrArg forward.output.term (Fin.ext (by rfl))
      _ = forward.inserted.get j₁ := forward.output_inserted_term j₁
      _ = _ := rfl

/-- The explicit slot swap carries the canonical inverse output to the named interleaved source. -/
theorem inverse_endpoint_eq :
    ∀ q, inverseCanonicalTerm (endpointPermutation.symm q) = ambientSource.term q := by
  intro q
  change inverse.output.term (Fin.cast resultRanks.2.symm (endpointPermutation.symm q)) =
    ambientSource.term q
  let q₀ : Fin (4 - inverse.removed.card) := ⟨0, by simp⟩
  let q₁ : Fin (4 - inverse.removed.card) := ⟨1, by simp⟩
  let j₀ : Fin inverse.inserted.length := ⟨0, by simp⟩
  let j₁ : Fin inverse.inserted.length := ⟨1, by simp⟩
  have hs := inverse_survivors
  change inverse.survivor q₀ = 0 ∧ inverse.survivor q₁ = 2 at hs
  fin_cases q
  all_goals simp only
  · calc
      _ = inverse.output.term (inverse.survivorSlot q₀) :=
        congrArg inverse.output.term (Fin.ext (by rfl))
      _ = ambientTarget.term (inverse.survivor q₀) := inverse.output_survivor_term q₀
      _ = _ := by rw [hs.1]; rfl
  · calc
      _ = inverse.output.term (inverse.insertedSlot j₀) :=
        congrArg inverse.output.term (Fin.ext (by rfl))
      _ = inverse.inserted.get j₀ := inverse.output_inserted_term j₀
      _ = _ := rfl
  · calc
      _ = inverse.output.term (inverse.survivorSlot q₁) :=
        congrArg inverse.output.term (Fin.ext (by rfl))
      _ = ambientTarget.term (inverse.survivor q₁) := inverse.output_survivor_term q₁
      _ = _ := by rw [hs.2]; rfl
  · calc
      _ = inverse.output.term (inverse.insertedSlot j₁) :=
        congrArg inverse.output.term (Fin.ext (by rfl))
      _ = inverse.inserted.get j₁ := inverse.output_inserted_term j₁
      _ = _ := rfl

/-- The concrete forward and inverse certificates both satisfy their exact selected-versus-
inserted local tensor equalities. -/
theorem forward_inverse_local_equalities :
    Replacement.selectedTensor ambientSource {1, 3} =
        Replacement.insertedTensor [targetPair.term 0, targetPair.term 1] ∧
      Replacement.selectedTensor ambientTarget {1, 3} =
        Replacement.insertedTensor [sourcePair.term 0, sourcePair.term 1] :=
  ⟨forward.local_eq, inverse.local_eq⟩

/-- Both nonadjacent ambient replacements preserve the represented full tensor. -/
theorem forward_inverse_sumTensor_eq :
    forward.output.sumTensor = ambientSource.sumTensor ∧
      inverse.output.sumTensor = ambientTarget.sumTensor :=
  ⟨forward.sumTensor_eq, inverse.sumTensor_eq⟩

end NonadjacentAmbientCertificate

/-! Executable and ground-truth checks. -/

example : ∃ (S R : Scheme (ZMod 2) 1 2 2 2),
    Nonempty (ProjectiveOrdinaryTwoTermFlip S R) := by
  let u : Fin 1 → ZMod 2 := fun _ => 1
  let v₀ : Fin 2 → ZMod 2 := fun j => if j = 0 then 1 else 0
  let v₁ : Fin 2 → ZMod 2 := fun j => if j = 1 then 1 else 0
  let w₀ : Fin 2 → ZMod 2 := fun l => if l = 0 then 1 else 0
  let w₁ : Fin 2 → ZMod 2 := fun l => if l = 1 then 1 else 0
  let S := pairScheme (u, v₀, w₀) (u, v₁, w₁)
  let R := flipPair S .first 1
  have hrep : RepeatedNonzeroFactor S .first := by
    refine ⟨?_, rfl⟩
    intro hzero
    have hentry := congrFun hzero 0
    norm_num [S, pairScheme, u] at hentry
  let hordinary : NontrivialOrdinaryTwoTermFlip S R := by
    refine
      { position := .first
        coefficient := 1
        coefficient_ne_zero := one_ne_zero
        target_eq := rfl
        tensor_eq := sumTensor_flipPair S .first 1 hrep
        source_term_ne_zero := ?_
        target_term_ne_zero := ?_
        source_ne_target := ?_ }
    · intro s hzero
      fin_cases s
      · have hentry := congrFun (congrFun (congrFun hzero 0) 0) 0
        norm_num [S, pairScheme, TriadData.eval, triad, u, v₀, w₀] at hentry
      · have hentry := congrFun (congrFun (congrFun hzero 0) 1) 1
        norm_num [S, pairScheme, TriadData.eval, triad, u, v₁, w₁] at hentry
    · intro s hzero
      fin_cases s
      · have hentry := congrFun (congrFun (congrFun hzero 0) 0) 0
        norm_num [R, S, flipPair, pairScheme, TriadData.eval, triad, u, v₀, v₁,
          w₀, w₁] at hentry
      · have hentry := congrFun (congrFun (congrFun hzero 0) 1) 1
        norm_num [R, S, flipPair, pairScheme, TriadData.eval, triad, u, v₀, v₁,
          w₀, w₁] at hentry
    · intro heq
      have hentry := congrArg (fun X => (X.term 0).2.1 1) heq
      norm_num [R, S, flipPair, pairScheme, u, v₀, v₁] at hentry
  let hinverse : NontrivialOrdinaryTwoTermFlip R S := hordinary.symm
  have hindex : hordinary.position ∈ repeatedFactorIndexF2 S :=
    ordinaryTwoTermFlip_position_mem_index_f2 hordinary
  exact ⟨S, R, ⟨
    { sourceRefactor := S
      targetRefactor := R
      source_projective := ProjectiveRefactorization.refl S
      target_projective := ProjectiveRefactorization.refl R
      ordinary := hordinary }⟩⟩

example :
    let t : TriadData (ZMod 2) 1 1 1 :=
      ((fun _ => 1), (fun _ => 1), (fun _ => 1))
    (pairScheme t t).term 0 = t := by
  rfl

example :
    let t : TriadData (ZMod 2) 1 1 1 :=
      ((fun _ => 1), (fun _ => 1), (fun _ => 1))
    repeatedFactorIndexF2 (pairScheme t t) =
      [.first, .second, .third] := by decide

example :
    let u : Fin 1 → ℚ := fun _ => 1
    let x : Fin 2 → Fin 1 → ℚ := fun _ => u
    SpansOneDimensional (k := ℚ) x := by
  dsimp only
  refine ⟨fun _ => 1, ?_, ?_, ⟨0, ?_⟩⟩
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  · intro s
    exact ⟨1, by simp⟩
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry

example :
    let u : Fin 1 → ℚ := fun _ => 1
    let v₀ : Fin 1 → ℚ := fun _ => 2
    let v₁ : Fin 1 → ℚ := fun _ => 3
    let w₀ : Fin 1 → ℚ := fun _ => 5
    let w₁ : Fin 1 → ℚ := fun _ => 7
    (firstFlipCertificate u v₀ v₁ w₀ w₁ 2).output.sumTensor =
      (pairScheme (u, v₀, w₀) (u, v₁, w₁)).sumTensor := by
  apply firstFlip_output_sumTensor

example :
    let u : Fin 1 → ZMod 11 := fun _ => 1
    let v₀ : Fin 1 → ZMod 11 := fun _ => 2
    let v₁ : Fin 1 → ZMod 11 := fun _ => 3
    let w₀ : Fin 1 → ZMod 11 := fun _ => 5
    let w₁ : Fin 1 → ZMod 11 := fun _ => 7
    flipFirstPair u v₀ v₁ w₀ w₁ 4 =
      [(u, (fun _ => 3), w₀), (u, v₁, (fun _ => 9))] := by decide

example :
    let u₀ : Fin 1 → ZMod 11 := fun _ => 1
    let u₁ : Fin 1 → ZMod 11 := fun _ => 2
    let v : Fin 1 → ZMod 11 := fun _ => 3
    let w₀ : Fin 1 → ZMod 11 := fun _ => 5
    let w₁ : Fin 1 → ZMod 11 := fun _ => 7
    flipSecondPair u₀ u₁ v w₀ w₁ 4 =
      [((fun _ => 9), v, w₀), (u₁, v, (fun _ => 9))] := by decide

example :
    let u₀ : Fin 1 → ZMod 11 := fun _ => 1
    let u₁ : Fin 1 → ZMod 11 := fun _ => 2
    let v₀ : Fin 1 → ZMod 11 := fun _ => 2
    let v₁ : Fin 1 → ZMod 11 := fun _ => 3
    let w : Fin 1 → ZMod 11 := fun _ => 5
    flipThirdPair u₀ u₁ v₀ v₁ w 4 =
      [((fun _ => 9), v₀, w), (u₁, (fun _ => 6), w)] := by decide

example :
    factorAt .second
      ((fun _ : Fin 1 => (1 : ZMod 2)),
       (fun _ : Fin 1 => (0 : ZMod 2)),
       (fun _ : Fin 1 => (1 : ZMod 2))) 0 = 0 := by
  rfl

example :
    let t : TriadData (ZMod 2) 1 1 1 :=
      ((fun _ => 1), (fun _ => 1), (fun _ => 1))
    RepeatedNonzeroFactor (pairScheme t t) .third := by
  dsimp only
  constructor
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num [pairScheme] at hentry
  · rfl

example :
    let S : Scheme (ZMod 11) 1 1 1 2 :=
      pairScheme ((fun _ => 1), (fun _ => 2), (fun _ => 5))
        ((fun _ => 1), (fun _ => 3), (fun _ => 7))
    ((flipPair S .first 4).term 0).2.1 0 = 3 := by decide

example :
    let x : Fin 2 → Fin 1 → ℚ := fun _ _ => 1
    let y : Fin 2 → Fin 1 → ℚ := fun _ _ => 1
    let z : Fin 2 → Fin 1 → ℚ := fun _ _ => 1
    RankLE (fun i j l => ∑ s, x s i * y s j * z s l) 1 := by
  dsimp only
  let x : Fin 2 → Fin 1 → ℚ := fun _ _ => 1
  let y : Fin 2 → Fin 1 → ℚ := fun _ _ => 1
  let z : Fin 2 → Fin 1 → ℚ := fun _ _ => 1
  have hx : SpansOneDimensional (k := ℚ) x := by
    refine ⟨fun _ => 1, ?_, ?_, ⟨0, ?_⟩⟩
    · intro hzero
      have hentry := congrFun hzero 0
      norm_num at hentry
    · intro s
      exact ⟨1, by simp [x]⟩
    · intro hzero
      have hentry := congrFun hzero 0
      norm_num [x] at hentry
  have hy : ¬ LinearIndependent ℚ y := by
    intro hli
    have hneq := (linearIndependent_fin2.mp hli).2 1
    exact hneq (by simp [y])
  simpa [x, y, z] using
    (rankLE_sum_of_spansOneDimensional_of_not_linearIndependent
      (k := ℚ) (r := 2) (by decide) x y z hx hy)

#check @selectedTensor_pairScheme_univ
#check @selectedTensor_pairSlots
#check @sumTensor_two
#check @insertedTensor_pair
#check @firstFlipCertificate
#check @secondFlipCertificate
#check @thirdFlipCertificate
#check @inverseFirstFlipCertificate
#check @inverseSecondFlipCertificate
#check @inverseThirdFlipCertificate
#check @firstFlip_output_sumTensor
#check @secondFlip_output_sumTensor
#check @thirdFlip_output_sumTensor
#check @inverseFirstFlip_output_sumTensor
#check @inverseSecondFlip_output_sumTensor
#check @inverseThirdFlip_output_sumTensor
#check @eval_refactor
#check @ProjectiveRefactorization.sameTensors
#check @SameTensors.sumTensor_eq
#check @TriadData.factors_ne_zero_of_eval_ne_zero
#check @sumTensor_flipPair
#check @repeatedNonzeroFactor_of_sumTensor_flipPair_eq
#check @NontrivialOrdinaryTwoTermFlip.repeated
#check @flipPair_neg
#check @NontrivialOrdinaryTwoTermFlip.symm
#check @ProjectiveOrdinaryTwoTermFlip.sumTensor_eq
#check @ProjectiveOrdinaryTwoTermFlip.symm
#check @ProjectiveOrdinaryTwoTermFlip.forwardCertificateAt
#check @ProjectiveOrdinaryTwoTermFlip.inverseCertificateAt
#check @ProjectiveOrdinaryTwoTermFlip.forwardCertificateAt_removed
#check @ProjectiveOrdinaryTwoTermFlip.forwardCertificateAt_inserted
#check @ProjectiveOrdinaryTwoTermFlip.inverseCertificateAt_removed
#check @ProjectiveOrdinaryTwoTermFlip.inverseCertificateAt_inserted
#check @ProjectiveOrdinaryTwoTermFlip.forwardCertificateAt_local_eq
#check @ProjectiveOrdinaryTwoTermFlip.inverseCertificateAt_local_eq
#check @ProjectiveOrdinaryTwoTermFlip.forwardCertificateAt_sumTensor_eq
#check @ProjectiveOrdinaryTwoTermFlip.inverseCertificateAt_sumTensor_eq
#check @rankLE_sum_scalar_shared_first_of_not_linearIndependent
#check @rankLE_sum_of_spansOneDimensional_of_not_linearIndependent
#check @rankLE_sum_of_oneDimensional_factor_of_dependent_other
#check @ordinaryTwoTermFlip_has_repeated_projective_factor_f2
#check @mem_repeatedFactorIndexF2_iff
#check @ordinaryTwoTermFlip_position_mem_index_f2
#check @ProjectiveRefactorization.eq_f2
#check @projectiveOrdinaryTwoTermFlip_has_repeated_projective_factor_f2
#check @projectiveOrdinaryTwoTermFlip_position_mem_index_f2
#check NonadjacentAmbientCertificate.forward
#check NonadjacentAmbientCertificate.inverse
#check NonadjacentAmbientCertificate.forward_removed
#check NonadjacentAmbientCertificate.inverse_removed
#check NonadjacentAmbientCertificate.forward_inserted
#check NonadjacentAmbientCertificate.inverse_inserted
#check NonadjacentAmbientCertificate.forward_survivors
#check NonadjacentAmbientCertificate.inverse_survivors
#check NonadjacentAmbientCertificate.forward_untouched_survivors
#check NonadjacentAmbientCertificate.inverse_untouched_survivors
#check NonadjacentAmbientCertificate.resultRanks
#check NonadjacentAmbientCertificate.endpointPermutation
#check NonadjacentAmbientCertificate.forwardCanonicalTerm
#check NonadjacentAmbientCertificate.inverseCanonicalTerm
#check NonadjacentAmbientCertificate.forward_endpoint_eq
#check NonadjacentAmbientCertificate.inverse_endpoint_eq
#check NonadjacentAmbientCertificate.forward_inverse_local_equalities
#check NonadjacentAmbientCertificate.forward_inverse_sumTensor_eq

#print axioms selectedTensor_pairScheme_univ
#print axioms selectedTensor_pairSlots
#print axioms sumTensor_two
#print axioms insertedTensor_pair
#print axioms firstFlipCertificate
#print axioms secondFlipCertificate
#print axioms thirdFlipCertificate
#print axioms inverseFirstFlipCertificate
#print axioms inverseSecondFlipCertificate
#print axioms inverseThirdFlipCertificate
#print axioms firstFlip_output_sumTensor
#print axioms secondFlip_output_sumTensor
#print axioms thirdFlip_output_sumTensor
#print axioms inverseFirstFlip_output_sumTensor
#print axioms inverseSecondFlip_output_sumTensor
#print axioms inverseThirdFlip_output_sumTensor
#print axioms eval_refactor
#print axioms ProjectiveRefactorization.sameTensors
#print axioms SameTensors.sumTensor_eq
#print axioms TriadData.factors_ne_zero_of_eval_ne_zero
#print axioms sumTensor_flipPair
#print axioms repeatedNonzeroFactor_of_sumTensor_flipPair_eq
#print axioms NontrivialOrdinaryTwoTermFlip.repeated
#print axioms flipPair_neg
#print axioms NontrivialOrdinaryTwoTermFlip.symm
#print axioms ProjectiveOrdinaryTwoTermFlip.sumTensor_eq
#print axioms ProjectiveOrdinaryTwoTermFlip.symm
#print axioms ProjectiveOrdinaryTwoTermFlip.forwardCertificateAt
#print axioms ProjectiveOrdinaryTwoTermFlip.inverseCertificateAt
#print axioms ProjectiveOrdinaryTwoTermFlip.forwardCertificateAt_removed
#print axioms ProjectiveOrdinaryTwoTermFlip.forwardCertificateAt_inserted
#print axioms ProjectiveOrdinaryTwoTermFlip.inverseCertificateAt_removed
#print axioms ProjectiveOrdinaryTwoTermFlip.inverseCertificateAt_inserted
#print axioms ProjectiveOrdinaryTwoTermFlip.forwardCertificateAt_local_eq
#print axioms ProjectiveOrdinaryTwoTermFlip.inverseCertificateAt_local_eq
#print axioms ProjectiveOrdinaryTwoTermFlip.forwardCertificateAt_sumTensor_eq
#print axioms ProjectiveOrdinaryTwoTermFlip.inverseCertificateAt_sumTensor_eq
#print axioms rankLE_sum_of_spansOneDimensional_of_not_linearIndependent
#print axioms rankLE_sum_of_oneDimensional_factor_of_dependent_other
#print axioms rankLE_sum_scalar_shared_first_of_not_linearIndependent
#print axioms projectivelyEqual_iff_eq_f2
#print axioms mem_repeatedFactorIndexF2_iff
#print axioms ordinaryTwoTermFlip_has_repeated_projective_factor_f2
#print axioms ordinaryTwoTermFlip_position_mem_index_f2
#print axioms ProjectiveRefactorization.eq_f2
#print axioms projectiveOrdinaryTwoTermFlip_has_repeated_projective_factor_f2
#print axioms projectiveOrdinaryTwoTermFlip_position_mem_index_f2
#print axioms NonadjacentAmbientCertificate.forward
#print axioms NonadjacentAmbientCertificate.inverse
#print axioms NonadjacentAmbientCertificate.forward_survivors
#print axioms NonadjacentAmbientCertificate.inverse_survivors
#print axioms NonadjacentAmbientCertificate.forward_untouched_survivors
#print axioms NonadjacentAmbientCertificate.inverse_untouched_survivors
#print axioms NonadjacentAmbientCertificate.resultRanks
#print axioms NonadjacentAmbientCertificate.forward_endpoint_eq
#print axioms NonadjacentAmbientCertificate.inverse_endpoint_eq
#print axioms NonadjacentAmbientCertificate.forward_inverse_local_equalities
#print axioms NonadjacentAmbientCertificate.forward_inverse_sumTensor_eq

end FlipReduction
end Scheme
end BilinearComplexity
