import BilinearComplexity.FieldFiveCircuitProfile
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

open scoped BigOperators

namespace BilinearComplexity
namespace FieldCircuitContraction

open FieldFiveCircuitProfile

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- A coefficient vector is a linear relation on an indexed vector family. -/
def IsLinearRelation {n : ℕ} (t : Fin n → V) (c : Fin n → k) : Prop :=
  ∑ i, c i • t i = 0

/-- Every family obtained from four vectors by deleting one index is linearly independent. -/
def EveryDeletionIndependent4 (t : Fin 4 → V) : Prop :=
  ∀ d : Fin 4, LinearIndependent k (fun i : {i : Fin 4 // i ≠ d} => t i.1)

/-- A four-family is a minimal circuit when it has a nonzero relation and no nonzero
relation can vanish at one coordinate. -/
def IsMinimalFourCircuit (t : Fin 4 → V) : Prop :=
  (∃ c : Fin 4 → k, c ≠ 0 ∧ IsLinearRelation t c) ∧
    ∀ c : Fin 4 → k, IsLinearRelation t c → (∃ i, c i = 0) → c = 0

/-- Two vectors are nonproportional when neither is a scalar multiple in the displayed
order. For nonzero vectors this is symmetric. -/
def Nonproportional (u v : V) : Prop :=
  ∀ a : k, u ≠ a • v

/-- The two endpoint shapes of the residual signed four-family. -/
inductive FourFamilyShape
  | oneThree
  | twoTwo
  deriving DecidableEq

/-- Canonical coefficients for `q = b₀+b₁+b₂` and `a₀+a₁ = b₀+b₁`. -/
def signedFourCoefficients (shape : FourFamilyShape) : Fin 4 → k :=
  match shape with
  | .oneThree => ![1, -1, -1, -1]
  | .twoTwo => ![1, 1, -1, -1]

/-- A coefficient-correct minimally dependent four-family in canonical endpoint order. -/
structure SignedMinimalFour (k : Type*) (V : Type*) [Field k] [AddCommGroup V] [Module k V] where
  term : Fin 4 → V
  shape : FourFamilyShape
  signed_relation : IsLinearRelation term (signedFourCoefficients (k := k) shape)
  everyDeletionIndependent : EveryDeletionIndependent4 (k := k) term


/-- An explicit coefficient-aware contraction of two slots of a five-family. -/
structure ContractionData (k : Type*) [Field k] (t : Fin 5 → V) [AddCommGroup V] [Module k V] where
  split : Fin 2 ⊕ Fin 3 ≃ Fin 5
  q : V
  leftScale : k
  rightScale : k
  originalCoefficients : Fin 5 → k
  residualCoefficients : Fin 4 → k
  q_eq : q = leftScale • t (split (.inl 0)) + rightScale • t (split (.inl 1))
  original_relation : IsLinearRelation (k := k) t originalCoefficients
  originalCoefficients_ne_zero : originalCoefficients ≠ 0
  match_left : originalCoefficients (split (.inl 0)) =
    residualCoefficients 0 * leftScale
  match_right : originalCoefficients (split (.inl 1)) =
    residualCoefficients 0 * rightScale
  match_rest : ∀ j : Fin 3,
    originalCoefficients (split (.inr j)) = residualCoefficients j.succ

/-- The four-family produced by a contraction: the new vector first, then the three retained
original vectors. -/
def ContractionData.residualFamily {t : Fin 5 → V} (C : ContractionData k t) : Fin 4 → V :=
  Fin.cases C.q (fun j => t (C.split (.inr j)))

/-- Lift coefficients of a residual relation back to the original five slots. -/
def ContractionData.liftCoefficients {t : Fin 5 → V} (C : ContractionData k t)
    (u : Fin 4 → k) : Fin 5 → k :=
  fun i =>
    match C.split.symm i with
    | .inl j => u 0 * ![C.leftScale, C.rightScale] j
    | .inr j => u j.succ

example : signedFourCoefficients (k := ℚ) .oneThree = ![1, -1, -1, -1] := rfl
example : signedFourCoefficients (k := ℚ) .twoTwo = ![1, 1, -1, -1] := rfl
example : Nonproportional (k := ℚ) (1 : ℚ) 0 := by simp [Nonproportional]

example : ∃ C : ContractionData ℚ (fun _ : Fin 5 => (0 : ℚ)),
    C.residualFamily 0 = 0 := by
  let C : ContractionData ℚ (fun _ : Fin 5 => (0 : ℚ)) := {
    split := finSumFinEquiv
    q := 0
    leftScale := 1
    rightScale := 1
    originalCoefficients := fun _ => 1
    residualCoefficients := fun _ => 1
    q_eq := by simp
    original_relation := by simp [IsLinearRelation]
    originalCoefficients_ne_zero := by
      intro hzero
      have := congrFun hzero 0
      simp at this
    match_left := by simp
    match_right := by simp
    match_rest := by intro j; simp }
  exact ⟨C, rfl⟩

/-- The zero-coefficient criterion is equivalent to independence after every deletion. -/
theorem vanishing_relation_iff_everyDeletionIndependent4 (t : Fin 4 → V) :
    (∀ c : Fin 4 → k, IsLinearRelation t c → (∃ i, c i = 0) → c = 0) ↔
      EveryDeletionIndependent4 (k := k) t := by
  classical
  have sum_extend (d : Fin 4) (coeff : {i : Fin 4 // i ≠ d} → k) :
      (∑ i, (if h : i ≠ d then coeff ⟨i, h⟩ else 0) • t i) =
        ∑ i, coeff i • t i := by
    let f : Fin 4 → V := fun i =>
      (if h : i ≠ d then coeff ⟨i, h⟩ else 0) • t i
    calc
      ∑ i, (if h : i ≠ d then coeff ⟨i, h⟩ else 0) • t i =
          (∑ i : {i : Fin 4 // i ≠ d}, f i) +
            ∑ i : {i : Fin 4 // ¬ i ≠ d}, f i := by
              exact (Fintype.sum_subtype_add_sum_subtype
                (fun i : Fin 4 => i ≠ d) f).symm
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
    let extended : Fin 4 → k :=
      fun j => if hj : j ≠ d then coeff ⟨j, hj⟩ else 0
    have hextended : IsLinearRelation t extended := by
      unfold IsLinearRelation
      rw [show (∑ j, extended j • t j) = ∑ j, coeff j • t j by
        simpa only [extended] using sum_extend d coeff]
      exact hcoeff
    have hzero : extended = 0 := h extended hextended ⟨d, by simp [extended]⟩
    have hi := congrFun hzero i.1
    simpa only [extended, dif_pos i.2, Pi.zero_apply] using hi
  · intro h c hc
    rintro ⟨d, hd⟩
    have hcoeffPoint : ∀ i : {i : Fin 4 // i ≠ d}, c i.1 = 0 := by
      apply (Fintype.linearIndependent_iff.mp (h d))
      change (∑ i : {i : Fin 4 // i ≠ d}, c i.1 • t i.1) = 0
      rw [← sum_extend d (fun i => c i.1)]
      have hext : (fun i : Fin 4 => if hi : i ≠ d then c i else 0) = c := by
        funext i
        by_cases hi : i = d
        · subst i
          simp only [ne_eq, not_true_eq_false, ↓reduceDIte, hd]
        · exact dif_pos hi
      change (∑ i, (if hi : i ≠ d then c i else 0) • t i) = 0
      calc
        _ = ∑ i, c i • t i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [congrFun hext i]
        _ = 0 := hc
    funext i
    by_cases hi : i = d
    · subst i
      exact hd
    · exact hcoeffPoint ⟨i, hi⟩

/-- The deletion formulation is an exact checkpoint for four-circuit minimality. -/
theorem minimalFourCircuit_iff (t : Fin 4 → V) :
    IsMinimalFourCircuit (k := k) t ↔
      (∃ c : Fin 4 → k, c ≠ 0 ∧ IsLinearRelation t c) ∧
        EveryDeletionIndependent4 (k := k) t := by
  unfold IsMinimalFourCircuit
  rw [vanishing_relation_iff_everyDeletionIndependent4]


@[simp] theorem ContractionData.residualFamily_zero {t : Fin 5 → V}
    (C : ContractionData k t) : C.residualFamily 0 = C.q := rfl

@[simp] theorem ContractionData.residualFamily_succ {t : Fin 5 → V}
    (C : ContractionData k t) (j : Fin 3) :
    C.residualFamily j.succ = t (C.split (.inr j)) := rfl

@[simp] theorem ContractionData.liftCoefficients_left {t : Fin 5 → V}
    (C : ContractionData k t) (u : Fin 4 → k) (j : Fin 2) :
    C.liftCoefficients u (C.split (.inl j)) =
      u 0 * ![C.leftScale, C.rightScale] j := by
  simp [ContractionData.liftCoefficients]

@[simp] theorem ContractionData.liftCoefficients_rest {t : Fin 5 → V}
    (C : ContractionData k t) (u : Fin 4 → k) (j : Fin 3) :
    C.liftCoefficients u (C.split (.inr j)) = u j.succ := by
  simp [ContractionData.liftCoefficients]

/-- Every proper indexed subfamily of a deletion-independent five-family is independent. -/
theorem everyDeletionIndependent5_linearIndependent_comp (t : Fin 5 → V)
    (h : EveryDeletionIndependent (k := k) t) {ι : Type*} [Fintype ι]
    (f : ι → Fin 5) (hf : Function.Injective f) (hcard : Fintype.card ι < 5) :
    LinearIndependent k (t ∘ f) := by
  let s : Set (Fin 5) := Set.range f
  have hs : s ≠ Set.univ := by
    intro hs
    have hsurj : Function.Surjective f := Set.range_eq_univ.mp hs
    have hle : Fintype.card (Fin 5) ≤ Fintype.card ι :=
      Fintype.card_le_of_surjective f hsurj
    simp only [Fintype.card_fin] at hle
    omega
  have hrestrict := h.linearIndependent_restrict t s hs
  let g : ι → s := fun i => ⟨f i, Set.mem_range_self i⟩
  have hg : Function.Injective g := by
    intro i j hij
    exact hf (congrArg Subtype.val hij)
  exact hrestrict.comp g hg

/-- Every proper indexed subfamily of a deletion-independent four-family is independent. -/
theorem EveryDeletionIndependent4.linearIndependent_comp (t : Fin 4 → V)
    (h : EveryDeletionIndependent4 (k := k) t) {ι : Type*} [Fintype ι]
    (f : ι → Fin 4) (hf : Function.Injective f) (hcard : Fintype.card ι < 4) :
    LinearIndependent k (t ∘ f) := by
  let s : Set (Fin 4) := Set.range f
  have hs : s ≠ Set.univ := by
    intro hs
    have hsurj : Function.Surjective f := Set.range_eq_univ.mp hs
    have hle : Fintype.card (Fin 4) ≤ Fintype.card ι :=
      Fintype.card_le_of_surjective f hsurj
    simp only [Fintype.card_fin] at hle
    omega
  have hex : ∃ d : Fin 4, d ∉ s := by
    by_contra hnone
    push Not at hnone
    exact hs (Set.eq_univ_of_forall hnone)
  obtain ⟨d, hd⟩ := hex
  let g : ι → {i : Fin 4 // i ≠ d} := fun i =>
    ⟨f i, fun hi => hd (hi ▸ Set.mem_range_self i)⟩
  have hg : Function.Injective g := by
    intro i j hij
    exact hf (congrArg Subtype.val hij)
  exact (h d).comp g hg

/-- Deletion independence is preserved by a computable reindexing. -/
theorem EveryDeletionIndependent4.reindex (t : Fin 4 → V)
    (h : EveryDeletionIndependent4 (k := k) t) (e : Fin 4 ≃ Fin 4) :
    EveryDeletionIndependent4 (k := k) (t ∘ e) := by
  intro d
  let f : {i : Fin 4 // i ≠ d} → {i : Fin 4 // i ≠ e d} := fun i =>
    ⟨e i.1, fun hi => i.2 (e.injective hi)⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val hij)
  exact (h (e d)).comp f hf

/-- The coefficient lift converts exactly a residual relation into an original relation. -/
theorem ContractionData.sum_liftCoefficients {t : Fin 5 → V} (C : ContractionData k t)
    (u : Fin 4 → k) :
    ∑ i, C.liftCoefficients u i • t i =
      ∑ i, u i • C.residualFamily i := by
  rw [← C.split.sum_comp (fun i => C.liftCoefficients u i • t i)]
  simp only [Fintype.sum_sum_type, C.liftCoefficients_left,
    C.liftCoefficients_rest]
  rw [show (∑ i : Fin 4, u i • C.residualFamily i) =
    u 0 • C.q + ∑ j : Fin 3, u j.succ • t (C.split (.inr j)) by
      rw [Fin.sum_univ_succ]
      rfl]
  rw [C.q_eq]
  simp only [smul_add, smul_smul]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Minimality forces every coefficient in a displayed nonzero relation to be nonzero. -/
theorem relation_coefficients_ne_zero {t : Fin 5 → V} {c : Fin 5 → k}
    (hminimal : ∀ u : Fin 5 → k, IsLinearRelation t u → (∃ i, u i = 0) → u = 0)
    (hrelation : IsLinearRelation t c) (hc : c ≠ 0) :
    ∀ i, c i ≠ 0 := by
  intro i hi
  exact hc (hminimal c hrelation ⟨i, hi⟩)

/-- The contraction scales are nonzero; this is a consequence of coefficient matching. -/
theorem ContractionData.scales_ne_zero {t : Fin 5 → V} (C : ContractionData k t)
    (hminimal : ∀ u : Fin 5 → k, IsLinearRelation t u → (∃ i, u i = 0) → u = 0) :
    C.leftScale ≠ 0 ∧ C.rightScale ≠ 0 ∧ C.residualCoefficients 0 ≠ 0 := by
  have hc := relation_coefficients_ne_zero hminimal C.original_relation
    C.originalCoefficients_ne_zero
  constructor
  · intro hzero
    exact hc (C.split (.inl 0)) (C.match_left.trans (by simp [hzero]))
  constructor
  · intro hzero
    exact hc (C.split (.inl 1)) (C.match_right.trans (by simp [hzero]))
  · intro hzero
    exact hc (C.split (.inl 0)) (C.match_left.trans (by simp [hzero]))

/-- The actual matched residual coefficients form the residual relation. -/
theorem ContractionData.residual_relation {t : Fin 5 → V} (C : ContractionData k t) :
    IsLinearRelation (k := k) C.residualFamily C.residualCoefficients := by
  unfold IsLinearRelation
  rw [← C.sum_liftCoefficients]
  have hlift : C.liftCoefficients C.residualCoefficients = C.originalCoefficients := by
    funext i
    have hi : i = C.split (C.split.symm i) := (C.split.apply_symm_apply i).symm
    rw [hi]
    obtain j | j := C.split.symm i
    · fin_cases j
      · simpa [ContractionData.liftCoefficients] using C.match_left.symm
      · simpa [ContractionData.liftCoefficients] using C.match_right.symm
    · simpa [ContractionData.liftCoefficients] using (C.match_rest j).symm
  rw [hlift]
  exact C.original_relation

/-- A zero residual coefficient lifts to a zero original coefficient. -/
theorem ContractionData.exists_zero_lift {t : Fin 5 → V} (C : ContractionData k t)
    (u : Fin 4 → k) (hzero : ∃ i, u i = 0) :
    ∃ i, C.liftCoefficients u i = 0 := by
  obtain ⟨i, hi⟩ := hzero
  cases i using Fin.cases with
  | zero => exact ⟨C.split (.inl 0), by simp [hi]⟩
  | succ j => exact ⟨C.split (.inr j), by simp [hi]⟩

/-- If a scale is nonzero, the coefficient lift is injective. -/
theorem ContractionData.liftCoefficients_injective {t : Fin 5 → V}
    (C : ContractionData k t) (hleft : C.leftScale ≠ 0) :
    Function.Injective C.liftCoefficients := by
  intro u v huv
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · have h := congrFun huv (C.split (.inl 0))
    simp only [C.liftCoefficients_left, Matrix.cons_val_zero] at h
    exact (mul_right_cancel₀ hleft h)
  · have h := congrFun huv (C.split (.inr j))
    simpa only [C.liftCoefficients_rest] using h

/-- The residual four-family inherits the zero-coefficient minimality criterion. -/
theorem ContractionData.residual_vanishing_relation {t : Fin 5 → V}
    (C : ContractionData k t)
    (hminimal : ∀ u : Fin 5 → k, IsLinearRelation t u → (∃ i, u i = 0) → u = 0) :
    ∀ u : Fin 4 → k, IsLinearRelation C.residualFamily u →
      (∃ i, u i = 0) → u = 0 := by
  intro u hrelation hzero
  have hliftRelation : IsLinearRelation (k := k) t (C.liftCoefficients u) := by
    unfold IsLinearRelation
    rw [C.sum_liftCoefficients]
    exact hrelation
  have hliftZero := C.exists_zero_lift u hzero
  have hliftEq : C.liftCoefficients u = 0 :=
    hminimal (C.liftCoefficients u) hliftRelation hliftZero
  have hleft := (C.scales_ne_zero hminimal).1
  apply C.liftCoefficients_injective hleft
  calc
    C.liftCoefficients u = 0 := hliftEq
    _ = C.liftCoefficients 0 := by
      funext i
      have hi : i = C.split (C.split.symm i) := (C.split.apply_symm_apply i).symm
      rw [hi]
      obtain j | j := C.split.symm i
      · fin_cases j <;> simp
      · simp

/-- Every vector in a deletion-independent five-family is nonzero. -/
theorem everyDeletionIndependent5_term_ne_zero (t : Fin 5 → V)
    (h : EveryDeletionIndependent (k := k) t) (i : Fin 5) : t i ≠ 0 := by
  let f : Fin 1 → Fin 5 := fun _ => i
  have hf : Function.Injective f := fun _ _ _ => Subsingleton.elim _ _
  have hli : LinearIndependent k (t ∘ f) :=
    everyDeletionIndependent5_linearIndependent_comp t h f hf (by decide)
  simpa only [Function.comp_apply, f] using hli.ne_zero 0

/-- Distinct vectors in a deletion-independent five-family form a linearly independent pair. -/
theorem everyDeletionIndependent5_pair_linearIndependent (t : Fin 5 → V)
    (h : EveryDeletionIndependent (k := k) t) (i j : Fin 5) (hij : i ≠ j) :
    LinearIndependent k ![t i, t j] := by
  let f : Fin 2 → Fin 5 := ![i, j]
  have hf : Function.Injective f := by
    intro p q hpq
    fin_cases p <;> fin_cases q <;> simp_all [f]
  have hli := everyDeletionIndependent5_linearIndependent_comp t h f hf (by decide)
  convert hli using 1
  funext p
  fin_cases p <;> rfl

/-- Three pairwise distinct vectors in a deletion-independent five-family are independent. -/
theorem everyDeletionIndependent5_triple_linearIndependent (t : Fin 5 → V)
    (h : EveryDeletionIndependent (k := k) t) (i j l : Fin 5)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    LinearIndependent k ![t i, t j, t l] := by
  let f : Fin 3 → Fin 5 := ![i, j, l]
  have hf : Function.Injective f := by
    intro p q hpq
    fin_cases p <;> fin_cases q <;> simp_all [f]
  have hli := everyDeletionIndependent5_linearIndependent_comp t h f hf (by decide)
  convert hli using 1
  funext p
  fin_cases p <;> rfl

/-- Every vector in a deletion-independent four-family is nonzero. -/
theorem EveryDeletionIndependent4.term_ne_zero (t : Fin 4 → V)
    (h : EveryDeletionIndependent4 (k := k) t) (i : Fin 4) : t i ≠ 0 := by
  let f : Fin 1 → Fin 4 := fun _ => i
  have hf : Function.Injective f := fun _ _ _ => Subsingleton.elim _ _
  have hli : LinearIndependent k (t ∘ f) := h.linearIndependent_comp t f hf (by decide)
  simpa only [Function.comp_apply, f] using hli.ne_zero 0

/-- Distinct vectors in a deletion-independent four-family form a linearly independent pair. -/
theorem EveryDeletionIndependent4.pair_linearIndependent (t : Fin 4 → V)
    (h : EveryDeletionIndependent4 (k := k) t) (i j : Fin 4) (hij : i ≠ j) :
    LinearIndependent k ![t i, t j] := by
  let f : Fin 2 → Fin 4 := ![i, j]
  have hf : Function.Injective f := by
    intro p q hpq
    fin_cases p <;> fin_cases q <;> simp_all [f]
  have hli := h.linearIndependent_comp t f hf (by decide)
  convert hli using 1
  funext p
  fin_cases p <;> rfl

/-- Distinct members of a deletion-independent four-family are nonproportional. -/
theorem EveryDeletionIndependent4.nonproportional (t : Fin 4 → V)
    (h : EveryDeletionIndependent4 (k := k) t) (i j : Fin 4) (hij : i ≠ j) :
    Nonproportional (k := k) (t i) (t j) := by
  intro a ha
  have hpair := h.pair_linearIndependent t j i (Ne.symm hij)
  have hji : ∀ b : k, b • t j ≠ t i :=
    (LinearIndependent.pair_iff' (h.term_ne_zero t j)).mp hpair
  exact hji a ha.symm

/-- A deletion-independent four-family is injectively indexed. -/
theorem EveryDeletionIndependent4.injective (t : Fin 4 → V)
    (h : EveryDeletionIndependent4 (k := k) t) : Function.Injective t := by
  intro i j hij
  by_contra hne
  exact h.nonproportional t i j hne 1 (by simpa only [one_smul] using hij)

/-- Every term in a signed minimal four-family is nonzero. -/
theorem SignedMinimalFour.term_ne_zero (S : SignedMinimalFour k V) (i : Fin 4) :
    S.term i ≠ 0 := S.everyDeletionIndependent.term_ne_zero S.term i

/-- Every distinct pair in a signed minimal four-family is linearly independent. -/
theorem SignedMinimalFour.pair_linearIndependent (S : SignedMinimalFour k V)
    (i j : Fin 4) (hij : i ≠ j) : LinearIndependent k ![S.term i, S.term j] :=
  S.everyDeletionIndependent.pair_linearIndependent S.term i j hij

/-- Every distinct pair in a signed minimal four-family is nonproportional. -/
theorem SignedMinimalFour.nonproportional (S : SignedMinimalFour k V)
    (i j : Fin 4) (hij : i ≠ j) : Nonproportional (k := k) (S.term i) (S.term j) :=
  S.everyDeletionIndependent.nonproportional S.term i j hij

/-- A signed minimal four-family has no repeated terms. -/
theorem SignedMinimalFour.injective (S : SignedMinimalFour k V) :
    Function.Injective S.term := S.everyDeletionIndependent.injective S.term


/-- The five-product minimality criterion in generic linear-relation form. -/
theorem minimalFive_vanishingRelation {a b c : ℕ}
    (x : Fin 5 → Fin a → k) (y : Fin 5 → Fin b → k)
    (z : Fin 5 → Fin c → k) (hminimal : IsMinimalFiveProductCircuit x y z) :
    ∀ u : Fin 5 → k, IsLinearRelation (productFamily x y z) u →
      (∃ i, u i = 0) → u = 0 := by
  intro u hu hzero
  apply hminimal.2 u
  · exact hu
  · exact hzero

/-- The original five-product minimality hypothesis exposes deletion independence. -/
theorem minimalFive_deletions {a b c : ℕ} (x : Fin 5 → Fin a → k)
    (y : Fin 5 → Fin b → k) (z : Fin 5 → Fin c → k)
    (hminimal : IsMinimalFiveProductCircuit x y z) :
    EveryDeletionIndependent (k := k) (productFamily x y z) :=
  (minimalFiveProductCircuit_iff x y z).mp hminimal |>.2

/-- Any proper subfamily of a minimal five-product circuit is linearly independent. -/
theorem minimalFive_properSubfamily {a b c : ℕ}
    (x : Fin 5 → Fin a → k) (y : Fin 5 → Fin b → k)
    (z : Fin 5 → Fin c → k) (hminimal : IsMinimalFiveProductCircuit x y z)
    (s : Set (Fin 5)) (hs : s ≠ Set.univ) :
    LinearIndependent k (fun i : s => productFamily x y z i.1) :=
  (minimalFive_deletions x y z hminimal).linearIndependent_restrict
    (productFamily x y z) s hs

/-- Any two distinct tensors in a minimal five-product circuit are linearly independent. -/
theorem minimalFive_pair_linearIndependent {a b c : ℕ}
    (x : Fin 5 → Fin a → k) (y : Fin 5 → Fin b → k)
    (z : Fin 5 → Fin c → k) (hminimal : IsMinimalFiveProductCircuit x y z)
    (i j : Fin 5) (hij : i ≠ j) :
    LinearIndependent k ![productFamily x y z i, productFamily x y z j] :=
  everyDeletionIndependent5_pair_linearIndependent _
    (minimalFive_deletions x y z hminimal) i j hij

/-- Every tensor in a minimal five-product circuit is nonzero. -/
theorem minimalFive_term_ne_zero {a b c : ℕ}
    (x : Fin 5 → Fin a → k) (y : Fin 5 → Fin b → k)
    (z : Fin 5 → Fin c → k) (hminimal : IsMinimalFiveProductCircuit x y z)
    (i : Fin 5) : productFamily x y z i ≠ 0 :=
  everyDeletionIndependent5_term_ne_zero _ (minimalFive_deletions x y z hminimal) i

/-- Distinct tensors in a minimal five-product circuit are nonproportional. -/
theorem minimalFive_not_proportional {a b c : ℕ}
    (x : Fin 5 → Fin a → k) (y : Fin 5 → Fin b → k)
    (z : Fin 5 → Fin c → k) (hminimal : IsMinimalFiveProductCircuit x y z)
    (i j : Fin 5) (hij : i ≠ j) :
    Nonproportional (k := k) (productFamily x y z i) (productFamily x y z j) := by
  intro scalar heq
  have hpair := minimalFive_pair_linearIndependent x y z hminimal j i hij.symm
  have hji : ∀ r : k, r • productFamily x y z j ≠ productFamily x y z i :=
    (LinearIndependent.pair_iff' (minimalFive_term_ne_zero x y z hminimal j)).mp hpair
  exact hji scalar heq.symm

/-- The new vector in a coefficient-correct contraction is nonzero. -/
theorem ContractionData.q_ne_zero {t : Fin 5 → V} (C : ContractionData k t)
    (hminimal : ∀ u : Fin 5 → k, IsLinearRelation t u → (∃ i, u i = 0) → u = 0) :
    C.q ≠ 0 := by
  have hdel : EveryDeletionIndependent (k := k) t :=
    (vanishing_relation_iff_everyDeletionIndependent t).mp (by
      simpa only [IsLinearRelation] using hminimal)
  have hpairs : C.split (.inl (0 : Fin 2)) ≠ C.split (.inl (1 : Fin 2)) := by
    intro heq
    have := C.split.injective heq
    simp at this
  have hpair := everyDeletionIndependent5_pair_linearIndependent t hdel
    (C.split (.inl 0)) (C.split (.inl 1)) hpairs
  intro hq
  have hrelation :
      C.leftScale • t (C.split (.inl 0)) +
        C.rightScale • t (C.split (.inl 1)) = 0 := by
    rw [← C.q_eq, hq]
  have hright := (LinearIndependent.pair_iff.mp hpair _ _ hrelation).2
  exact (C.scales_ne_zero hminimal).2.1 hright

/-- The contraction vector is not proportional to any of the five original vectors. -/
theorem ContractionData.q_not_proportional {t : Fin 5 → V} (C : ContractionData k t)
    (hminimal : ∀ u : Fin 5 → k, IsLinearRelation t u → (∃ i, u i = 0) → u = 0)
    (i : Fin 5) : Nonproportional (k := k) C.q (t i) := by
  have hdel : EveryDeletionIndependent (k := k) t :=
    (vanishing_relation_iff_everyDeletionIndependent t).mp (by
      simpa only [IsLinearRelation] using hminimal)
  let left := C.split (.inl (0 : Fin 2))
  let right := C.split (.inl (1 : Fin 2))
  have hlr : left ≠ right := by
    intro heq
    have := C.split.injective heq
    simp at this
  have hpair := everyDeletionIndependent5_pair_linearIndependent t hdel left right hlr
  intro scalar hq
  by_cases hil : i = left
  · subst i
    have hrelation :
        (C.leftScale - scalar) • t left + C.rightScale • t right = 0 := by
      calc
        _ = (C.leftScale • t left + C.rightScale • t right) - scalar • t left := by
          module
        _ = C.q - scalar • t left := by rw [C.q_eq]
        _ = 0 := sub_eq_zero.mpr hq
    have hright := (LinearIndependent.pair_iff.mp hpair _ _ hrelation).2
    exact (C.scales_ne_zero hminimal).2.1 hright
  by_cases hir : i = right
  · subst i
    have hrelation :
        C.leftScale • t left + (C.rightScale - scalar) • t right = 0 := by
      calc
        _ = (C.leftScale • t left + C.rightScale • t right) - scalar • t right := by
          module
        _ = C.q - scalar • t right := by rw [C.q_eq]
        _ = 0 := sub_eq_zero.mpr hq
    have hleft := (LinearIndependent.pair_iff.mp hpair _ _ hrelation).1
    exact (C.scales_ne_zero hminimal).1 hleft
  · have htriple := everyDeletionIndependent5_triple_linearIndependent t hdel
      left right i hlr (Ne.symm hil) (Ne.symm hir)
    have hrelation :
        C.leftScale • t left + C.rightScale • t right + (-scalar) • t i = 0 := by
      calc
        _ = (C.leftScale • t left + C.rightScale • t right) - scalar • t i := by
          module
        _ = C.q - scalar • t i := by rw [C.q_eq]
        _ = 0 := sub_eq_zero.mpr hq
    have hsum :
        ∑ j, ![C.leftScale, C.rightScale, -scalar] j • ![t left, t right, t i] j = 0 := by
      simpa [Fin.sum_univ_succ, Fin.sum_univ_two, add_assoc] using hrelation
    have hleft := Fintype.linearIndependent_iff.mp htriple
      ![C.leftScale, C.rightScale, -scalar] hsum 0
    exact (C.scales_ne_zero hminimal).1 hleft

/-- In particular, the contraction vector is unequal to every original endpoint vector. -/
theorem ContractionData.q_ne_original {t : Fin 5 → V} (C : ContractionData k t)
    (hminimal : ∀ u : Fin 5 → k, IsLinearRelation t u → (∃ i, u i = 0) → u = 0)
    (i : Fin 5) : C.q ≠ t i := by
  have h := C.q_not_proportional hminimal i 1
  simpa only [one_smul] using h

/-- The residual family produced by a coefficient-correct contraction is deletion-independent. -/
theorem ContractionData.residual_everyDeletionIndependent {t : Fin 5 → V}
    (C : ContractionData k t)
    (hminimal : ∀ u : Fin 5 → k, IsLinearRelation t u → (∃ i, u i = 0) → u = 0) :
    EveryDeletionIndependent4 (k := k) C.residualFamily :=
  (vanishing_relation_iff_everyDeletionIndependent4 C.residualFamily).mp
    (C.residual_vanishing_relation hminimal)

/-- Every residual vector is nonzero, as a consequence rather than an adapter assumption. -/
theorem ContractionData.residual_term_ne_zero {t : Fin 5 → V}
    (C : ContractionData k t)
    (hminimal : ∀ u : Fin 5 → k, IsLinearRelation t u → (∃ i, u i = 0) → u = 0)
    (i : Fin 4) : C.residualFamily i ≠ 0 :=
  (C.residual_everyDeletionIndependent hminimal).term_ne_zero C.residualFamily i

/-- Distinct residual vectors form a linearly independent pair. -/
theorem ContractionData.residual_pair_linearIndependent {t : Fin 5 → V}
    (C : ContractionData k t)
    (hminimal : ∀ u : Fin 5 → k, IsLinearRelation t u → (∃ i, u i = 0) → u = 0)
    (i j : Fin 4) (hij : i ≠ j) :
    LinearIndependent k ![C.residualFamily i, C.residualFamily j] :=
  (C.residual_everyDeletionIndependent hminimal).pair_linearIndependent
    C.residualFamily i j hij

/-- Distinct residual vectors are nonproportional. -/
theorem ContractionData.residual_nonproportional {t : Fin 5 → V}
    (C : ContractionData k t)
    (hminimal : ∀ u : Fin 5 → k, IsLinearRelation t u → (∃ i, u i = 0) → u = 0)
    (i j : Fin 4) (hij : i ≠ j) :
    Nonproportional (k := k) (C.residualFamily i) (C.residualFamily j) :=
  (C.residual_everyDeletionIndependent hminimal).nonproportional C.residualFamily i j hij

/-- The residual family has no semantic collisions. -/
theorem ContractionData.residual_injective {t : Fin 5 → V}
    (C : ContractionData k t)
    (hminimal : ∀ u : Fin 5 → k, IsLinearRelation t u → (∃ i, u i = 0) → u = 0) :
    Function.Injective C.residualFamily :=
  (C.residual_everyDeletionIndependent hminimal).injective C.residualFamily

/-- The residual family is a genuine minimal four-circuit, with its actual matched
coefficient relation. -/
theorem ContractionData.residual_isMinimalFourCircuit {t : Fin 5 → V}
    (C : ContractionData k t)
    (hminimal : ∀ u : Fin 5 → k, IsLinearRelation t u → (∃ i, u i = 0) → u = 0) :
    IsMinimalFourCircuit (k := k) C.residualFamily := by
  rw [minimalFourCircuit_iff]
  refine ⟨⟨C.residualCoefficients, ?_, C.residual_relation⟩,
    C.residual_everyDeletionIndependent hminimal⟩
  intro hzero
  exact (C.scales_ne_zero hminimal).2.2 (congrFun hzero 0)

/-- A canonical signed residual can be obtained after any explicit coefficient-preserving
reindexing. This supports both `1/3` and `2/2` endpoint orders. -/
def ContractionData.signedMinimalFour {t : Fin 5 → V} (C : ContractionData k t)
    (hminimal : ∀ u : Fin 5 → k, IsLinearRelation t u → (∃ i, u i = 0) → u = 0)
    (reindex : Fin 4 ≃ Fin 4) (shape : FourFamilyShape)
    (hcoeff : ∀ i : Fin 4,
      C.residualCoefficients (reindex i) = signedFourCoefficients (k := k) shape i) :
    SignedMinimalFour k V where
  term := C.residualFamily ∘ reindex
  shape := shape
  signed_relation := by
    unfold IsLinearRelation
    simp_rw [← hcoeff]
    change (∑ i, C.residualCoefficients (reindex i) •
      C.residualFamily (reindex i)) = 0
    calc
      _ = ∑ i, C.residualCoefficients i • C.residualFamily i :=
        reindex.sum_comp (fun i => C.residualCoefficients i • C.residualFamily i)
      _ = 0 := C.residual_relation
  everyDeletionIndependent :=
    (C.residual_everyDeletionIndependent hminimal).reindex C.residualFamily reindex

/-- All semantic consequences of a coefficient-correct contraction, derived from five-circuit
minimality rather than supplied by an adapter. -/
structure ContractionResult {t : Fin 5 → V} (C : ContractionData k t) where
  q_ne_zero : C.q ≠ 0
  q_not_proportional : ∀ i : Fin 5, Nonproportional (k := k) C.q (t i)
  q_ne_original : ∀ i : Fin 5, C.q ≠ t i
  residual_relation : IsLinearRelation C.residualFamily C.residualCoefficients
  residual_minimal : IsMinimalFourCircuit (k := k) C.residualFamily
  residual_deletions : EveryDeletionIndependent4 (k := k) C.residualFamily
  residual_term_ne_zero : ∀ i : Fin 4, C.residualFamily i ≠ 0
  residual_nonproportional : ∀ i j : Fin 4, i ≠ j →
    Nonproportional (k := k) (C.residualFamily i) (C.residualFamily j)
  residual_injective : Function.Injective C.residualFamily

/-- Package every derived contraction invariant for downstream adapters. -/
theorem ContractionData.result {t : Fin 5 → V} (C : ContractionData k t)
    (hminimal : ∀ u : Fin 5 → k, IsLinearRelation t u → (∃ i, u i = 0) → u = 0) :
    ContractionResult C where
  q_ne_zero := C.q_ne_zero hminimal
  q_not_proportional := C.q_not_proportional hminimal
  q_ne_original := C.q_ne_original hminimal
  residual_relation := C.residual_relation
  residual_minimal := C.residual_isMinimalFourCircuit hminimal
  residual_deletions := C.residual_everyDeletionIndependent hminimal
  residual_term_ne_zero := C.residual_term_ne_zero hminimal
  residual_nonproportional := C.residual_nonproportional hminimal
  residual_injective := C.residual_injective hminimal



end FieldCircuitContraction
end BilinearComplexity
