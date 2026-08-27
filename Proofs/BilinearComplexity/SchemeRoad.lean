import BilinearComplexity.SchemeDeformation
import BilinearComplexity.SchemeFlipReduction

set_option autoImplicit false

namespace BilinearComplexity
namespace Scheme
namespace Road

open Deformation FlipReduction

variable {k : Type*} {a b c n r : ℕ}

/-- An algebraic road is a coordinatewise affine one-parameter family of ordered schemes
with literal endpoints and constant represented tensor.  It uses no scheme-theoretic notions. -/
structure AlgebraicRoad [CommRing k]
    (source target : Scheme k a b c r) where
  /-- The ordered scheme at a parameter value. -/
  point : k → Scheme k a b c r
  /-- Every first-factor coordinate is affine in the parameter. -/
  first_affine : ∀ s i, ∃ x dx : k, ∀ t, ((point t).term s).1 i = x + t * dx
  /-- Every second-factor coordinate is affine in the parameter. -/
  second_affine : ∀ s j, ∃ x dx : k, ∀ t, ((point t).term s).2.1 j = x + t * dx
  /-- Every third-factor coordinate is affine in the parameter. -/
  third_affine : ∀ s l, ∃ x dx : k, ∀ t, ((point t).term s).2.2 l = x + t * dx
  /-- Parameter zero is literally the source ordered scheme. -/
  at_zero : point 0 = source
  /-- Parameter one is literally the target ordered scheme. -/
  at_one : point 1 = target
  /-- The represented tensor is exactly constant along the family. -/
  sumTensor_at : ∀ t, (point t).sumTensor = source.sumTensor

/-- The regular parameter locus records exactly the nonzero-term and term-distinctness
conditions omitted from the exact tensor equations of an algebraic road. -/
def AlgebraicRoad.regularLocus [CommRing k]
    {source target : Scheme k a b c r} (R : AlgebraicRoad source target) : Set k :=
  {t | (∀ s, (R.point t).TermNonzero s) ∧
    Function.Injective (fun s => ((R.point t).term s).eval)}

/-- Membership in the regular locus is precisely validity for the road's constant tensor. -/
theorem AlgebraicRoad.valid_at_iff_mem_regularLocus [CommRing k]
    {source target : Scheme k a b c r} (R : AlgebraicRoad source target) (t : k) :
    (R.point t).Valid source.sumTensor ↔ t ∈ R.regularLocus := by
  rw [Valid]
  simp only [R.sumTensor_at t, true_and]
  rfl

/-- Literal endpoint equality and family exactness imply equality of the represented endpoint
tensors, independently of any validity or minimal-rank assertion. -/
theorem AlgebraicRoad.target_sumTensor_eq_source [CommRing k]
    {source target : Scheme k a b c r} (R : AlgebraicRoad source target) :
    target.sumTensor = source.sumTensor := by
  rw [← R.at_one]
  exact R.sumTensor_at 1

/-- Every ordered point of a road gives only a rank-at-most statement for the constant tensor. -/
theorem AlgebraicRoad.rankLE [CommRing k]
    {source target : Scheme k a b c r} (R : AlgebraicRoad source target) (t : k) :
    RankLE source.sumTensor r := by
  rw [← R.sumTensor_at t]
  exact (R.point t).rankLE_sumTensor

/-- The constant family is an algebraic road from a scheme to itself. -/
def AlgebraicRoad.refl [CommRing k] (S : Scheme k a b c r) : AlgebraicRoad S S where
  point := fun _ => S
  first_affine := by
    intro s i
    exact ⟨(S.term s).1 i, 0, by simp⟩
  second_affine := by
    intro s j
    exact ⟨(S.term s).2.1 j, 0, by simp⟩
  third_affine := by
    intro s l
    exact ⟨(S.term s).2.2 l, 0, by simp⟩
  at_zero := rfl
  at_one := rfl
  sumTensor_at := fun _ => rfl

/-- Scaling the coefficient of a first-position ordinary flip gives an exact algebraic road. -/
def firstFlipRoad [Field k] (S : Scheme k a b c 2) (q : k)
    (hrep : RepeatedNonzeroFactor S .first) :
    AlgebraicRoad S (flipPair S .first q) where
  point := fun t => flipPair S .first (t * q)
  first_affine := by
    intro s i
    fin_cases s
    · exact ⟨(S.term 0).1 i, 0, by
        intro t
        simp [flipPair, pairScheme]⟩
    · exact ⟨(S.term 1).1 i, 0, by
        intro t
        simp [flipPair, pairScheme]⟩
  second_affine := by
    intro s j
    fin_cases s
    · exact ⟨(S.term 0).2.1 j, q * (S.term 1).2.1 j, by
        intro t
        simp [flipPair, pairScheme, Pi.smul_apply, smul_eq_mul]
        ring⟩
    · exact ⟨(S.term 1).2.1 j, 0, by
        intro t
        simp [flipPair, pairScheme]⟩
  third_affine := by
    intro s l
    fin_cases s
    · exact ⟨(S.term 0).2.2 l, 0, by
        intro t
        simp [flipPair, pairScheme]⟩
    · exact ⟨(S.term 1).2.2 l, -(q * (S.term 0).2.2 l), by
        intro t
        simp [flipPair, pairScheme, Pi.smul_apply, smul_eq_mul]
        ring⟩
  at_zero := by
    apply congrArg Scheme.mk
    funext s
    fin_cases s <;> simp
  at_one := by
    apply congrArg Scheme.mk
    funext s
    fin_cases s <;> simp
  sumTensor_at := fun t => sumTensor_flipPair S .first (t * q) hrep

/-- Erase one ordered slot, retaining the increasing `Fin.succAbove` order of all survivors. -/
def eraseSlot (S : Scheme k a b c (n + 1)) (p : Fin (n + 1)) : Scheme k a b c n :=
  ⟨fun s => S.term (p.succAbove s)⟩

/-- Erasing a slot reads every survivor through the standard increasing `succAbove` embedding. -/
@[simp] theorem eraseSlot_term (S : Scheme k a b c (n + 1)) (p : Fin (n + 1))
    (s : Fin n) : (eraseSlot S p).term s = S.term (p.succAbove s) :=
  rfl

/-- If the erased slot evaluates to zero, erasing it preserves the represented tensor exactly. -/
theorem sumTensor_eraseSlot_of_eval_eq_zero [CommSemiring k]
    (S : Scheme k a b c (n + 1)) (p : Fin (n + 1))
    (hp : (S.term p).eval = 0) :
    (eraseSlot S p).sumTensor = S.sumTensor := by
  funext i j l
  rw [sumTensor, sumTensor, Fin.sum_univ_succAbove (fun s => (S.term s).eval i j l) p]
  simp only [eraseSlot_term]
  rw [show (S.term p).eval i j l = 0 by rw [hp]; rfl]
  exact (zero_add _).symm

/-- An explicit Kauers--Moosbauer reduction witness in the first-factor orientation.
It names nonzero scales onto one common first factor and a second-factor dependence
with a selected nonzero pivot coefficient. -/
structure FirstFactorReductionWitness [Field k] (S : Scheme k a b c (n + 1)) where
  /-- The common first-factor line generator. -/
  commonFirst : Fin a → k
  /-- The scalar expressing each stored first factor on the common line. -/
  firstScale : Fin (n + 1) → k
  /-- Every scale is nonzero, allowing an interpolation with the literal stored factors. -/
  firstScale_ne_zero : ∀ s, firstScale s ≠ 0
  /-- Exact stored first-factor equations. -/
  first_eq : ∀ s, (S.term s).1 = firstScale s • commonFirst
  /-- Coefficients of the dependent second-factor relation. -/
  coefficient : Fin (n + 1) → k
  /-- The selected relation pivot. -/
  pivot : Fin (n + 1)
  /-- The pivot coefficient is nonzero. -/
  pivot_ne_zero : coefficient pivot ≠ 0
  /-- The exact second-factor dependence relation. -/
  second_relation : (∑ s, coefficient s • (S.term s).2.1) = 0

namespace FirstFactorReductionWitness

/-- The exact interpolation scales the pivot third factor by `1-t` and transfers its
missing tensor contribution to all nonpivot third factors through the dependence relation. -/
def family [Field k] {S : Scheme k a b c (n + 1)}
    (W : FirstFactorReductionWitness S) (t : k) : Scheme k a b c (n + 1) :=
  ⟨fun s =>
    ((S.term s).1, (S.term s).2.1,
      if s = W.pivot then
        (1 - t) • (S.term s).2.2
      else
        (S.term s).2.2 -
          (t * (W.coefficient s / W.coefficient W.pivot) *
            (W.firstScale W.pivot / W.firstScale s)) •
              (S.term W.pivot).2.2)⟩

/-- Parameter zero of the reduction interpolation is literally the original ordered scheme. -/
@[simp] theorem family_zero [Field k] {S : Scheme k a b c (n + 1)}
    (W : FirstFactorReductionWitness S) : W.family 0 = S := by
  apply congrArg Scheme.mk
  funext s
  simp

/-- The zero-slot boundary is the literal parameter-one endpoint of the interpolation. -/
def boundary [Field k] {S : Scheme k a b c (n + 1)}
    (W : FirstFactorReductionWitness S) : Scheme k a b c (n + 1) :=
  W.family 1

/-- The shorter replacement erases the pivot slot from the zero-slot boundary. -/
def shorter [Field k] {S : Scheme k a b c (n + 1)}
    (W : FirstFactorReductionWitness S) : Scheme k a b c n :=
  eraseSlot W.boundary W.pivot

/-- Every surviving slot of the shorter endpoint has the literal Kauers--Moosbauer
third-factor update in increasing source-slot order. -/
@[simp] theorem shorter_term [Field k] {S : Scheme k a b c (n + 1)}
    (W : FirstFactorReductionWitness S) (s : Fin n) :
    W.shorter.term s =
      ((S.term (W.pivot.succAbove s)).1,
        (S.term (W.pivot.succAbove s)).2.1,
        (S.term (W.pivot.succAbove s)).2.2 -
          (W.coefficient (W.pivot.succAbove s) / W.coefficient W.pivot *
            (W.firstScale W.pivot / W.firstScale (W.pivot.succAbove s))) •
              (S.term W.pivot).2.2) := by
  simp [shorter, boundary, family, Fin.succAbove_ne]

/-- Every coordinate of the explicit reduction interpolation is affine in its parameter. -/
theorem family_affine [Field k] {S : Scheme k a b c (n + 1)}
    (W : FirstFactorReductionWitness S) :
    (∀ s i, ∃ x dx : k, ∀ t, ((W.family t).term s).1 i = x + t * dx) ∧
    (∀ s j, ∃ x dx : k, ∀ t, ((W.family t).term s).2.1 j = x + t * dx) ∧
    (∀ s l, ∃ x dx : k, ∀ t, ((W.family t).term s).2.2 l = x + t * dx) := by
  constructor
  · intro s i
    exact ⟨(S.term s).1 i, 0, by simp [family]⟩
  constructor
  · intro s j
    exact ⟨(S.term s).2.1 j, 0, by simp [family]⟩
  · intro s l
    by_cases hs : s = W.pivot
    · subst s
      exact ⟨(S.term W.pivot).2.2 l, -(S.term W.pivot).2.2 l, by
        intro t
        simp [family, Pi.smul_apply, smul_eq_mul]
        ring⟩
    · exact ⟨(S.term s).2.2 l,
          -(W.coefficient s / W.coefficient W.pivot *
            (W.firstScale W.pivot / W.firstScale s) *
              (S.term W.pivot).2.2 l), by
        intro t
        simp [family, hs, Pi.smul_apply, smul_eq_mul]
        ring⟩

/-- The Kauers--Moosbauer interpolation preserves the represented tensor for every parameter. -/
theorem sumTensor_family [Field k] {S : Scheme k a b c (n + 1)}
    (W : FirstFactorReductionWitness S) (t : k) :
    (W.family t).sumTensor = S.sumTensor := by
  funext i j l
  have hrel : (∑ s, W.coefficient s * (S.term s).2.1 j) = 0 := by
    have hcoord := congrFun W.second_relation j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] using hcoord
  have hfirst (s : Fin (n + 1)) :
      (S.term s).1 i = W.firstScale s * W.commonFirst i := by
    have hcoord := congrFun (W.first_eq s) i
    simpa only [Pi.smul_apply, smul_eq_mul] using hcoord
  let d : k := t * (W.firstScale W.pivot / W.coefficient W.pivot) *
    W.commonFirst i * (S.term W.pivot).2.2 l
  have hterm (s : Fin (n + 1)) :
      ((W.family t).term s).eval i j l =
        (S.term s).eval i j l -
          d * (W.coefficient s * (S.term s).2.1 j) := by
    by_cases hs : s = W.pivot
    · subst s
      simp only [family, TriadData.eval, triad, if_pos, Pi.smul_apply,
        smul_eq_mul]
      rw [hfirst W.pivot]
      dsimp only [d]
      field_simp [W.pivot_ne_zero]
    · simp only [family, TriadData.eval, triad, if_neg hs, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [hfirst s]
      dsimp only [d]
      field_simp [W.pivot_ne_zero, W.firstScale_ne_zero s]
  simp only [sumTensor]
  calc
    (∑ s, ((W.family t).term s).eval i j l) =
        ∑ s, ((S.term s).eval i j l -
          d * (W.coefficient s * (S.term s).2.1 j)) := by
      apply Finset.sum_congr rfl
      intro s _hs
      exact hterm s
    _ = (∑ s, (S.term s).eval i j l) -
        d * ∑ s, W.coefficient s * (S.term s).2.1 j := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = ∑ s, (S.term s).eval i j l := by
      rw [hrel, mul_zero, sub_zero]

/-- The explicit reduction family is an algebraic road from the source to its zero-slot boundary. -/
def road [Field k] {S : Scheme k a b c (n + 1)}
    (W : FirstFactorReductionWitness S) : AlgebraicRoad S W.boundary where
  point := W.family
  first_affine := W.family_affine.1
  second_affine := W.family_affine.2.1
  third_affine := W.family_affine.2.2
  at_zero := W.family_zero
  at_one := rfl
  sumTensor_at := W.sumTensor_family

/-- At the boundary the selected pivot has a literally zero third factor. -/
theorem boundary_pivot_third_eq_zero [Field k] {S : Scheme k a b c (n + 1)}
    (W : FirstFactorReductionWitness S) :
    (W.boundary.term W.pivot).2.2 = 0 := by
  simp [boundary, family]

/-- The selected boundary slot evaluates to the zero tensor. -/
theorem boundary_pivot_eval_eq_zero [Field k] {S : Scheme k a b c (n + 1)}
    (W : FirstFactorReductionWitness S) :
    (W.boundary.term W.pivot).eval = 0 := by
  funext i j l
  simp [TriadData.eval, triad, W.boundary_pivot_third_eq_zero]

/-- The erased boundary is an exact shorter replacement for the source tensor. -/
theorem shorter_sumTensor_eq [Field k] {S : Scheme k a b c (n + 1)}
    (W : FirstFactorReductionWitness S) :
    W.shorter.sumTensor = S.sumTensor := by
  calc
    W.shorter.sumTensor = W.boundary.sumTensor :=
      sumTensor_eraseSlot_of_eval_eq_zero W.boundary W.pivot W.boundary_pivot_eval_eq_zero
    _ = S.sumTensor := W.sumTensor_family 1

/-- The reduction witness supplies a rank-at-most-`n` decomposition; it makes no
minimality or exact-rank claim. -/
theorem rankLE [Field k] {S : Scheme k a b c (n + 1)}
    (W : FirstFactorReductionWitness S) : RankLE S.sumTensor n := by
  rw [← W.shorter_sumTensor_eq]
  exact W.shorter.rankLE_sumTensor

end FirstFactorReductionWitness

/-- If a masked restricted Jacobian has zero kernel, a genuinely first nonzero
order-three arc coefficient cannot be supported in that mask. -/
theorem first_nonzero_not_mem_allowed_of_restricted_ker_eq_bot
    [CommRing k] {S : Scheme k a b c r} (A : OrderThreeArc S)
    (M : VariationMask a b c r) (q : Fin 3)
    (hlower : ∀ p, p < q → A.coefficient p = 0)
    (hnonzero : A.coefficient q ≠ 0)
    (hker : LinearMap.ker (M.restrictedJacobian S) = ⊥) :
    A.coefficient q ∉ M.allowed := by
  intro hsupported
  let d : M.allowed (k := k) := ⟨A.coefficient q, hsupported⟩
  have hdker : d ∈ LinearMap.ker (M.restrictedJacobian S) := by
    rw [LinearMap.mem_ker]
    change jacobian S (A.coefficient q) = 0
    exact (A.first_nonzero_mem_ker q hlower hnonzero).2
  have hdmem : d ∈ (⊥ : Submodule k (M.allowed (k := k))) := by
    rw [← hker]
    exact hdker
  have hdzero : d = 0 := by
    simpa only [Submodule.mem_bot] using hdmem
  exact hnonzero (congrArg Subtype.val hdzero)

section Fixtures

/-- The scalar two-slot scheme used to show the road and reduction hypotheses jointly occur. -/
def scalarPair : Scheme ℚ 1 1 1 2 :=
  ⟨fun _ => (![1], ![1], ![1])⟩

/-- The scalar pair repeats a nonzero first factor. -/
theorem scalarPair_repeated : RepeatedNonzeroFactor scalarPair .first := by
  constructor
  · intro h
    have h0 := congrFun h 0
    norm_num [scalarPair] at h0
  · rfl

/-- A concrete first-factor reduction witness has two nonzero terms and a nontrivial relation. -/
def scalarReductionWitness : FirstFactorReductionWitness scalarPair where
  commonFirst := ![1]
  firstScale := fun _ => 1
  firstScale_ne_zero := fun _ => one_ne_zero
  first_eq := by intro s; simp [scalarPair]
  coefficient := ![1, -1]
  pivot := 0
  pivot_ne_zero := one_ne_zero
  second_relation := by
    funext j
    fin_cases j
    simp [scalarPair, Fin.sum_univ_two]

/-- The concrete flip road has the named literal endpoints and constant tensor. -/
example :
    (firstFlipRoad scalarPair 1 scalarPair_repeated).point 0 = scalarPair ∧
      (firstFlipRoad scalarPair 1 scalarPair_repeated).point 1 =
        flipPair scalarPair .first 1 ∧
      ∀ t, ((firstFlipRoad scalarPair 1 scalarPair_repeated).point t).sumTensor =
        scalarPair.sumTensor := by
  exact ⟨(firstFlipRoad scalarPair 1 scalarPair_repeated).at_zero,
    (firstFlipRoad scalarPair 1 scalarPair_repeated).at_one,
    (firstFlipRoad scalarPair 1 scalarPair_repeated).sumTensor_at⟩

/-- The concrete reduction road reaches a zero slot and its erased endpoint has one term. -/
example :
    (scalarReductionWitness.boundary.term scalarReductionWitness.pivot).eval = 0 ∧
      scalarReductionWitness.shorter.sumTensor = scalarPair.sumTensor := by
  exact ⟨scalarReductionWitness.boundary_pivot_eval_eq_zero,
    scalarReductionWitness.shorter_sumTensor_eq⟩

end Fixtures

#check @AlgebraicRoad
#check @AlgebraicRoad.valid_at_iff_mem_regularLocus
#check @AlgebraicRoad.target_sumTensor_eq_source
#check @firstFlipRoad
#check @FirstFactorReductionWitness
#check @FirstFactorReductionWitness.road
#check @FirstFactorReductionWitness.shorter_sumTensor_eq
#check @FirstFactorReductionWitness.rankLE
#check @first_nonzero_not_mem_allowed_of_restricted_ker_eq_bot

#print axioms AlgebraicRoad.valid_at_iff_mem_regularLocus
#print axioms AlgebraicRoad.target_sumTensor_eq_source
#print axioms firstFlipRoad
#print axioms FirstFactorReductionWitness.sumTensor_family
#print axioms FirstFactorReductionWitness.shorter_sumTensor_eq
#print axioms FirstFactorReductionWitness.rankLE
#print axioms first_nonzero_not_mem_allowed_of_restricted_ker_eq_bot

end Road
end Scheme
end BilinearComplexity
