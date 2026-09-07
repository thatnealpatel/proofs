import BilinearComplexity.SchemeReplacement
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-!
# Exact one-factor affine deformations over F2

For each slot of a finite ordered `Scheme`, `ModeChoice` selects exactly one of its three
factors.  A `Delta` stores candidate vectors for all three factor types in each slot, while
the mode choice activates exactly one candidate and ignores the other two.  The endpoint adds
only that active vector.  The linear map
`evaluationDifference` is the sum of the corresponding one-factor insertions.

The main contracts proved below are:

* `sumTensor_update` and `sumTensor_update_of_mem_ker`: the endpoint sum is the source sum
  plus the linear evaluation difference, hence kernel points preserve the exact tensor;
* `first_collision_feasible_iff_mem_range` and its two analogues: a prescribed same-factor
  collision between two slots is feasible precisely when the affine source offset belongs to
  the range of the coordinate-difference map restricted to the evaluation kernel;
* `update_retains_unchanged_unequal_factor`: if each source factor family is injective, every
  endpoint pair retains a common unchanged source factor that is unequal;
* `update_eval_injective`: over F2, nonzero endpoint pure tensors are therefore pairwise
  distinct;
* `collision_deformation_dichotomy`: a kernel endpoint with a prescribed factor collision
  either has a zero term, which can be erased to a strictly shorter exact scheme, or is an
  exact scheme of the same displayed size whose nonzero pure tensors are distinct while the
  prescribed factor collision remains.

The final collision is equality of one factor, not equality of the evaluated pure tensors.
No endpoint is asserted to be a legal Flip or Reduction move.  The affine-kernel construction
is the elementary linear-algebra step used in Algorithm 4 of Heule--Kauers--Seidl,
*New ways to multiply 3 x 3-matrices*, Journal of Symbolic Computation 104 (2021), Section 7;
the exact endpoint and distinctness statements here are elementary consequences specialized
to the repository's concrete tensors over `ZMod 2`.
-/

namespace BilinearComplexity
namespace Scheme
namespace BinaryOneFactorDeformation

abbrev F2 := ZMod 2

variable {a b c r : ℕ}

/-- One of the three factor modes of a pure three-tensor. -/
inductive ModeChoice
  | first
  | second
  | third
  deriving DecidableEq, Repr

/-- A deformation payload stores candidate vectors for each mode in every slot.  The mode
choice below activates exactly one component and ignores the other two. -/
abbrev Delta (a b c r : ℕ) :=
  Fin r → TriadData F2 a b c

/-- The first-factor change, zero unless the selected mode is first. -/
def firstChange (choice : Fin r → ModeChoice) (d : Delta a b c r)
    (s : Fin r) : Fin a → F2 :=
  match choice s with
  | .first => (d s).1
  | .second => 0
  | .third => 0

/-- The second-factor change, zero unless the selected mode is second. -/
def secondChange (choice : Fin r → ModeChoice) (d : Delta a b c r)
    (s : Fin r) : Fin b → F2 :=
  match choice s with
  | .first => 0
  | .second => (d s).2.1
  | .third => 0

/-- The third-factor change, zero unless the selected mode is third. -/
def thirdChange (choice : Fin r → ModeChoice) (d : Delta a b c r)
    (s : Fin r) : Fin c → F2 :=
  match choice s with
  | .first => 0
  | .second => 0
  | .third => (d s).2.2

example (d : Delta 1 1 1 1) :
    firstChange (fun _ : Fin 1 => .first) d 0 = (d 0).1 := rfl

example (d : Delta 1 1 1 1) :
    secondChange (fun _ : Fin 1 => .first) d 0 = 0 := rfl

example (d : Delta 1 1 1 1) :
    thirdChange (fun _ : Fin 1 => .first) d 0 = 0 := rfl

/-- Add the one selected change vector to each source term. -/
def update (S : Scheme F2 a b c r) (choice : Fin r → ModeChoice)
    (d : Delta a b c r) : Scheme F2 a b c r :=
  ⟨fun s => ((S.term s).1 + firstChange choice d s,
    (S.term s).2.1 + secondChange choice d s,
    (S.term s).2.2 + thirdChange choice d s)⟩

example (S : Scheme F2 1 1 1 1)
    (d : Delta 1 1 1 1) :
    (update S (fun _ : Fin 1 => .first) d).term 0 =
      ((S.term 0).1 + firstChange (fun _ : Fin 1 => .first) d 0,
        (S.term 0).2.1, (S.term 0).2.2) := by
  simp [update, firstChange, secondChange, thirdChange]

/-- The linear evaluation difference obtained by inserting the selected delta while leaving
both other factors fixed. -/
def evaluationDifference (S : Scheme F2 a b c r) (choice : Fin r → ModeChoice) :
    Delta a b c r →ₗ[F2] Tensor F2 a b c where
  toFun d := fun i j l => ∑ s, (
    firstChange choice d s i * (S.term s).2.1 j * (S.term s).2.2 l +
    (S.term s).1 i * secondChange choice d s j * (S.term s).2.2 l +
    (S.term s).1 i * (S.term s).2.1 j * thirdChange choice d s l)
  map_add' d e := by
    funext i j l
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _hs
    cases h : choice s <;>
      simp only [firstChange, secondChange, thirdChange, h, Pi.add_apply,
        Prod.fst_add, Prod.snd_add, Pi.zero_apply] <;> ring
  map_smul' q d := by
    funext i j l
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _hs
    cases h : choice s <;>
      simp only [firstChange, secondChange, thirdChange, h, Pi.smul_apply,
        Prod.smul_fst, Prod.smul_snd, Pi.zero_apply] <;> ring

example (S : Scheme F2 1 1 1 1) :
    evaluationDifference S (fun _ : Fin 1 => .first) 0 = 0 := by
  exact LinearMap.map_zero _

/-- The exact endpoint tensor is the source tensor plus the selected linear evaluation
change.  There are no higher-order terms because each slot changes only one factor. -/
theorem sumTensor_update (S : Scheme F2 a b c r) (choice : Fin r → ModeChoice)
    (d : Delta a b c r) :
    (update S choice d).sumTensor = S.sumTensor + evaluationDifference S choice d := by
  funext i j l
  simp only [Scheme.sumTensor, update, TriadData.eval, triad, Pi.add_apply,
    evaluationDifference, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _hs
  cases h : choice s <;>
    simp only [firstChange, secondChange, thirdChange, h, Pi.zero_apply,
      add_zero] <;> ring

/-- Every kernel deformation preserves the represented tensor exactly. -/
theorem sumTensor_update_of_mem_ker (S : Scheme F2 a b c r)
    (choice : Fin r → ModeChoice) (d : Delta a b c r)
    (hd : d ∈ LinearMap.ker (evaluationDifference S choice)) :
    (update S choice d).sumTensor = S.sumTensor := by
  rw [sumTensor_update, LinearMap.mem_ker.mp hd, add_zero]

/-- The active first coordinate at a slot, as a linear map on deformation payloads. -/
def firstCoordinate (choice : Fin r → ModeChoice) (s : Fin r) :
    Delta a b c r →ₗ[F2] (Fin a → F2) where
  toFun d := firstChange choice d s
  map_add' d e := by
    cases h : choice s <;>
      simp [firstChange, h]
  map_smul' q d := by
    cases h : choice s <;>
      simp [firstChange, h]

/-- The active second coordinate at a slot, as a linear map on deformation payloads. -/
def secondCoordinate (choice : Fin r → ModeChoice) (s : Fin r) :
    Delta a b c r →ₗ[F2] (Fin b → F2) where
  toFun d := secondChange choice d s
  map_add' d e := by
    cases h : choice s <;>
      simp [secondChange, h]
  map_smul' q d := by
    cases h : choice s <;>
      simp [secondChange, h]

/-- The active third coordinate at a slot, as a linear map on deformation payloads. -/
def thirdCoordinate (choice : Fin r → ModeChoice) (s : Fin r) :
    Delta a b c r →ₗ[F2] (Fin c → F2) where
  toFun d := thirdChange choice d s
  map_add' d e := by
    cases h : choice s <;>
      simp [thirdChange, h]
  map_smul' q d := by
    cases h : choice s <;>
      simp [thirdChange, h]

example (choice : Fin r → ModeChoice) (s : Fin r) :
    firstCoordinate (a := a) (b := b) (c := c) choice s 0 = 0 := by
  exact LinearMap.map_zero _

example (choice : Fin r → ModeChoice) (s : Fin r) :
    secondCoordinate (a := a) (b := b) (c := c) choice s 0 = 0 := by
  exact LinearMap.map_zero _

example (choice : Fin r → ModeChoice) (s : Fin r) :
    thirdCoordinate (a := a) (b := b) (c := c) choice s 0 = 0 := by
  exact LinearMap.map_zero _

/-- On the exact-deformation kernel, add the two active first-coordinate changes. -/
def firstKernelDifference (S : Scheme F2 a b c r) (choice : Fin r → ModeChoice)
    (p q : Fin r) :
    LinearMap.ker (evaluationDifference S choice) →ₗ[F2] (Fin a → F2) :=
  (firstCoordinate choice p + firstCoordinate choice q).comp
    (LinearMap.ker (evaluationDifference S choice)).subtype

/-- On the exact-deformation kernel, add the two active second-coordinate changes. -/
def secondKernelDifference (S : Scheme F2 a b c r) (choice : Fin r → ModeChoice)
    (p q : Fin r) :
    LinearMap.ker (evaluationDifference S choice) →ₗ[F2] (Fin b → F2) :=
  (secondCoordinate choice p + secondCoordinate choice q).comp
    (LinearMap.ker (evaluationDifference S choice)).subtype

/-- On the exact-deformation kernel, add the two active third-coordinate changes. -/
def thirdKernelDifference (S : Scheme F2 a b c r) (choice : Fin r → ModeChoice)
    (p q : Fin r) :
    LinearMap.ker (evaluationDifference S choice) →ₗ[F2] (Fin c → F2) :=
  (thirdCoordinate choice p + thirdCoordinate choice q).comp
    (LinearMap.ker (evaluationDifference S choice)).subtype

example (S : Scheme F2 a b c r) (choice : Fin r → ModeChoice) (p q : Fin r) :
    firstKernelDifference S choice p q 0 = 0 := by exact LinearMap.map_zero _

example (S : Scheme F2 a b c r) (choice : Fin r → ModeChoice) (p q : Fin r) :
    secondKernelDifference S choice p q 0 = 0 := by exact LinearMap.map_zero _

example (S : Scheme F2 a b c r) (choice : Fin r → ModeChoice) (p q : Fin r) :
    thirdKernelDifference S choice p q 0 = 0 := by exact LinearMap.map_zero _

/-- Every element of an F2-module is its own additive inverse. -/
theorem add_self_eq_zero_f2_module {M : Type*} [AddCommGroup M] [Module F2 M]
    (x : M) : x + x = 0 := by
  calc
    x + x = (1 : F2) • x + (1 : F2) • x := by simp only [one_smul]
    _ = ((1 : F2) + 1) • x := (add_smul 1 1 x).symm
    _ = 0 := by rw [show (1 : F2) + 1 = 0 by decide, zero_smul]

/-- In an F2-module, equality of two affine translates is the corresponding source-offset
equation. -/
theorem add_eq_add_iff_add_eq_add_f2 {M : Type*} [AddCommGroup M] [Module F2 M]
    (u d v e : M) : u + d = v + e ↔ d + e = u + v := by
  constructor
  · intro h
    calc
      d + e = (u + u) + (d + e) := by rw [add_self_eq_zero_f2_module, zero_add]
      _ = (u + d) + (u + e) := by ac_rfl
      _ = (v + e) + (u + e) := congrArg (fun z => z + (u + e)) h
      _ = (e + e) + (v + u) := by ac_rfl
      _ = u + v := by rw [add_self_eq_zero_f2_module, zero_add, add_comm]
  · intro h
    calc
      u + d = (e + e) + (u + d) := by rw [add_self_eq_zero_f2_module, zero_add]
      _ = (d + e) + (u + e) := by ac_rfl
      _ = (u + v) + (u + e) := congrArg (fun z => z + (u + e)) h
      _ = (u + u) + (v + e) := by ac_rfl
      _ = v + e := by rw [add_self_eq_zero_f2_module, zero_add]

/-- A kernel deformation producing a first-factor collision exists exactly when the affine
first-factor offset lies in the range of the kernel-restricted coordinate-difference map. -/
theorem first_collision_feasible_iff_mem_range
    (S : Scheme F2 a b c r) (choice : Fin r → ModeChoice) (p q : Fin r)
    (_hpq : p ≠ q) (_hp : choice p = .first) (_hq : choice q = .first) :
    (∃ d : Delta a b c r,
      d ∈ LinearMap.ker (evaluationDifference S choice) ∧
      ((update S choice d).term p).1 = ((update S choice d).term q).1) ↔
      (S.term p).1 + (S.term q).1 ∈
        LinearMap.range (firstKernelDifference S choice p q) := by
  constructor
  · rintro ⟨d, hd, hcollision⟩
    refine ⟨⟨d, hd⟩, ?_⟩
    change firstChange choice d p + firstChange choice d q = _
    exact (add_eq_add_iff_add_eq_add_f2 _ _ _ _).mp hcollision
  · rintro ⟨d, hd⟩
    refine ⟨d.1, d.property, ?_⟩
    apply (add_eq_add_iff_add_eq_add_f2 _ _ _ _).mpr
    change firstChange choice d.1 p + firstChange choice d.1 q = _ at hd
    exact hd

/-- A kernel deformation producing a second-factor collision exists exactly when the affine
second-factor offset lies in the range of the kernel-restricted coordinate-difference map. -/
theorem second_collision_feasible_iff_mem_range
    (S : Scheme F2 a b c r) (choice : Fin r → ModeChoice) (p q : Fin r)
    (_hpq : p ≠ q) (_hp : choice p = .second) (_hq : choice q = .second) :
    (∃ d : Delta a b c r,
      d ∈ LinearMap.ker (evaluationDifference S choice) ∧
      ((update S choice d).term p).2.1 = ((update S choice d).term q).2.1) ↔
      (S.term p).2.1 + (S.term q).2.1 ∈
        LinearMap.range (secondKernelDifference S choice p q) := by
  constructor
  · rintro ⟨d, hd, hcollision⟩
    refine ⟨⟨d, hd⟩, ?_⟩
    change secondChange choice d p + secondChange choice d q = _
    exact (add_eq_add_iff_add_eq_add_f2 _ _ _ _).mp hcollision
  · rintro ⟨d, hd⟩
    refine ⟨d.1, d.property, ?_⟩
    apply (add_eq_add_iff_add_eq_add_f2 _ _ _ _).mpr
    change secondChange choice d.1 p + secondChange choice d.1 q = _ at hd
    exact hd

/-- A kernel deformation producing a third-factor collision exists exactly when the affine
third-factor offset lies in the range of the kernel-restricted coordinate-difference map. -/
theorem third_collision_feasible_iff_mem_range
    (S : Scheme F2 a b c r) (choice : Fin r → ModeChoice) (p q : Fin r)
    (_hpq : p ≠ q) (_hp : choice p = .third) (_hq : choice q = .third) :
    (∃ d : Delta a b c r,
      d ∈ LinearMap.ker (evaluationDifference S choice) ∧
      ((update S choice d).term p).2.2 = ((update S choice d).term q).2.2) ↔
      (S.term p).2.2 + (S.term q).2.2 ∈
        LinearMap.range (thirdKernelDifference S choice p q) := by
  constructor
  · rintro ⟨d, hd, hcollision⟩
    refine ⟨⟨d, hd⟩, ?_⟩
    change thirdChange choice d p + thirdChange choice d q = _
    exact (add_eq_add_iff_add_eq_add_f2 _ _ _ _).mp hcollision
  · rintro ⟨d, hd⟩
    refine ⟨d.1, d.property, ?_⟩
    apply (add_eq_add_iff_add_eq_add_f2 _ _ _ _).mpr
    change thirdChange choice d.1 p + thirdChange choice d.1 q = _ at hd
    exact hd

/-- The source factors are individually nonzero and pairwise distinct in each of the three
modes.  This is stronger than pairwise distinct evaluated source terms. -/
def FactorwiseSeparated (S : Scheme F2 a b c r) : Prop :=
  (∀ s, (S.term s).1 ≠ 0 ∧ (S.term s).2.1 ≠ 0 ∧ (S.term s).2.2 ≠ 0) ∧
  Function.Injective (fun s => (S.term s).1) ∧
  Function.Injective (fun s => (S.term s).2.1) ∧
  Function.Injective (fun s => (S.term s).2.2)

example : FactorwiseSeparated
    (⟨fun _ : Fin 1 => (![1], ![1], ![1])⟩ : Scheme F2 1 1 1 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    fin_cases s
    simp
  · intro s t _hst
    exact Subsingleton.elim s t
  · intro s t _hst
    exact Subsingleton.elim s t
  · intro s t _hst
    exact Subsingleton.elim s t

/-- Any two endpoint slots retain a common unchanged source factor; source separation makes
that retained factor unequal. -/
theorem update_retains_unchanged_unequal_factor
    (S : Scheme F2 a b c r) (choice : Fin r → ModeChoice) (d : Delta a b c r)
    (hS : FactorwiseSeparated S) (s t : Fin r) (hst : s ≠ t) :
    (((update S choice d).term s).1 = (S.term s).1 ∧
      ((update S choice d).term t).1 = (S.term t).1 ∧
      (S.term s).1 ≠ (S.term t).1) ∨
    (((update S choice d).term s).2.1 = (S.term s).2.1 ∧
      ((update S choice d).term t).2.1 = (S.term t).2.1 ∧
      (S.term s).2.1 ≠ (S.term t).2.1) ∨
    (((update S choice d).term s).2.2 = (S.term s).2.2 ∧
      ((update S choice d).term t).2.2 = (S.term t).2.2 ∧
      (S.term s).2.2 ≠ (S.term t).2.2) := by
  have hfirst : (S.term s).1 ≠ (S.term t).1 := fun heq => hst (hS.2.1 heq)
  have hsecond : (S.term s).2.1 ≠ (S.term t).2.1 := fun heq => hst (hS.2.2.1 heq)
  have hthird : (S.term s).2.2 ≠ (S.term t).2.2 := fun heq => hst (hS.2.2.2 heq)
  cases hs : choice s <;> cases ht : choice t
  · exact Or.inr (Or.inl ⟨by simp [update, secondChange, hs],
      by simp [update, secondChange, ht], hsecond⟩)
  · exact Or.inr (Or.inr ⟨by simp [update, thirdChange, hs],
      by simp [update, thirdChange, ht], hthird⟩)
  · exact Or.inr (Or.inl ⟨by simp [update, secondChange, hs],
      by simp [update, secondChange, ht], hsecond⟩)
  · exact Or.inr (Or.inr ⟨by simp [update, thirdChange, hs],
      by simp [update, thirdChange, ht], hthird⟩)
  · exact Or.inl ⟨by simp [update, firstChange, hs],
      by simp [update, firstChange, ht], hfirst⟩
  · exact Or.inl ⟨by simp [update, firstChange, hs],
      by simp [update, firstChange, ht], hfirst⟩
  · exact Or.inr (Or.inl ⟨by simp [update, secondChange, hs],
      by simp [update, secondChange, ht], hsecond⟩)
  · exact Or.inl ⟨by simp [update, firstChange, hs],
      by simp [update, firstChange, ht], hfirst⟩
  · exact Or.inl ⟨by simp [update, firstChange, hs],
      by simp [update, firstChange, ht], hfirst⟩

/-- A nonzero binary scalar is one. -/
theorem eq_one_of_ne_zero_f2 (x : F2) (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact (hx rfl).elim
  · rfl

/-- Over F2, two equal nonzero evaluated pure tensors have identical factors.  The conclusion
fails over larger fields because reciprocal rescalings of factors are possible. -/
theorem factors_eq_of_eval_eq_of_ne_zero
    (x y : TriadData F2 a b c) (hx : x.eval ≠ 0) (_hy : y.eval ≠ 0)
    (hxy : x.eval = y.eval) :
    x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2 = y.2.2 := by
  classical
  have hxFirst : ∃ i, x.1 i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext i j k
    simp [TriadData.eval, h i]
  have hxSecond : ∃ j, x.2.1 j ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext i j k
    simp [TriadData.eval, h j]
  have hxThird : ∃ k, x.2.2 k ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext i j k
    simp [TriadData.eval, h k]
  obtain ⟨i, hi0⟩ := hxFirst
  obtain ⟨j, hj0⟩ := hxSecond
  obtain ⟨k, hk0⟩ := hxThird
  have hi : x.1 i = 1 := eq_one_of_ne_zero_f2 _ hi0
  have hj : x.2.1 j = 1 := eq_one_of_ne_zero_f2 _ hj0
  have hk : x.2.2 k = 1 := eq_one_of_ne_zero_f2 _ hk0
  have hcoord (i' : Fin a) (j' : Fin b) (k' : Fin c) :
      x.1 i' * x.2.1 j' * x.2.2 k' = y.1 i' * y.2.1 j' * y.2.2 k' :=
    congrFun (congrFun (congrFun hxy i') j') k'
  have hyProduct : y.1 i * y.2.1 j * y.2.2 k ≠ 0 := by
    rw [← hcoord i j k, hi, hj, hk]
    decide
  have hyi0 : y.1 i ≠ 0 := by
    intro hyi
    apply hyProduct
    simp [hyi]
  have hyj0 : y.2.1 j ≠ 0 := by
    intro hyj
    apply hyProduct
    simp [hyj]
  have hyk0 : y.2.2 k ≠ 0 := by
    intro hyk
    apply hyProduct
    simp [hyk]
  have hyi : y.1 i = 1 := eq_one_of_ne_zero_f2 _ hyi0
  have hyj : y.2.1 j = 1 := eq_one_of_ne_zero_f2 _ hyj0
  have hyk : y.2.2 k = 1 := eq_one_of_ne_zero_f2 _ hyk0
  refine ⟨funext fun i' => ?_, funext fun j' => ?_, funext fun k' => ?_⟩
  · simpa only [hj, hk, hyj, hyk, mul_one] using hcoord i' j k
  · simpa only [hi, hk, hyi, hyk, one_mul, mul_one] using hcoord i j' k
  · simpa only [hi, hj, hyi, hyj, one_mul] using hcoord i j k'

/-- If every updated term is nonzero, factorwise separation of the source makes the evaluated
updated terms pairwise distinct. -/
theorem update_eval_injective
    (S : Scheme F2 a b c r) (choice : Fin r → ModeChoice) (d : Delta a b c r)
    (hS : FactorwiseSeparated S)
    (hnonzero : ∀ s, ((update S choice d).term s).eval ≠ 0) :
    Function.Injective (fun s => ((update S choice d).term s).eval) := by
  intro s t heval
  by_contra hst
  have hretained := update_retains_unchanged_unequal_factor S choice d hS s t hst
  have hfactors := factors_eq_of_eval_eq_of_ne_zero
    ((update S choice d).term s) ((update S choice d).term t)
    (hnonzero s) (hnonzero t) heval
  rcases hretained with hfirst | hsecond | hthird
  · exact hfirst.2.2 (hfirst.1.symm.trans (hfactors.1.trans hfirst.2.1))
  · exact hsecond.2.2 (hsecond.1.symm.trans (hfactors.2.1.trans hsecond.2.1))
  · exact hthird.2.2 (hthird.1.symm.trans (hfactors.2.2.trans hthird.2.1))

/-- Equality of the factors in a prescribed mode at two slots. -/
def FactorCollision (m : ModeChoice) (E : Scheme F2 a b c r) (p q : Fin r) : Prop :=
  match m with
  | .first => (E.term p).1 = (E.term q).1
  | .second => (E.term p).2.1 = (E.term q).2.1
  | .third => (E.term p).2.2 = (E.term q).2.2

example : FactorCollision .first
    (⟨fun _ : Fin 1 => (![1], ![1], ![1])⟩ : Scheme F2 1 1 1 1) 0 0 := rfl

/-- Erasing one zero evaluated term gives a strictly shorter scheme representing the same
fixed target tensor. -/
theorem exists_shorter_valid_of_eval_eq_zero
    (T : Tensor F2 a b c) (E : Scheme F2 a b c r) (hE : E.Valid T)
    (s : Fin r) (hzero : (E.term s).eval = 0) :
    ∃ n, n < r ∧ ∃ R : Scheme F2 a b c n, R.Valid T := by
  let C : Replacement.Certificate E :=
    { removed := {s}
      inserted := []
      local_eq := by
        funext i j k
        simp [Replacement.selectedTensor, Replacement.insertedTensor, hzero] }
  refine ⟨C.resultRank, ?_, C.output, ?_⟩
  · change r - ({s} : Finset (Fin r)).card + [].length < r
    simp only [Finset.card_singleton, List.length_nil, Nat.add_zero]
    omega
  · rw [Valid, C.sumTensor_eq]
    exact hE

/-- A same-mode collision at an exact kernel endpoint has the promised dichotomy: a zero
term can be erased to a strictly shorter exact decomposition, while otherwise the endpoint
keeps the original number of terms, all nonzero and pairwise distinct, and keeps the
prescribed factor collision. -/
theorem collision_deformation_dichotomy
    (T : Tensor F2 a b c) (S : Scheme F2 a b c r)
    (choice : Fin r → ModeChoice) (d : Delta a b c r)
    (p q : Fin r) (m : ModeChoice) (hpq : p ≠ q)
    (hp : choice p = m) (hq : choice q = m)
    (hS : S.Valid T) (hsep : FactorwiseSeparated S)
    (hd : d ∈ LinearMap.ker (evaluationDifference S choice))
    (hcollision : FactorCollision m (update S choice d) p q) :
    (∃ n, n < r ∧ ∃ R : Scheme F2 a b c n, R.Valid T) ∨
    ((update S choice d).Valid T ∧
      (∀ s, ((update S choice d).term s).eval ≠ 0) ∧
      Function.Injective (fun s => ((update S choice d).term s).eval) ∧
      FactorCollision m (update S choice d) p q) := by
  have hsum : (update S choice d).sumTensor = S.sumTensor :=
    sumTensor_update_of_mem_ker S choice d hd
  have hvalid : (update S choice d).Valid T := by
    rw [Valid, hsum]
    exact hS
  by_cases hzero : ∃ s, ((update S choice d).term s).eval = 0
  · obtain ⟨s, hs⟩ := hzero
    exact Or.inl (exists_shorter_valid_of_eval_eq_zero T (update S choice d) hvalid s hs)
  · have hnonzero : ∀ s, ((update S choice d).term s).eval ≠ 0 := by
      push Not at hzero
      exact hzero
    exact Or.inr ⟨hvalid, hnonzero, update_eval_injective S choice d hsep hnonzero,
      hcollision⟩

example :
    let S : Scheme F2 3 3 3 7 := ⟨![
      (![1, 0, 0], ![1, 1, 0], ![1, 1, 1]),
      (![0, 1, 1], ![1, 0, 0], ![0, 1, 1]),
      (![0, 1, 0], ![0, 1, 0], ![1, 1, 0]),
      (![1, 1, 0], ![1, 0, 1], ![1, 0, 1]),
      (![0, 0, 1], ![0, 1, 1], ![0, 0, 1]),
      (![1, 0, 1], ![0, 0, 1], ![1, 0, 0]),
      (![1, 1, 1], ![1, 1, 1], ![0, 1, 0])]⟩
    let choice : Fin 7 → ModeChoice :=
      ![.first, .first, .first, .first, .first, .first, .second]
    let z : Fin 3 → F2 := ![0, 0, 0]
    let d : Delta 3 3 3 7 := ![
      (![1, 1, 1], z, z),
      (z, z, z),
      (![1, 1, 1], z, z),
      (![1, 1, 1], z, z),
      (![1, 1, 1], z, z),
      (![1, 1, 1], z, z),
      (z, ![1, 0, 0], z)]
    S.Valid S.sumTensor ∧ FactorwiseSeparated S ∧
      (0 : Fin 7) ≠ 1 ∧ choice 0 = .first ∧ choice 1 = .first ∧
      d ∈ LinearMap.ker (evaluationDifference S choice) ∧
      FactorCollision .first (update S choice d) 0 1 := by
  decide

end BinaryOneFactorDeformation
end Scheme
end BilinearComplexity
