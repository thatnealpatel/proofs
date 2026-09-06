import BilinearComplexity.Scheme
import BilinearComplexity.NormalizedBinaryCarrier
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace BilinearComplexity
namespace FieldRankOne

variable {k : Type*} {a b c r : ℕ}

/-- Evaluate a coefficient-bearing triple of coordinate vectors as a rectangular tensor. -/
def evalFactors [CommSemiring k] (q : k) (u : Fin a → k) (v : Fin b → k)
    (w : Fin c → k) : Tensor k a b c :=
  fun i j l => q * u i * v j * w l

/-- The scalar coordinate model agrees with the repository's unweighted triad evaluation. -/
theorem evalFactors_one_eq_triad [CommSemiring k] (u : Fin a → k) (v : Fin b → k)
    (w : Fin c → k) : evalFactors 1 u v w = (TriadData.eval (u, v, w)) := by
  funext i j l
  simp only [evalFactors, TriadData.eval, triad, one_mul]

/-- A raw representative carries a nonzero coefficient and three nonzero factors. -/
structure Rep (k : Type*) [Field k] (a b c : ℕ) where
  /-- The coefficient not absorbed into a factor. -/
  coeff : k
  /-- The first factor. -/
  first : Fin a → k
  /-- The second factor. -/
  second : Fin b → k
  /-- The third factor. -/
  third : Fin c → k
  /-- The coefficient is nonzero. -/
  coeff_ne_zero : coeff ≠ 0
  /-- The first factor is nonzero. -/
  first_ne_zero : first ≠ 0
  /-- The second factor is nonzero. -/
  second_ne_zero : second ≠ 0
  /-- The third factor is nonzero. -/
  third_ne_zero : third ≠ 0

namespace Rep

variable [Field k]

/-- Evaluate a raw representative; equality of atoms will use this value, not raw fields. -/
def eval (t : Rep k a b c) : Tensor k a b c :=
  evalFactors t.coeff t.first t.second t.third

/-- Every well-formed raw representative evaluates to a nonzero tensor. -/
theorem eval_ne_zero (t : Rep k a b c) : t.eval ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp t.first_ne_zero
  obtain ⟨j, hj⟩ := Function.ne_iff.mp t.second_ne_zero
  obtain ⟨l, hl⟩ := Function.ne_iff.mp t.third_ne_zero
  intro hzero
  have hcoord := congrFun (congrFun (congrFun hzero i) j) l
  simp only [eval, evalFactors, Pi.zero_apply] at hcoord
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero t.coeff_ne_zero hi) hj) hl hcoord

/-- Absorb the stored coefficient into the first factor and set the coefficient to one. -/
def absorbFirst (t : Rep k a b c) : Rep k a b c where
  coeff := 1
  first := t.coeff • t.first
  second := t.second
  third := t.third
  coeff_ne_zero := one_ne_zero
  first_ne_zero := smul_ne_zero t.coeff_ne_zero t.first_ne_zero
  second_ne_zero := t.second_ne_zero
  third_ne_zero := t.third_ne_zero

/-- Coefficient absorption into the first factor preserves the evaluated tensor exactly. -/
theorem absorbFirst_eval (t : Rep k a b c) : t.absorbFirst.eval = t.eval := by
  funext i j l
  simp only [absorbFirst, eval, evalFactors, Pi.smul_apply, smul_eq_mul, one_mul]

/-- Rescale all three factors while retaining the stored coefficient. -/
def productOneGauge (t : Rep k a b c) (x y z : k)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) : Rep k a b c where
  coeff := t.coeff
  first := x • t.first
  second := y • t.second
  third := z • t.third
  coeff_ne_zero := t.coeff_ne_zero
  first_ne_zero := smul_ne_zero hx t.first_ne_zero
  second_ne_zero := smul_ne_zero hy t.second_ne_zero
  third_ne_zero := smul_ne_zero hz t.third_ne_zero

/-- Product-one gauge rescaling with fixed coefficient preserves evaluation. -/
theorem productOneGauge_eval (t : Rep k a b c) (x y z : k)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hxyz : x * y * z = 1) :
    (t.productOneGauge x y z hx hy hz).eval = t.eval := by
  funext i j l
  simp only [productOneGauge, eval, evalFactors, Pi.smul_apply, smul_eq_mul]
  calc
    t.coeff * (x * t.first i) * (y * t.second j) * (z * t.third l) =
        (x * y * z) * (t.coeff * t.first i * t.second j * t.third l) := by ring
    _ = t.coeff * t.first i * t.second j * t.third l := by rw [hxyz, one_mul]

/-- Change the coefficient and all factors simultaneously. -/
def rescale (t : Rep k a b c) (q x y z : k)
    (hq : q ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) : Rep k a b c where
  coeff := q
  first := x • t.first
  second := y • t.second
  third := z • t.third
  coeff_ne_zero := hq
  first_ne_zero := smul_ne_zero hx t.first_ne_zero
  second_ne_zero := smul_ne_zero hy t.second_ne_zero
  third_ne_zero := smul_ne_zero hz t.third_ne_zero

/-- The correct general rescaling law allows the coefficient to change when
`q*x*y*z` equals the old coefficient. -/
theorem rescale_eval (t : Rep k a b c) (q x y z : k)
    (hq : q ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hprod : q * x * y * z = t.coeff) :
    (t.rescale q x y z hq hx hy hz).eval = t.eval := by
  funext i j l
  simp only [rescale, eval, evalFactors, Pi.smul_apply, smul_eq_mul]
  calc
    q * (x * t.first i) * (y * t.second j) * (z * t.third l) =
        (q * x * y * z) * (t.first i * t.second j * t.third l) := by ring
    _ = t.coeff * t.first i * t.second j * t.third l := by rw [hprod]; ring

end Rep

/-- An atom is an actual nonzero coordinate tensor together with evidence that it is pure.
Raw triples are witnesses only; atom equality is equality of evaluated tensors. -/
structure Atom (k : Type*) [Field k] (a b c : ℕ) where
  /-- The evaluated tensor, which determines atom equality. -/
  val : Tensor k a b c
  /-- The evaluated tensor is nonzero. -/
  nonzero : val ≠ 0
  /-- The tensor has a coefficient-bearing pure representative. -/
  pure : ∃ t : Rep k a b c, t.eval = val

namespace Atom

variable [Field k]

/-- Construct the actual atom represented by a raw coefficient-bearing triple. -/
def ofRep (t : Rep k a b c) : Atom k a b c where
  val := t.eval
  nonzero := t.eval_ne_zero
  pure := ⟨t, rfl⟩

/-- `ofRep` exposes exactly the representative's evaluated tensor. -/
@[simp] theorem ofRep_val (t : Rep k a b c) : (ofRep t).val = t.eval := rfl

/-- Two atoms are equal exactly when their evaluated tensors are equal. -/
@[ext] theorem ext {x y : Atom k a b c} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- Distinct evaluated tensors determine distinct semantic atoms. -/
theorem ne_of_val_ne {x y : Atom k a b c} (h : x.val ≠ y.val) : x ≠ y := by
  intro hxy
  exact h (congrArg Atom.val hxy)

/-- Atom equality is decidable whenever scalar equality is decidable, by comparing the finite
coordinate tensors that determine semantic atoms. -/
instance instDecidableEq [DecidableEq k] : DecidableEq (Atom k a b c) :=
  fun x y => decidable_of_iff (x.val = y.val) ⟨Atom.ext, congrArg Atom.val⟩

/-- Recover one raw representative of a pure atom. This is proof-side and noncomputable. -/
noncomputable def rep (x : Atom k a b c) : Rep k a b c :=
  Classical.choose x.pure

/-- The recovered representative evaluates to the atom. -/
@[simp] theorem rep_eval (x : Atom k a b c) : x.rep.eval = x.val :=
  Classical.choose_spec x.pure

/-- Convert an atom to the repository's unweighted raw triad by absorbing its coefficient. -/
noncomputable def triad (x : Atom k a b c) : TriadData k a b c :=
  ((x.rep.absorbFirst).first, (x.rep.absorbFirst).second, (x.rep.absorbFirst).third)

/-- The recovered unweighted triad evaluates faithfully to the atom. -/
@[simp] theorem triad_eval (x : Atom k a b c) : x.triad.eval = x.val := by
  rw [← x.rep_eval, ← x.rep.absorbFirst_eval]
  exact (evalFactors_one_eq_triad _ _ _).symm

end Atom

/-- A native state is a finite set of actual nonzero pure tensors. Finset occupancy therefore
uses evaluated equality and cannot retain two gauge representatives of the same atom. -/
abbrev State (k : Type*) [Field k] (a b c : ℕ) := Finset (Atom k a b c)

/-- Evaluate a native finite state by summing its actual atoms. -/
def stateEval [Field k] (s : State k a b c) : Tensor k a b c :=
  ∑ t ∈ s, t.val

/-- The empty state evaluates to zero. -/
@[simp] theorem stateEval_empty [Field k] : stateEval (∅ : State k a b c) = 0 := by
  simp [stateEval]

/-- Evaluate an ordered atom presentation without forgetting its slots. -/
def presentationEval [Field k] (p : Fin r → Atom k a b c) : Tensor k a b c :=
  ∑ i, (p i).val

/-- Forget slot order and retain only actual atoms. -/
noncomputable def presentationState [Field k] (p : Fin r → Atom k a b c) : State k a b c := by
  classical
  exact Finset.univ.image p

/-- An evaluated-injective ordered presentation loses no terms when converted to a state. -/
theorem stateEval_presentationState [Field k] (p : Fin r → Atom k a b c)
    (hp : Function.Injective p) : stateEval (presentationState p) = presentationEval p := by
  classical
  unfold stateEval presentationState presentationEval
  rw [Finset.sum_image]
  exact fun x _ y _ hxy => hp hxy

/-- Build an actual atom from a repository triad known to evaluate nontrivially. -/
def atomOfTriad [Field k] (t : TriadData k a b c) (ht : t.eval ≠ 0) :
    Atom k a b c where
  val := t.eval
  nonzero := ht
  pure := by
    have hfirst : t.1 ≠ 0 := by
      intro hu
      apply ht
      funext i j l
      simp only [TriadData.eval, triad, hu, Pi.zero_apply, zero_mul]
    have hsecond : t.2.1 ≠ 0 := by
      intro hv
      apply ht
      funext i j l
      simp only [TriadData.eval, triad, hv, Pi.zero_apply, mul_zero, zero_mul]
    have hthird : t.2.2 ≠ 0 := by
      intro hw
      apply ht
      funext i j l
      simp only [TriadData.eval, triad, hw, Pi.zero_apply, mul_zero]
    let rep : Rep k a b c := {
      coeff := 1
      first := t.1
      second := t.2.1
      third := t.2.2
      coeff_ne_zero := one_ne_zero
      first_ne_zero := hfirst
      second_ne_zero := hsecond
      third_ne_zero := hthird }
    refine ⟨rep, ?_⟩
    exact evalFactors_one_eq_triad _ _ _

/-- Convert a valid ordered scheme to its faithful atom presentation. -/
def schemePresentation [Field k] (S : Scheme k a b c r)
    (hS : ∀ i, S.TermNonzero i) : Fin r → Atom k a b c :=
  fun i => atomOfTriad (S.term i) (hS i)

/-- Valid scheme slots remain injective after conversion to actual atoms. -/
theorem schemePresentation_injective [Field k] (S : Scheme k a b c r)
    (hS : ∀ i, S.TermNonzero i)
    (hinj : Function.Injective (fun i => (S.term i).eval)) :
    Function.Injective (schemePresentation S hS) := by
  intro i j hij
  apply hinj
  exact congrArg Atom.val hij

/-- A valid ordered scheme and its native finite-set image have exactly the same evaluation. -/
theorem stateEval_schemePresentation [Field k] (S : Scheme k a b c r)
    (hS : S.Valid S.sumTensor) :
    stateEval (presentationState (schemePresentation S hS.2.1)) = S.sumTensor := by
  rw [stateEval_presentationState _ (schemePresentation_injective S hS.2.1 hS.2.2)]
  funext i j l
  simp only [presentationEval, Scheme.sumTensor, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro x _hx
  rfl

/-- Enumerate a finite native state as an ordered scheme, choosing one representative per atom. -/
noncomputable def stateScheme [Field k] (s : State k a b c) : Scheme k a b c s.card :=
  ⟨fun i => Atom.triad ((s.equivFin.symm i).val)⟩

/-- The ordered scheme recovered from a state is valid and evaluates to exactly that state. -/
theorem stateScheme_valid [Field k] (s : State k a b c) :
    (stateScheme s).Valid (stateEval s) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · funext i j l
    rw [Scheme.sumTensor, stateEval]
    simp only [Finset.sum_apply, stateScheme]
    calc
      (∑ x : Fin s.card, (Atom.triad ((s.equivFin.symm x).val)).eval i j l) =
          ∑ x : Fin s.card, (s.equivFin.symm x).val.val i j l := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact congrFun (congrFun (congrFun (Atom.triad_eval _) i) j) l
      _ = ∑ x : {x // x ∈ s}, x.val.val i j l := by
        exact Equiv.sum_comp s.equivFin.symm
          (fun x : {x // x ∈ s} => x.val.val i j l)
      _ = ∑ x ∈ s, x.val i j l :=
        (Finset.sum_subtype s (fun _ => Iff.rfl) (fun x => x.val i j l)).symm
  · intro i
    change (Atom.triad ((s.equivFin.symm i).val)).eval ≠ 0
    rw [Atom.triad_eval]
    exact (s.equivFin.symm i).val.nonzero
  · intro i j hij
    change (Atom.triad ((s.equivFin.symm i).val)).eval =
      (Atom.triad ((s.equivFin.symm j).val)).eval at hij
    simp only [Atom.triad_eval] at hij
    have hatom : (s.equivFin.symm i).val = (s.equivFin.symm j).val := Atom.ext hij
    exact s.equivFin.symm.injective (Subtype.ext hatom)

/-- Effective linear transport consists of a tensor linear map, an injective map of actual
atoms, and a checked commuting square between them. This interface never transports a chosen raw
gauge representative independently of its evaluated atom. -/
structure LinearTransport (k : Type*) [Field k] (a b c a' b' c' : ℕ) where
  /-- The effective map on actual atoms. -/
  atomMap : Atom k a b c → Atom k a' b' c'
  /-- The effective linear map on coordinate tensors. -/
  tensorMap : Tensor k a b c →ₗ[k] Tensor k a' b' c'
  /-- Atom evaluation commutes with tensor transport. -/
  map_val : ∀ x, (atomMap x).val = tensorMap x.val
  /-- Distinct atoms remain distinct, so transport creates no collisions. -/
  atomMap_injective : Function.Injective atomMap

namespace LinearTransport

variable [Field k] {a' b' c' : ℕ}

/-- Transport every atom of a finite state by the supplied injective atom map. Finset mapping
uses the injection directly and requires no classical equality decision. -/
def mapState (F : LinearTransport k a b c a' b' c')
    (s : State k a b c) : State k a' b' c' :=
  s.map ⟨F.atomMap, F.atomMap_injective⟩

/-- Effective injective state transport commutes exactly with finite-state evaluation. -/
theorem stateEval_mapState (F : LinearTransport k a b c a' b' c')
    (s : State k a b c) : stateEval (F.mapState s) = F.tensorMap (stateEval s) := by
  classical
  unfold mapState stateEval
  rw [Finset.sum_map]
  change (∑ x ∈ s, (F.atomMap x).val) = F.tensorMap (∑ x ∈ s, x.val)
  simp_rw [F.map_val]
  rw [map_sum]

/-- Identity transport is an effective collision-preserving linear transport. -/
def id (k : Type*) [Field k] (a b c : ℕ) : LinearTransport k a b c a b c where
  atomMap := _root_.id
  tensorMap := LinearMap.id
  map_val := fun _ => rfl
  atomMap_injective := Function.injective_id

/-- Identity transport fixes every finite state. -/
@[simp] theorem id_mapState (s : State k a b c) : (id k a b c).mapState s = s := by
  classical
  simp [mapState, id]

end LinearTransport

namespace BinaryCorrespondence

open NormalizedBinaryCarrier

/-- Convert a normalized binary factor triple to its actual evaluated semantic atom. -/
def ofCarrier {p : Profile} (t : Carrier p) :
    Atom F2 p.first p.second p.third :=
  Atom.ofRep {
    coeff := 1
    first := t.1.1
    second := t.2.1.1
    third := t.2.2.1
    coeff_ne_zero := one_ne_zero
    first_ne_zero := t.1.2
    second_ne_zero := t.2.1.2
    third_ne_zero := t.2.2.2 }

/-- Binary carrier conversion preserves the coordinate tensor exactly. -/
@[simp] theorem ofCarrier_val {p : Profile} (t : Carrier p) :
    (ofCarrier t).val = tensorEvaluation t := by
  exact evalFactors_one_eq_triad _ _ _

/-- Binary carrier conversion is injective because normalized F2 rank-one evaluation is injective. -/
theorem ofCarrier_injective {p : Profile} : Function.Injective (@ofCarrier p) := by
  intro s t hst
  apply tensorEvaluation_injective
  simpa only [← ofCarrier_val] using congrArg Atom.val hst

/-- Recover the unique normalized F2 carrier triple from an actual semantic atom. -/
noncomputable def toCarrier {p : Profile} (x : Atom F2 p.first p.second p.third) : Carrier p :=
  ⟨⟨x.triad.1, (x.rep.absorbFirst).first_ne_zero⟩,
    ⟨⟨x.triad.2.1, (x.rep.absorbFirst).second_ne_zero⟩,
      ⟨x.triad.2.2, (x.rep.absorbFirst).third_ne_zero⟩⟩⟩

/-- Recovering a carrier and converting back fixes every actual binary atom. -/
@[simp] theorem ofCarrier_toCarrier {p : Profile}
    (x : Atom F2 p.first p.second p.third) : ofCarrier (toCarrier x) = x := by
  apply Atom.ext
  rw [ofCarrier_val, tensorEvaluation_eq_triad]
  exact Atom.triad_eval x

/-- Converting a normalized carrier and recovering it fixes the carrier. -/
@[simp] theorem toCarrier_ofCarrier {p : Profile} (t : Carrier p) :
    toCarrier (ofCarrier t) = t := by
  apply ofCarrier_injective
  exact ofCarrier_toCarrier (ofCarrier t)

/-- Normalized binary factor triples are equivalent to actual nonzero pure-tensor atoms. -/
noncomputable def atomEquiv (p : Profile) :
    Carrier p ≃ Atom F2 p.first p.second p.third where
  toFun := ofCarrier
  invFun := toCarrier
  left_inv := toCarrier_ofCarrier
  right_inv := ofCarrier_toCarrier

/-- Finite-set binary states correspond bijectively, without introducing occurrence multiplicity. -/
noncomputable def stateEquiv (p : Profile) :
    NormalizedBinaryCarrier.State p ≃ State F2 p.first p.second p.third :=
  (atomEquiv p).finsetCongr

/-- The binary finite-set correspondence preserves state cardinality. -/
@[simp] theorem stateEquiv_card {p : Profile} (D : NormalizedBinaryCarrier.State p) :
    ((stateEquiv p) D).card = D.card := by
  classical
  simp [stateEquiv]

/-- The binary finite-set correspondence preserves coordinate tensor evaluation exactly. -/
theorem stateEquiv_eval {p : Profile} (D : NormalizedBinaryCarrier.State p) :
    stateEval ((stateEquiv p) D) = NormalizedBinaryCarrier.stateEvaluation D := by
  classical
  simp [stateEquiv, stateEval, NormalizedBinaryCarrier.stateEvaluation,
    BinaryCircuit.evaluation, atomEquiv]

/-- The empty normalized binary state corresponds to the empty semantic state. -/
example : (stateEquiv profile221) (∅ : NormalizedBinaryCarrier.State profile221) = ∅ := by
  classical
  simp [stateEquiv]

end BinaryCorrespondence

/-- The finite-state representation is satisfiable over a genuinely nonbinary field. -/
example :
    let oneRep : Rep (ZMod 3) 1 1 1 := {
      coeff := 2
      first := fun _ => 1
      second := fun _ => 1
      third := fun _ => 1
      coeff_ne_zero := by decide
      first_ne_zero := by decide
      second_ne_zero := by decide
      third_ne_zero := by decide }
    (Atom.ofRep oneRep).val 0 0 0 = 2 := by
  decide

#check @Rep.rescale_eval
#check @stateEval_schemePresentation
#check @stateScheme_valid
#check @LinearTransport.stateEval_mapState
#check @BinaryCorrespondence.atomEquiv
#check @BinaryCorrespondence.stateEquiv
#check @BinaryCorrespondence.stateEquiv_card
#check @BinaryCorrespondence.stateEquiv_eval
#print axioms Rep.rescale_eval
#print axioms stateScheme_valid
#print axioms LinearTransport.stateEval_mapState
#print axioms BinaryCorrespondence.stateEquiv_eval

end FieldRankOne
end BilinearComplexity
