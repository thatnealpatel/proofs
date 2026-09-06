import BilinearComplexity.FieldContextual
import Mathlib.Tactic.Abel

set_option autoImplicit false

namespace BilinearComplexity
namespace FieldNativeMoves

open FieldRankOne FieldContextual

variable {k : Type*} {a b c : ℕ} [Field k]

/-- A nonzero coordinate factor. Bundling nonvanishing keeps field-native formula witnesses
honest without choosing a gauge representative for an atom. -/
abbrev Factor (k : Type*) [Zero k] (n : ℕ) := {u : Fin n → k // u ≠ 0}

namespace Factor

/-- Negation preserves nonvanishing. -/
def neg (u : Factor k a) : Factor k a := ⟨-u.1, neg_ne_zero.mpr u.2⟩

/-- A certified nonzero sum of two factors. -/
def add (u v : Factor k a) (h : u.1 + v.1 ≠ 0) : Factor k a := ⟨u.1 + v.1, h⟩

/-- A certified nonzero difference of two factors. -/
def sub (u v : Factor k a) (h : u.1 - v.1 ≠ 0) : Factor k a := ⟨u.1 - v.1, h⟩

/-- Reversing a nonzero difference preserves nonvanishing. -/
theorem sub_ne_zero_rev (u v : Factor k a) (h : u.1 - v.1 ≠ 0) :
    v.1 - u.1 ≠ 0 := by
  intro huv
  apply h
  have hneg : -(v.1 - u.1) = -(0 : Fin a → k) := congrArg (fun z : Fin a → k => -z) huv
  simpa only [neg_sub, neg_zero] using hneg

/-- Reversing a certified difference negates it as a bundled factor. -/
theorem sub_rev_eq_neg (u v : Factor k a) (h : u.1 - v.1 ≠ 0) :
    Factor.sub v u (sub_ne_zero_rev u v h) = Factor.neg (Factor.sub u v h) := by
  apply Subtype.ext
  simp only [sub, neg, neg_sub]

/-- Adding the negation of the second summand recovers the first bundled factor. -/
theorem add_add_neg_eq (u v : Factor k a) (h : u.1 + v.1 ≠ 0)
    (hback : (Factor.add u v h).1 + (Factor.neg v).1 ≠ 0) :
    Factor.add (Factor.add u v h) (Factor.neg v) hback = u := by
  apply Subtype.ext
  simp only [add, neg, add_neg_cancel_right]

/-- Subtracting the first input from the reversed difference gives the negated second input. -/
theorem sub_rev_sub_eq_neg (u v : Factor k a) (h : u.1 - v.1 ≠ 0)
    (hback : (Factor.sub v u (sub_ne_zero_rev u v h)).1 - v.1 ≠ 0) :
    Factor.sub (Factor.sub v u (sub_ne_zero_rev u v h)) v hback = Factor.neg u := by
  apply Subtype.ext
  simp only [sub, neg]
  abel

end Factor

/-- Evaluate a coefficient-absorbed nonzero factor triple as an actual semantic atom. -/
def atom (u : Factor k a) (v : Factor k b) (w : Factor k c) : Atom k a b c :=
  Atom.ofRep {
    coeff := 1
    first := u.1
    second := v.1
    third := w.1
    coeff_ne_zero := one_ne_zero
    first_ne_zero := u.2
    second_ne_zero := v.2
    third_ne_zero := w.2 }

/-- A coefficient-absorbed atom exposes exactly its rank-one coordinate tensor. -/
@[simp] theorem atom_val (u : Factor k a) (v : Factor k b) (w : Factor k c) :
    (atom u v w).val = evalFactors 1 u.1 v.1 w.1 := rfl

/-- Every semantic atom has a coefficient-absorbed factor presentation. -/
theorem atom_surjective (x : Atom k a b c) : ∃ u v w, atom u v w = x := by
  let r := x.rep.absorbFirst
  let u : Factor k a := ⟨r.first, r.first_ne_zero⟩
  let v : Factor k b := ⟨r.second, r.second_ne_zero⟩
  let w : Factor k c := ⟨r.third, r.third_ne_zero⟩
  refine ⟨u, v, w, ?_⟩
  apply Atom.ext
  change r.eval = x.val
  exact x.rep.absorbFirst_eval.trans x.rep_eval

/-- Negating the first two absorbed factors is a product-one gauge change. -/
theorem atom_neg_first_second (u : Factor k a) (v : Factor k b) (w : Factor k c) :
    atom (Factor.neg u) (Factor.neg v) w = atom u v w := by
  apply Atom.ext
  funext i j l
  simp only [atom_val, evalFactors, Factor.neg, Pi.neg_apply, one_mul]
  ring

/-- Negating the first and third absorbed factors is a product-one gauge change. -/
theorem atom_neg_first_third (u : Factor k a) (v : Factor k b) (w : Factor k c) :
    atom (Factor.neg u) v (Factor.neg w) = atom u v w := by
  apply Atom.ext
  funext i j l
  simp only [atom_val, evalFactors, Factor.neg, Pi.neg_apply, one_mul]
  ring

/-- Negating the second and third absorbed factors is a product-one gauge change. -/
theorem atom_neg_second_third (u : Factor k a) (v : Factor k b) (w : Factor k c) :
    atom u (Factor.neg v) (Factor.neg w) = atom u v w := by
  apply Atom.ext
  funext i j l
  simp only [atom_val, evalFactors, Factor.neg, Pi.neg_apply, one_mul]
  ring

/-- A one-factor additive formula before selecting which tensor factor it occupies. -/
structure AddFormula (n : ℕ) (f : Factor k n → Atom k a b c)
    (source left right : Atom k a b c) where
  /-- First summand. -/
  x : Factor k n
  /-- Second summand. -/
  y : Factor k n
  /-- Their sum is nonzero. -/
  sum_ne : x.1 + y.1 ≠ 0
  /-- The source uses their certified sum. -/
  source_eq : source = f (Factor.add x y sum_ne)
  /-- The first output uses the first summand. -/
  left_eq : left = f x
  /-- The second output uses the second summand. -/
  right_eq : right = f y

/-- An actual Split formula in one of the three factor positions. -/
inductive SplitFormula (source left right : Atom k a b c) : Prop
  | first (v : Factor k b) (w : Factor k c)
      (h : AddFormula a (fun u => atom u v w) source left right) :
      SplitFormula source left right
  | second (u : Factor k a) (w : Factor k c)
      (h : AddFormula b (fun v => atom u v w) source left right) :
      SplitFormula source left right
  | third (u : Factor k a) (v : Factor k b)
      (h : AddFormula c (fun w => atom u v w) source left right) :
      SplitFormula source left right

/-- Every field-native Split formula has the correct tensor evaluation. -/
theorem SplitFormula.eval_eq {source left right : Atom k a b c}
    (h : SplitFormula source left right) : source.val = left.val + right.val := by
  cases h with
  | first v w h =>
      rcases h with ⟨x, y, hsum, rfl, rfl, rfl⟩
      exact splitFirst_eval 1 x.1 y.1 v.1 w.1
  | second u w h =>
      rcases h with ⟨x, y, hsum, rfl, rfl, rfl⟩
      exact splitSecond_eval 1 u.1 x.1 y.1 w.1
  | third u v h =>
      rcases h with ⟨x, y, hsum, rfl, rfl, rfl⟩
      exact splitThird_eval 1 u.1 v.1 x.1 y.1

/-- Generic ordered shear data. The order of `(x₁,y₁)` and `(x₂,y₂)` is retained, so
source-order variants are not silently quotiented. -/
structure ShearFormula (m n : ℕ) (f : Factor k m → Factor k n → Atom k a b c)
    (source₁ source₂ target₁ target₂ : Atom k a b c) where
  /-- First source's first varying factor. -/
  x₁ : Factor k m
  /-- Second source's first varying factor. -/
  x₂ : Factor k m
  /-- First source's second varying factor. -/
  y₁ : Factor k n
  /-- Second source's second varying factor. -/
  y₂ : Factor k n
  /-- The first output's sum is nonzero. -/
  sum_ne : x₁.1 + x₂.1 ≠ 0
  /-- The second output's difference is nonzero. -/
  diff_ne : y₂.1 - y₁.1 ≠ 0
  /-- First source presentation. -/
  source₁_eq : source₁ = f x₁ y₁
  /-- Second source presentation. -/
  source₂_eq : source₂ = f x₂ y₂
  /-- First output presentation. -/
  target₁_eq : target₁ = f (Factor.add x₁ x₂ sum_ne) y₁
  /-- Second output presentation. -/
  target₂_eq : target₂ = f x₂ (Factor.sub y₂ y₁ diff_ne)

/-- The coefficient-correct inverse shear negates one first varying factor and reverses the
second-factor difference. The paired negations are a product-one gauge change. -/
def ShearFormula.inverse {m n : ℕ} {f : Factor k m → Factor k n → Atom k a b c}
    {source₁ source₂ target₁ target₂ : Atom k a b c}
    (hneg : ∀ x y, f (Factor.neg x) (Factor.neg y) = f x y)
    (h : ShearFormula m n f source₁ source₂ target₁ target₂) :
    ShearFormula m n f target₁ target₂ source₁ source₂ := by
  have hsumBack :
      (Factor.add h.x₁ h.x₂ h.sum_ne).1 + (Factor.neg h.x₂).1 ≠ 0 := by
    intro hz
    apply h.x₁.2
    calc
      h.x₁.1 = (Factor.add h.x₁ h.x₂ h.sum_ne).1 + (Factor.neg h.x₂).1 := by
        simp only [Factor.add, Factor.neg, add_neg_cancel_right]
      _ = 0 := hz
  let hrev := Factor.sub_ne_zero_rev h.y₂ h.y₁ h.diff_ne
  have hdiffBack : (Factor.sub h.y₁ h.y₂ hrev).1 - h.y₁.1 ≠ 0 := by
    intro hz
    apply h.y₂.2
    have hnegzero : -h.y₂.1 = 0 := by
      calc
        -h.y₂.1 = (Factor.sub h.y₁ h.y₂ hrev).1 - h.y₁.1 := by
          simp only [Factor.sub]
          abel
        _ = 0 := hz
    exact neg_eq_zero.mp hnegzero
  refine {
    x₁ := Factor.add h.x₁ h.x₂ h.sum_ne
    x₂ := Factor.neg h.x₂
    y₁ := h.y₁
    y₂ := Factor.sub h.y₁ h.y₂ hrev
    sum_ne := hsumBack
    diff_ne := hdiffBack
    source₁_eq := h.target₁_eq
    source₂_eq := ?_
    target₁_eq := ?_
    target₂_eq := ?_ }
  · calc
      target₂ = f h.x₂ (Factor.sub h.y₂ h.y₁ h.diff_ne) := h.target₂_eq
      _ = f (Factor.neg h.x₂) (Factor.neg (Factor.sub h.y₂ h.y₁ h.diff_ne)) :=
        (hneg h.x₂ (Factor.sub h.y₂ h.y₁ h.diff_ne)).symm
      _ = f (Factor.neg h.x₂) (Factor.sub h.y₁ h.y₂ hrev) := by
        rw [Factor.sub_rev_eq_neg h.y₂ h.y₁ h.diff_ne]
  · calc
      source₁ = f h.x₁ h.y₁ := h.source₁_eq
      _ = f (Factor.add (Factor.add h.x₁ h.x₂ h.sum_ne) (Factor.neg h.x₂)
          hsumBack) h.y₁ := by
        rw [Factor.add_add_neg_eq h.x₁ h.x₂ h.sum_ne hsumBack]
  · calc
      source₂ = f h.x₂ h.y₂ := h.source₂_eq
      _ = f (Factor.neg h.x₂) (Factor.neg h.y₂) := (hneg h.x₂ h.y₂).symm
      _ = f (Factor.neg h.x₂)
          (Factor.sub (Factor.sub h.y₁ h.y₂ hrev) h.y₁ hdiffBack) := by
        rw [Factor.sub_rev_sub_eq_neg h.y₂ h.y₁ h.diff_ne hdiffBack]

/-- The six ordered assignments of the two varying factors and the common factor. -/
inductive FlipFormula (source₁ source₂ target₁ target₂ : Atom k a b c) : Prop
  | firstSecond (w : Factor k c)
      (h : ShearFormula a b (fun u v => atom u v w)
        source₁ source₂ target₁ target₂) : FlipFormula source₁ source₂ target₁ target₂
  | secondFirst (w : Factor k c)
      (h : ShearFormula b a (fun v u => atom u v w)
        source₁ source₂ target₁ target₂) : FlipFormula source₁ source₂ target₁ target₂
  | firstThird (v : Factor k b)
      (h : ShearFormula a c (fun u w => atom u v w)
        source₁ source₂ target₁ target₂) : FlipFormula source₁ source₂ target₁ target₂
  | thirdFirst (v : Factor k b)
      (h : ShearFormula c a (fun w u => atom u v w)
        source₁ source₂ target₁ target₂) : FlipFormula source₁ source₂ target₁ target₂
  | secondThird (u : Factor k a)
      (h : ShearFormula b c (fun v w => atom u v w)
        source₁ source₂ target₁ target₂) : FlipFormula source₁ source₂ target₁ target₂
  | thirdSecond (u : Factor k a)
      (h : ShearFormula c b (fun w v => atom u v w)
        source₁ source₂ target₁ target₂) : FlipFormula source₁ source₂ target₁ target₂

/-- Every one of the six field-native Flip orientations preserves exact tensor evaluation. -/
theorem FlipFormula.eval_eq {source₁ source₂ target₁ target₂ : Atom k a b c}
    (h : FlipFormula source₁ source₂ target₁ target₂) :
    source₁.val + source₂.val = target₁.val + target₂.val := by
  cases h with
  | firstSecond w h
  | secondFirst w h
  | firstThird v h
  | thirdFirst v h
  | secondThird u h
  | thirdSecond u h =>
      rcases h with ⟨x₁, x₂, y₁, y₂, hsum, hdiff, rfl, rfl, rfl, rfl⟩
      funext i j l
      simp only [atom_val, evalFactors, Factor.add, Factor.sub, Pi.add_apply, Pi.sub_apply,
        one_mul]
      ring

/-- Every field-native Flip has a coefficient-correct inverse Flip in the same ordered
factor orientation. In particular, no characteristic-two identity is used. -/
theorem FlipFormula.symm {source₁ source₂ target₁ target₂ : Atom k a b c}
    (h : FlipFormula source₁ source₂ target₁ target₂) :
    FlipFormula target₁ target₂ source₁ source₂ := by
  cases h with
  | firstSecond w h =>
      exact .firstSecond w (h.inverse (fun u v => atom_neg_first_second u v w))
  | secondFirst w h =>
      exact .secondFirst w (h.inverse (fun v u => atom_neg_first_second u v w))
  | firstThird v h =>
      exact .firstThird v (h.inverse (fun u w => atom_neg_first_third u v w))
  | thirdFirst v h =>
      exact .thirdFirst v (h.inverse (fun w u => atom_neg_first_third u v w))
  | secondThird u h =>
      exact .secondThird u (h.inverse (fun v w => atom_neg_second_third u v w))
  | thirdSecond u h =>
      exact .thirdSecond u (h.inverse (fun w v => atom_neg_second_third u v w))

/-- A native local relation is generated only by Split, its directed Reduction inverse, and
one of the six ordered Flip orientations. Distinctness records the finite-set arity. -/
inductive NativeReplacement : State k a b c → State k a b c → Prop
  | split {source left right : Atom k a b c} (h : SplitFormula source left right)
      (hlr : left ≠ right) :
      NativeReplacement (singletonState source) (pairState left right)
  | reduction {source left right : Atom k a b c} (h : SplitFormula source left right)
      (hlr : left ≠ right) :
      NativeReplacement (pairState left right) (singletonState source)
  | flip {source₁ source₂ target₁ target₂ : Atom k a b c}
      (h : FlipFormula source₁ source₂ target₁ target₂)
      (hsource : source₁ ≠ source₂) (htarget : target₁ ≠ target₂) :
      NativeReplacement (pairState source₁ source₂) (pairState target₁ target₂)

/-- Reversing a native local relation swaps Split with directed Reduction and uses the
coefficient-correct inverse shear for Flip. -/
theorem NativeReplacement.symm {R T : State k a b c} (h : NativeReplacement R T) :
    NativeReplacement T R := by
  cases h with
  | split h hlr => exact .reduction h hlr
  | reduction h hlr => exact .split h hlr
  | flip h hs ht => exact .flip h.symm ht hs

/-- Every native local relation has equal source and target evaluation. -/
theorem NativeReplacement.eval_eq {R T : State k a b c} (h : NativeReplacement R T) :
    stateEval R = stateEval T := by
  cases h with
  | split h hlr =>
      rw [stateEval_singletonState, stateEval_pairState _ _ hlr]
      exact h.eval_eq
  | reduction h hlr =>
      rw [stateEval_pairState _ _ hlr, stateEval_singletonState]
      exact h.eval_eq.symm
  | flip h hs ht =>
      rw [stateEval_pairState _ _ hs, stateEval_pairState _ _ ht]
      exact h.eval_eq

/-- A full native step removes exactly its local source, inserts exactly its local target,
and checks target freshness only against the unchanged state. -/
structure NativeStep (D E : State k a b c) where
  /-- Local source atom set. -/
  source : State k a b c
  /-- Local target atom set. -/
  target : State k a b c
  /-- The local relation is genuinely native. -/
  native : NativeReplacement source target
  /-- Every local source atom is present. -/
  source_subset : source ⊆ D
  /-- Outputs are fresh against atoms not removed by the step. -/
  target_fresh : Disjoint target (stateDifference D source)
  /-- The endpoint is the exact erase/insert result. -/
  result_eq : E = stateUnion (stateDifference D source) target

/-- A native step preserves the evaluated tensor. -/
theorem NativeStep.eval_eq {D E : State k a b c} (h : NativeStep D E) :
    stateEval D = stateEval E := by
  rcases h with ⟨source, target, native, source_subset, target_fresh, rfl⟩
  classical
  have hsource_disjoint : Disjoint (stateDifference D source) source := by
    rw [Finset.disjoint_left]
    intro x hxDiff hxSource
    simp only [stateDifference, Finset.mem_sdiff] at hxDiff
    exact hxDiff.2 hxSource
  have hrecover : stateUnion (stateDifference D source) source = D := by
    exact Finset.sdiff_union_of_subset source_subset
  calc
    stateEval D = stateEval (stateUnion (stateDifference D source) source) :=
      congrArg stateEval hrecover.symm
    _ = stateEval (stateDifference D source) + stateEval source :=
      stateEval_union hsource_disjoint
    _ = stateEval (stateDifference D source) + stateEval target := by
      rw [native.eval_eq]
    _ = stateEval (stateUnion (stateDifference D source) target) :=
      (stateEval_union target_fresh.symm).symm

/-- Reversing a native step uses the coefficient-correct inverse local move and exactly
recovers the erased source. This construction does not assert that the step is strict. -/
def NativeStep.reverse {D E : State k a b c} (h : NativeStep D E) :
    NativeStep E D := by
  rcases h with ⟨source, target, native, source_subset, target_fresh, result_eq⟩
  have htarget_subset : target ⊆ E := by
    intro x hx
    rw [result_eq]
    simp only [stateUnion, Finset.mem_union]
    exact Or.inr hx
  have herase : stateDifference E target = stateDifference D source := by
    classical
    rw [result_eq]
    ext x
    simp only [stateDifference, stateUnion, Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hx | hx, hnot⟩
      · exact hx
      · exact False.elim (hnot hx)
    · intro hx
      refine ⟨Or.inl hx, ?_⟩
      rw [Finset.disjoint_left] at target_fresh
      exact fun hxt => target_fresh hxt (by
        simp only [stateDifference, Finset.mem_sdiff]
        exact hx)
  have hsource_fresh : Disjoint source (stateDifference E target) := by
    rw [herase]
    classical
    rw [Finset.disjoint_left]
    intro x hxSource hxDiff
    simp only [stateDifference, Finset.mem_sdiff] at hxDiff
    exact hxDiff.2 hxSource
  refine {
    source := target
    target := source
    native := native.symm
    source_subset := htarget_subset
    target_fresh := hsource_fresh
    result_eq := ?_ }
  classical
  rw [herase]
  exact (Finset.sdiff_union_of_subset source_subset).symm

/-- Reversal exposes the old local target as its local source. -/
@[simp] theorem NativeStep.reverse_source {D E : State k a b c} (h : NativeStep D E) :
    h.reverse.source = h.target := by
  classical
  rcases h with ⟨source, target, native, source_subset, target_fresh, rfl⟩
  rfl

/-- Reversal exposes the old local source as its local target. -/
@[simp] theorem NativeStep.reverse_target {D E : State k a b c} (h : NativeStep D E) :
    h.reverse.target = h.source := by
  classical
  rcases h with ⟨source, target, native, source_subset, target_fresh, rfl⟩
  rfl

#check @atom_surjective
#check @SplitFormula.eval_eq
#check @FlipFormula.eval_eq
#check @FlipFormula.symm
#check @NativeReplacement.symm
#check @NativeReplacement.eval_eq
#print axioms FlipFormula.symm
#print axioms NativeReplacement.eval_eq

end FieldNativeMoves
end BilinearComplexity
