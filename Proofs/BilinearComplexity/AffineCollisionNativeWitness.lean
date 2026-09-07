import BilinearComplexity.BinaryOneFactorDeformation
import BilinearComplexity.FieldNativePairBridge
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-!
# An affine factor-collision native-Flip checkpoint

This file records the bounded bridge analysis following
`Scheme.BinaryOneFactorDeformation.collision_deformation_dichotomy` and checks one concrete
native witness.  It does not provide a general collision-to-move interface.

Consider two distinct nonzero endpoint terms over `F2` with a first-factor collision,

`x = a ⊗ b ⊗ c` and `y = a ⊗ d ⊗ e`.

The relevant identity is

`x + y = a ⊗ (b + d) ⊗ c + a ⊗ d ⊗ (e + c)`.

For an endpoint produced by the published affine construction, the precise retained-factor
hypotheses needed for the two displayed outputs to be atoms are `b ≠ d` and `c ≠ e`.  They
follow when the source is `FactorwiseSeparated`, the slots are distinct, and both slots select
`.first`: the second and third factors are unchanged and separated.  Over `F2` these inequalities
are exactly the nonvanishing of `b + d` and `e + c`.  Endpoint validity supplies nonvanishing
of `a,b,c,d,e` and distinctness of `x,y`.  The two outputs are then distinct from each other and
from both sources.

Let `C` be the unchanged valid context.  There are three exhaustive freshness cases.

* If neither output occurs in `C`, both outputs are nonzero and fresh against every context
  term, so `FlipFormula.secondThird`, `NativeReplacement.flip`, and `contextualStrictStep`
  give a legal strict ordinary Flip.
* If exactly one output occurs in `C`, remove `x`, `y`, and that context copy, then insert the
  other output.  Binary cancellation preserves the exact tensor and changes an `N`-term
  decomposition to an `N - 2`-term decomposition.
* If both outputs occur in `C`, their context copies are distinct because the outputs are
  distinct.  Remove `x`, `y`, and both copies and insert nothing.  Binary cancellation gives
  an exact `N - 4`-term decomposition.

A valid context contains each atom at most once, so there is no unaccounted multiple-match
case.  The retained inequalities are sufficient but not necessary for the broader dichotomy.
Without them, endpoint validity rules out both outputs being zero but permits exactly one zero.
Omitting that zero and inserting the other output shortens by one when it is fresh; if the
nonzero output already occurs in `C`, canceling its context copy shortens by three.  Thus endpoint
validity alone still gives “ordinary Flip or strictly shorter exact decomposition,” while
`b ≠ d` and `c ≠ e` are precisely what restricts the analysis to the three freshness cases above.
-/

namespace BilinearComplexity
namespace AffineCollisionNativeWitness

open FieldRankOne FieldContextual FieldNativeMoves FieldNativePath
open Scheme.BinaryOneFactorDeformation

/-- Concrete separated retained factors and a five-atom fresh context realize the binary
collision identity as one strict native ordinary Flip. -/
theorem exists_strictNativeFlip :
    ∃ (a b d : Factor F2 3) (c e : Factor F2 3)
      (hbd : b.1 + d.1 ≠ 0) (hec : e.1 + c.1 ≠ 0)
      (C : State F2 3 3 3),
      b.1 ≠ d.1 ∧ c.1 ≠ e.1 ∧ C.card = 5 ∧
      let source₁ := atom a b c
      let source₂ := atom a d e
      let target₁ := atom a (Factor.add b d hbd) c
      let target₂ := atom a d (Factor.add e c hec)
      Nonempty (StrictNativeStep
        (stateUnion C (pairState source₁ source₂))
        (stateUnion C (pairState target₁ target₂))) := by
  let f1 : Factor F2 3 := ⟨![1, 0, 0], by decide⟩
  let f2 : Factor F2 3 := ⟨![0, 1, 0], by decide⟩
  let f3 : Factor F2 3 := ⟨![0, 0, 1], by decide⟩
  let f12 : Factor F2 3 := ⟨![1, 1, 0], by decide⟩
  let f13 : Factor F2 3 := ⟨![1, 0, 1], by decide⟩
  let f23 : Factor F2 3 := ⟨![0, 1, 1], by decide⟩
  let a := f1
  let b := f1
  let d := f2
  let c := f1
  let e := f2
  have hbd : b.1 + d.1 ≠ 0 := by
    dsimp [b, d, f1, f2]
    decide
  have hec : e.1 + c.1 ≠ 0 := by
    dsimp [e, c, f1, f2]
    decide
  have hsub : e.1 - c.1 ≠ 0 := by
    dsimp [e, c, f1, f2]
    decide
  have hsubadd : Factor.sub e c hsub = Factor.add e c hec := by
    apply Subtype.ext
    dsimp [Factor.sub, Factor.add, e, c, f1, f2]
    funext i
    fin_cases i <;> decide
  let source₁ := atom a b c
  let source₂ := atom a d e
  let target₁ := atom a (Factor.add b d hbd) c
  let target₂ := atom a d (Factor.add e c hec)
  let q1 := atom f2 f3 f3
  let q2 := atom f3 f3 f3
  let q3 := atom f12 f3 f3
  let q4 := atom f13 f3 f3
  let q5 := atom f23 f3 f3
  let C : State F2 3 3 3 := {q1, q2, q3, q4, q5}
  have atom_ne_of_coord (x y : Atom F2 3 3 3) (i j l : Fin 3)
      (hcoord : x.val i j l ≠ y.val i j l) : x ≠ y :=
    Atom.ne_of_val_ne fun hval => hcoord (congrFun (congrFun (congrFun hval i) j) l)
  have hbne : b.1 ≠ d.1 := by
    dsimp [b, d, f1, f2]
    decide
  have hcne : c.1 ≠ e.1 := by
    dsimp [c, e, f1, f2]
    decide
  have hCcard : C.card = 5 := by
    dsimp [C, q1, q2, q3, q4, q5, f1, f2, f3, f12, f13, f23]
    decide
  have hsource : source₁ ≠ source₂ := by
    dsimp [source₁, source₂, a, b, c, d, e, f1, f2]
    decide
  have htarget : target₁ ≠ target₂ := by
    apply atom_ne_of_coord target₁ target₂ 0 0 0
    simp [target₁, target₂, a, b, c, d, e, f1, f2, Factor.add,
      FieldNativeMoves.atom_val, evalFactors]
  have hsource₁target₁ : source₁ ≠ target₁ := by
    apply atom_ne_of_coord source₁ target₁ 0 1 0
    simp [source₁, target₁, a, b, c, d, f1, f2, Factor.add,
      FieldNativeMoves.atom_val, evalFactors]
  have hsource₁target₂ : source₁ ≠ target₂ := by
    apply atom_ne_of_coord source₁ target₂ 0 1 1
    simp [source₁, target₂, a, b, c, d, e, f1, f2, Factor.add,
      FieldNativeMoves.atom_val, evalFactors]
  have hsource₂target₁ : source₂ ≠ target₁ := by
    apply atom_ne_of_coord source₂ target₁ 0 1 1
    simp [source₂, target₁, a, b, c, d, e, f1, f2, Factor.add,
      FieldNativeMoves.atom_val, evalFactors]
  have hsource₂target₂ : source₂ ≠ target₂ := by
    apply atom_ne_of_coord source₂ target₂ 0 1 0
    simp [source₂, target₂, a, c, d, e, f1, f2, Factor.add,
      FieldNativeMoves.atom_val, evalFactors]
  let shear : ShearFormula 3 3 (fun v w => atom a v w)
      source₁ source₂ target₁ target₂ := {
    x₁ := b
    x₂ := d
    y₁ := c
    y₂ := e
    sum_ne := hbd
    diff_ne := hsub
    source₁_eq := rfl
    source₂_eq := rfl
    target₁_eq := rfl
    target₂_eq := by rw [hsubadd] }
  let native : NativeReplacement (pairState source₁ source₂)
      (pairState target₁ target₂) :=
    .flip (.secondThird a shear) hsource htarget
  have hendpoints : Disjoint (pairState source₁ source₂)
      (pairState target₁ target₂) := by
    simp [pairState, hsource₁target₁.symm, hsource₁target₂.symm,
      hsource₂target₁.symm, hsource₂target₂.symm]
  have hq1local (v w : Factor F2 3) : q1 ≠ atom a v w := by
    apply atom_ne_of_coord q1 (atom a v w) 1 2 2
    simp [q1, a, f1, f2, f3, FieldNativeMoves.atom_val, evalFactors]
  have hq2local (v w : Factor F2 3) : q2 ≠ atom a v w := by
    apply atom_ne_of_coord q2 (atom a v w) 2 2 2
    simp [q2, a, f1, f3, FieldNativeMoves.atom_val, evalFactors]
  have hq3local (v w : Factor F2 3) : q3 ≠ atom a v w := by
    apply atom_ne_of_coord q3 (atom a v w) 1 2 2
    simp [q3, a, f1, f3, f12, FieldNativeMoves.atom_val, evalFactors]
  have hq4local (v w : Factor F2 3) : q4 ≠ atom a v w := by
    apply atom_ne_of_coord q4 (atom a v w) 2 2 2
    simp [q4, a, f1, f3, f13, FieldNativeMoves.atom_val, evalFactors]
  have hq5local (v w : Factor F2 3) : q5 ≠ atom a v w := by
    apply atom_ne_of_coord q5 (atom a v w) 1 2 2
    simp [q5, a, f1, f3, f23, FieldNativeMoves.atom_val, evalFactors]
  have hq1 : q1 ∉ stateUnion (pairState source₁ source₂)
      (pairState target₁ target₂) := by
    simp [stateUnion, pairState, source₁, source₂, target₁, target₂, hq1local]
  have hq2 : q2 ∉ stateUnion (pairState source₁ source₂)
      (pairState target₁ target₂) := by
    simp [stateUnion, pairState, source₁, source₂, target₁, target₂, hq2local]
  have hq3 : q3 ∉ stateUnion (pairState source₁ source₂)
      (pairState target₁ target₂) := by
    simp [stateUnion, pairState, source₁, source₂, target₁, target₂, hq3local]
  have hq4 : q4 ∉ stateUnion (pairState source₁ source₂)
      (pairState target₁ target₂) := by
    simp [stateUnion, pairState, source₁, source₂, target₁, target₂, hq4local]
  have hq5 : q5 ∉ stateUnion (pairState source₁ source₂)
      (pairState target₁ target₂) := by
    simp [stateUnion, pairState, source₁, source₂, target₁, target₂, hq5local]
  have hcontext : Disjoint C
      (stateUnion (pairState source₁ source₂) (pairState target₁ target₂)) := by
    rw [Finset.disjoint_left]
    intro x hxC hxLocal
    simp only [C, Finset.mem_insert, Finset.mem_singleton] at hxC
    rcases hxC with rfl | rfl | rfl | rfl | rfl
    · exact hq1 hxLocal
    · exact hq2 hxLocal
    · exact hq3 hxLocal
    · exact hq4 hxLocal
    · exact hq5 hxLocal
  refine ⟨a, b, d, c, e, hbd, hec, C, hbne, hcne, hCcard, ?_⟩
  exact ⟨FieldNativePairBridge.contextualStrictStep native hendpoints hcontext⟩

#check @exists_strictNativeFlip
#print axioms exists_strictNativeFlip

end AffineCollisionNativeWitness
end BilinearComplexity
