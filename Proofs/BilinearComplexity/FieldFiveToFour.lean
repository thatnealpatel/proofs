import BilinearComplexity.FieldCircuitContraction
import BilinearComplexity.FieldNativePairBridge
import BilinearComplexity.FieldThreeProductCircuit
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace BilinearComplexity
namespace FieldFiveToFour

open FieldRankOne FieldContextual FieldNativeMoves FieldNativePath
open FieldFiveCircuitProfile FieldCircuitContraction FieldNativePairBridge

/-- The field with three elements used by the scanned contraction data. -/
abbrev F3 := FieldTernaryFiveCircuitPair.F3

/-- An effective displayed five-circuit with its actual two-versus-three endpoint equality. -/
structure DisplayedF3PairTriple (a b c : ℕ) where
  x : Fin 5 → Fin a → F3
  y : Fin 5 → Fin b → F3
  z : Fin 5 → Fin c → F3
  x_ne : ∀ i, x i ≠ 0
  y_ne : ∀ i, y i ≠ 0
  z_ne : ∀ i, z i ≠ 0
  slots : Fin 2 ⊕ Fin 3 ≃ Fin 5
  eval_eq : (∑ i : Fin 2, productFamily x y z (slots (.inl i))) =
    ∑ j : Fin 3, productFamily x y z (slots (.inr j))
  minimal : IsMinimalFiveProductCircuit x y z

namespace DisplayedF3PairTriple

variable {a b c : ℕ}

/-- The effective displayed factors at one original slot. -/
def factors (I : DisplayedF3PairTriple a b c) (i : Fin 5) : FactorTriple F3 a b c :=
  factorTripleAt I.x I.y I.z I.x_ne I.y_ne I.z_ne i

/-- The semantic atom at one original slot. -/
def atomAt (I : DisplayedF3PairTriple a b c) (i : Fin 5) : Atom F3 a b c :=
  (I.factors i).atom

/-- The actual endpoint coefficient is `1` on the two-source side and `-1` on the
three-target side. -/
def coefficient (I : DisplayedF3PairTriple a b c) (i : Fin 5) : F3 :=
  match I.slots.symm i with
  | .inl _ => 1
  | .inr _ => -1

/-- Displayed atom evaluation agrees definitionally with the five-product family. -/
@[simp] theorem atomAt_val (I : DisplayedF3PairTriple a b c) (i : Fin 5) :
    (I.atomAt i).val = productFamily I.x I.y I.z i := rfl

/-- The supplied endpoint equality is the actual signed five-term relation. -/
theorem signed_relation (I : DisplayedF3PairTriple a b c) :
    IsLinearRelation (productFamily I.x I.y I.z) I.coefficient := by
  unfold IsLinearRelation
  calc
    ∑ i, I.coefficient i • productFamily I.x I.y I.z i =
        ∑ s : Fin 2 ⊕ Fin 3,
          I.coefficient (I.slots s) • productFamily I.x I.y I.z (I.slots s) := by
      exact (I.slots.sum_comp
        (fun i => I.coefficient i • productFamily I.x I.y I.z i)).symm
    _ = (∑ i : Fin 2, productFamily I.x I.y I.z (I.slots (.inl i))) -
        ∑ j : Fin 3, productFamily I.x I.y I.z (I.slots (.inr j)) := by
      simp only [Fintype.sum_sum_type, coefficient, Equiv.symm_apply_apply,
        one_smul, neg_one_smul, sub_eq_add_neg, Finset.sum_neg_distrib]
    _ = 0 := sub_eq_zero.mpr I.eval_eq

/-- The source endpoint consists of the two displayed source atoms. -/
def sourceState (I : DisplayedF3PairTriple a b c) : State F3 a b c :=
  Finset.univ.image (fun i : Fin 2 => I.atomAt (I.slots (.inl i)))

/-- The target endpoint consists of the three displayed target atoms. -/
def targetState (I : DisplayedF3PairTriple a b c) : State F3 a b c :=
  Finset.univ.image (fun i : Fin 3 => I.atomAt (I.slots (.inr i)))

/-- Five-circuit minimality makes the displayed atom family injective. -/
theorem atomAt_injective (I : DisplayedF3PairTriple a b c) : Function.Injective I.atomAt := by
  intro i j hij
  by_contra hne
  have hli := minimalFive_pair_linearIndependent I.x I.y I.z I.minimal i j hne
  have heq : productFamily I.x I.y I.z i = productFamily I.x I.y I.z j := by
    simpa only [atomAt_val] using congrArg Atom.val hij
  have hzero : (1 : F3) • productFamily I.x I.y I.z i +
      (-1 : F3) • productFamily I.x I.y I.z j = 0 := by
    rw [one_smul, neg_one_smul, heq]
    exact add_neg_cancel _
  exact (one_ne_zero : (1 : F3) ≠ 0)
    (hli.eq_zero_of_pair (s := (1 : F3)) (t := (-1 : F3)) hzero).1

/-- The two source atoms are distinct. -/
theorem source_atoms_ne (I : DisplayedF3PairTriple a b c) :
    I.atomAt (I.slots (.inl 0)) ≠ I.atomAt (I.slots (.inl 1)) := by
  intro heq
  have hslots := I.atomAt_injective heq
  have hsum := I.slots.injective hslots
  exact Fin.zero_ne_one (Sum.inl.inj hsum)

/-- The displayed source and target endpoint states are disjoint. -/
theorem source_target_disjoint (I : DisplayedF3PairTriple a b c) :
    Disjoint I.sourceState I.targetState := by
  classical
  rw [Finset.disjoint_left]
  intro u hu hv
  simp only [sourceState, targetState, Finset.mem_image, Finset.mem_univ, true_and] at hu hv
  obtain ⟨i, rfl⟩ := hu
  obtain ⟨j, hj⟩ := hv
  have hs := I.atomAt_injective hj
  exact Sum.inr_ne_inl (I.slots.injective hs)

end DisplayedF3PairTriple

variable {a b c : ℕ}

/-- Swap a checked pair gauge, inverting its two actual nonzero scalar gauges. -/
def swapGauge {p r : FactorTriple F3 a b c} (g : PairGauge p r) : PairGauge r p := by
  cases g with
  | xy s t hs ht hfirst hsecond =>
      exact .xy s⁻¹ t⁻¹ (inv_ne_zero hs) (inv_ne_zero ht)
        (by rw [hfirst, inv_smul_smul₀ hs]) (by rw [hsecond, inv_smul_smul₀ ht])
  | xz s t hs ht hfirst hthird =>
      exact .xz s⁻¹ t⁻¹ (inv_ne_zero hs) (inv_ne_zero ht)
        (by rw [hfirst, inv_smul_smul₀ hs]) (by rw [hthird, inv_smul_smul₀ ht])
  | yz s t hs ht hsecond hthird =>
      exact .yz s⁻¹ t⁻¹ (inv_ne_zero hs) (inv_ne_zero ht)
        (by rw [hsecond, inv_smul_smul₀ hs]) (by rw [hthird, inv_smul_smul₀ ht])

/-- A computable permutation that moves two distinct indices to the first two positions. -/
def pairFrontPerm (i j : Fin 5) : Equiv.Perm (Fin 5) :=
  (Equiv.swap 1 ((Equiv.swap 0 i) j)).trans (Equiv.swap 0 i)

/-- Reindex the five slots so a selected ordered pair is the contraction pair. -/
def pairFrontSplit (i j : Fin 5) : Fin 2 ⊕ Fin 3 ≃ Fin 5 :=
  finSumFinEquiv.trans (pairFrontPerm i j)

@[simp] theorem pairFrontPerm_zero (i j : Fin 5) (hij : i ≠ j) :
    pairFrontPerm i j 0 = i := by
  fin_cases i <;> fin_cases j <;>
    simp_all [pairFrontPerm, Equiv.trans_apply, Equiv.swap_apply_def]

@[simp] theorem pairFrontPerm_one (i j : Fin 5) (hij : i ≠ j) :
    pairFrontPerm i j 1 = j := by
  fin_cases i <;> fin_cases j <;>
    simp_all [pairFrontPerm, Equiv.trans_apply, Equiv.swap_apply_def]

@[simp] theorem pairFrontSplit_left_zero (i j : Fin 5) (hij : i ≠ j) :
    pairFrontSplit i j (.inl 0) = i := by
  change pairFrontPerm i j 0 = i
  exact pairFrontPerm_zero i j hij

@[simp] theorem pairFrontSplit_left_one (i j : Fin 5) (hij : i ≠ j) :
    pairFrontSplit i j (.inl 1) = j := by
  change pairFrontPerm i j 1 = j
  exact pairFrontPerm_one i j hij

/-- Placement of the scanner-selected shared pair in the displayed two-versus-three equality. -/
inductive PairPlacement
  | sourceSource
  | targetTarget
  | opposite
  deriving DecidableEq, Repr

/-- Endpoint-aware normalization of the scanner-selected pair. The opposite constructors
always orient the difference from the source atom to the target atom. -/
inductive EffectiveDisplayedF3PairTriple (I : DisplayedF3PairTriple a b c)
    (scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne) : Type _
  | sourceSource (u v : Fin 2) (huv : u ≠ v)
      (hfirst : scan.candidate.first = I.slots (.inl u))
      (hsecond : scan.candidate.second = I.slots (.inl v))
      (pair : SumPair (I.factors scan.candidate.first) (I.factors scan.candidate.second))
  | targetTarget (u v : Fin 3) (huv : u ≠ v)
      (hfirst : scan.candidate.first = I.slots (.inr u))
      (hsecond : scan.candidate.second = I.slots (.inr v))
      (pair : SumPair (I.factors scan.candidate.first) (I.factors scan.candidate.second))
  | oppositeForward (u : Fin 2) (v : Fin 3)
      (hfirst : scan.candidate.first = I.slots (.inl u))
      (hsecond : scan.candidate.second = I.slots (.inr v))
      (pair : DifferencePair (I.factors scan.candidate.first) (I.factors scan.candidate.second))
  | oppositeReverse (u : Fin 2) (v : Fin 3)
      (hfirst : scan.candidate.first = I.slots (.inr v))
      (hsecond : scan.candidate.second = I.slots (.inl u))
      (pair : DifferencePair (I.factors scan.candidate.second) (I.factors scan.candidate.first))

namespace EffectiveDisplayedF3PairTriple

/-- The placement represented by an endpoint-aware normalized pair. -/
def placement {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) : PairPlacement :=
  match P with
  | .sourceSource .. => .sourceSource
  | .targetTarget .. => .targetTarget
  | .oppositeForward .. | .oppositeReverse .. => .opposite

/-- The first contraction slot, oriented source-to-target in an opposite placement. -/
def leftIndex {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) : Fin 5 :=
  match P with
  | .sourceSource _ _ _ _ _ _ | .targetTarget _ _ _ _ _ _ |
      .oppositeForward _ _ _ _ _ => scan.candidate.first
  | .oppositeReverse _ _ _ _ _ => scan.candidate.second

/-- The second contraction slot, oriented source-to-target in an opposite placement. -/
def rightIndex {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) : Fin 5 :=
  match P with
  | .sourceSource _ _ _ _ _ _ | .targetTarget _ _ _ _ _ _ |
      .oppositeForward _ _ _ _ _ => scan.candidate.second
  | .oppositeReverse _ _ _ _ _ => scan.candidate.first

/-- The effectively constructed displayed factors of the contraction atom. -/
def qFactors {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) : FactorTriple F3 a b c :=
  match P with
  | .sourceSource _ _ _ _ _ pair | .targetTarget _ _ _ _ _ pair => pair.qFactors
  | .oppositeForward _ _ _ _ pair | .oppositeReverse _ _ _ _ pair => pair.qFactors

/-- The effectively constructed contraction atom. -/
def q {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) : Atom F3 a b c :=
  P.qFactors.atom

/-- The selected contraction indices are distinct. -/
theorem indices_ne {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) : P.leftIndex ≠ P.rightIndex := by
  cases P with
  | sourceSource u v huv hfirst hsecond pair =>
      simpa only [leftIndex, rightIndex] using scan.valid.1
  | targetTarget u v huv hfirst hsecond pair =>
      simpa only [leftIndex, rightIndex] using scan.valid.1
  | oppositeForward u v hfirst hsecond pair =>
      simpa only [leftIndex, rightIndex] using scan.valid.1
  | oppositeReverse u v hfirst hsecond pair =>
      simpa only [leftIndex, rightIndex] using scan.valid.1.symm

/-- Exact semantic formula for the constructed contraction atom. -/
theorem q_val_eq {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) :
    P.q.val = (I.atomAt P.leftIndex).val +
      (match P.placement with | .opposite => -1 | _ => 1) •
        (I.atomAt P.rightIndex).val := by
  cases P with
  | sourceSource u v huv hfirst hsecond pair =>
      simpa only [q, qFactors, leftIndex, rightIndex, placement, pair.q_eq,
        one_smul, DisplayedF3PairTriple.atomAt, DisplayedF3PairTriple.factors] using pair.eval_eq
  | targetTarget u v huv hfirst hsecond pair =>
      simpa only [q, qFactors, leftIndex, rightIndex, placement, pair.q_eq,
        one_smul, DisplayedF3PairTriple.atomAt, DisplayedF3PairTriple.factors] using pair.eval_eq
  | oppositeForward u v hfirst hsecond pair =>
      simpa only [q, qFactors, leftIndex, rightIndex, placement, pair.q_eq,
        neg_one_smul, sub_eq_add_neg, DisplayedF3PairTriple.atomAt,
        DisplayedF3PairTriple.factors] using pair.eval_eq
  | oppositeReverse u v hfirst hsecond pair =>
      simpa only [q, qFactors, leftIndex, rightIndex, placement, pair.q_eq,
        neg_one_smul, sub_eq_add_neg, DisplayedF3PairTriple.atomAt,
        DisplayedF3PairTriple.factors] using pair.eval_eq

/-- The first displayed factor of the contraction atom lies in the span of the selected
original first factors. -/
theorem qFactors_first_mem {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) :
    P.qFactors.first.1 ∈ Submodule.span F3
      ({(I.factors P.leftIndex).first.1,
        (I.factors P.rightIndex).first.1} : Set (Fin a → F3)) := by
  cases P with
  | sourceSource u v huv hfirst hsecond pair => exact pair.first_mem
  | targetTarget u v huv hfirst hsecond pair => exact pair.first_mem
  | oppositeForward u v hfirst hsecond pair => exact pair.first_mem
  | oppositeReverse u v hfirst hsecond pair => exact pair.first_mem

/-- The second displayed factor of the contraction atom lies in the span of the selected
original second factors. -/
theorem qFactors_second_mem {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) :
    P.qFactors.second.1 ∈ Submodule.span F3
      ({(I.factors P.leftIndex).second.1,
        (I.factors P.rightIndex).second.1} : Set (Fin b → F3)) := by
  cases P with
  | sourceSource u v huv hfirst hsecond pair => exact pair.second_mem
  | targetTarget u v huv hfirst hsecond pair => exact pair.second_mem
  | oppositeForward u v hfirst hsecond pair => exact pair.second_mem
  | oppositeReverse u v hfirst hsecond pair => exact pair.second_mem

/-- The third displayed factor of the contraction atom lies in the span of the selected
original third factors. -/
theorem qFactors_third_mem {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) :
    P.qFactors.third.1 ∈ Submodule.span F3
      ({(I.factors P.leftIndex).third.1,
        (I.factors P.rightIndex).third.1} : Set (Fin c → F3)) := by
  cases P with
  | sourceSource u v huv hfirst hsecond pair => exact pair.third_mem
  | targetTarget u v huv hfirst hsecond pair => exact pair.third_mem
  | oppositeForward u v hfirst hsecond pair => exact pair.third_mem
  | oppositeReverse u v hfirst hsecond pair => exact pair.third_mem

/-- The actual outer native primitive, with coefficient-correct direction in every placement. -/
theorem outer {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) :
    match P.placement with
    | .sourceSource => NativeReplacement
        (pairState (I.atomAt P.leftIndex) (I.atomAt P.rightIndex)) (singletonState P.q)
    | .targetTarget => NativeReplacement (singletonState P.q)
        (pairState (I.atomAt P.leftIndex) (I.atomAt P.rightIndex))
    | .opposite => NativeReplacement (singletonState (I.atomAt P.leftIndex))
        (pairState (I.atomAt P.rightIndex) P.q) := by
  cases P with
  | sourceSource u v huv hfirst hsecond pair =>
      simp only [placement, leftIndex, rightIndex, q, qFactors,
        DisplayedF3PairTriple.atomAt, DisplayedF3PairTriple.factors]
      rw [← pair.q_eq]
      exact pair.nativeReduction (fun heq => scan.valid.1 (I.atomAt_injective heq))
  | targetTarget u v huv hfirst hsecond pair =>
      simp only [placement, leftIndex, rightIndex, q, qFactors,
        DisplayedF3PairTriple.atomAt, DisplayedF3PairTriple.factors]
      rw [← pair.q_eq]
      exact pair.nativeSplit (fun heq => scan.valid.1 (I.atomAt_injective heq))
  | oppositeForward u v hfirst hsecond pair =>
      have htargetQ : (I.factors scan.candidate.second).atom ≠ pair.q := by
        intro heq
        have hprop := minimalFive_not_proportional I.x I.y I.z I.minimal
          scan.candidate.first scan.candidate.second scan.valid.1 (2 : F3)
        apply hprop
        rw [← DisplayedF3PairTriple.atomAt_val, ← DisplayedF3PairTriple.atomAt_val]
        change (I.factors scan.candidate.first).atom.val =
          (2 : F3) • (I.factors scan.candidate.second).atom.val
        calc
          _ = (I.factors scan.candidate.second).atom.val + pair.q.val := pair.formula.eval_eq
          _ = (I.factors scan.candidate.second).atom.val +
              (I.factors scan.candidate.second).atom.val := by rw [← heq]
          _ = (2 : F3) • (I.factors scan.candidate.second).atom.val := by module
      simp only [placement, leftIndex, rightIndex, q, qFactors,
        DisplayedF3PairTriple.atomAt, DisplayedF3PairTriple.factors]
      rw [← pair.q_eq]
      exact pair.nativeSplit htargetQ
  | oppositeReverse u v hfirst hsecond pair =>
      have htargetQ : (I.factors scan.candidate.first).atom ≠ pair.q := by
        intro heq
        have hprop := minimalFive_not_proportional I.x I.y I.z I.minimal
          scan.candidate.second scan.candidate.first scan.valid.1.symm (2 : F3)
        apply hprop
        rw [← DisplayedF3PairTriple.atomAt_val, ← DisplayedF3PairTriple.atomAt_val]
        change (I.factors scan.candidate.second).atom.val =
          (2 : F3) • (I.factors scan.candidate.first).atom.val
        calc
          _ = (I.factors scan.candidate.first).atom.val + pair.q.val := pair.formula.eval_eq
          _ = (I.factors scan.candidate.first).atom.val +
              (I.factors scan.candidate.first).atom.val := by rw [← heq]
          _ = (2 : F3) • (I.factors scan.candidate.first).atom.val := by module
      simp only [placement, leftIndex, rightIndex, q, qFactors,
        DisplayedF3PairTriple.atomAt, DisplayedF3PairTriple.factors]
      rw [← pair.q_eq]
      exact pair.nativeSplit htargetQ

end EffectiveDisplayedF3PairTriple

/-- Normalize a certified scanned pair in its actual endpoint placement. The construction
uses the scanner's gauge, derives pair independence from five-circuit minimality, and swaps
opposite candidates only to restore the source-to-target direction. -/
def effectiveDisplayedF3PairTriple (I : DisplayedF3PairTriple a b c)
    (scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne) :
    EffectiveDisplayedF3PairTriple I scan := by
  let g := scan.gauge
  have hli : LinearIndependent F3
      ![(I.factors scan.candidate.first).atom.val,
        (I.factors scan.candidate.second).atom.val] := by
    change LinearIndependent F3
      ![productFamily I.x I.y I.z scan.candidate.first,
        productFamily I.x I.y I.z scan.candidate.second]
    exact minimalFive_pair_linearIndependent I.x I.y I.z I.minimal
      scan.candidate.first scan.candidate.second scan.valid.1
  have hnprop : g.VaryingNonproportional := g.varyingNonproportional_of_linearIndependent hli
  cases hleft : I.slots.symm scan.candidate.first with
  | inl u =>
      cases hright : I.slots.symm scan.candidate.second with
      | inl v =>
          have huv : u ≠ v := by
            intro huv
            subst v
            apply scan.valid.1
            calc
              scan.candidate.first = I.slots (I.slots.symm scan.candidate.first) :=
                (I.slots.apply_symm_apply _).symm
              _ = I.slots (.inl u) := congrArg I.slots hleft
              _ = I.slots (I.slots.symm scan.candidate.second) :=
                congrArg I.slots hright.symm
              _ = scan.candidate.second := I.slots.apply_symm_apply _
          exact .sourceSource u v huv
            ((I.slots.apply_symm_apply _).symm.trans (congrArg I.slots hleft))
            ((I.slots.apply_symm_apply _).symm.trans (congrArg I.slots hright))
            (g.sum hnprop)
      | inr v =>
          exact .oppositeForward u v
            ((I.slots.apply_symm_apply _).symm.trans (congrArg I.slots hleft))
            ((I.slots.apply_symm_apply _).symm.trans (congrArg I.slots hright))
            (g.difference hnprop)
  | inr v =>
      cases hright : I.slots.symm scan.candidate.second with
      | inl u =>
          let gs := swapGauge g
          have hliSwap : LinearIndependent F3
              ![(I.factors scan.candidate.second).atom.val,
                (I.factors scan.candidate.first).atom.val] := by
            change LinearIndependent F3
              ![productFamily I.x I.y I.z scan.candidate.second,
                productFamily I.x I.y I.z scan.candidate.first]
            exact minimalFive_pair_linearIndependent I.x I.y I.z I.minimal
              scan.candidate.second scan.candidate.first scan.valid.1.symm
          let hnpropSwap : gs.VaryingNonproportional :=
            gs.varyingNonproportional_of_linearIndependent hliSwap
          exact .oppositeReverse u v
            ((I.slots.apply_symm_apply _).symm.trans (congrArg I.slots hleft))
            ((I.slots.apply_symm_apply _).symm.trans (congrArg I.slots hright))
            (gs.difference hnpropSwap)
      | inr w =>
          have hvw : v ≠ w := by
            intro hvw
            subst w
            apply scan.valid.1
            calc
              scan.candidate.first = I.slots (I.slots.symm scan.candidate.first) :=
                (I.slots.apply_symm_apply _).symm
              _ = I.slots (.inr v) := congrArg I.slots hleft
              _ = I.slots (I.slots.symm scan.candidate.second) :=
                congrArg I.slots hright.symm
              _ = scan.candidate.second := I.slots.apply_symm_apply _
          exact .targetTarget v w hvw
            ((I.slots.apply_symm_apply _).symm.trans (congrArg I.slots hleft))
            ((I.slots.apply_symm_apply _).symm.trans (congrArg I.slots hright))
            (g.sum hnprop)

/-- The displayed endpoint ordering as a permutation of five logical slots. -/
def DisplayedF3PairTriple.logicalSlots (I : DisplayedF3PairTriple a b c) :
    Equiv.Perm (Fin 5) := finSumFinEquiv.symm.trans I.slots

/-- A contraction split computed in logical endpoint coordinates before applying the user's
arbitrary displayed-slot equivalence. -/
def EffectiveDisplayedF3PairTriple.normalizedSplit
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) : Fin 2 ⊕ Fin 3 ≃ Fin 5 :=
  (pairFrontSplit
    (finSumFinEquiv (I.slots.symm P.leftIndex))
    (finSumFinEquiv (I.slots.symm P.rightIndex))).trans I.logicalSlots

@[simp] theorem EffectiveDisplayedF3PairTriple.normalizedSplit_left_zero
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) :
    P.normalizedSplit (.inl 0) = P.leftIndex := by
  simp [EffectiveDisplayedF3PairTriple.normalizedSplit,
    DisplayedF3PairTriple.logicalSlots, pairFrontSplit_left_zero,
    P.indices_ne]

@[simp] theorem EffectiveDisplayedF3PairTriple.normalizedSplit_left_one
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) :
    P.normalizedSplit (.inl 1) = P.rightIndex := by
  simp [EffectiveDisplayedF3PairTriple.normalizedSplit,
    DisplayedF3PairTriple.logicalSlots, pairFrontSplit_left_one,
    P.indices_ne]

/-- Coefficient-correct contraction data for an endpoint-aware normalized pair. -/
def EffectiveDisplayedF3PairTriple.contraction
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) :
    ContractionData F3 (productFamily I.x I.y I.z) := {
  split := P.normalizedSplit
  q := P.q.val
  leftScale := 1
  rightScale := match P.placement with | .opposite => -1 | _ => 1
  originalCoefficients := I.coefficient
  residualCoefficients := Fin.cases (I.coefficient P.leftIndex)
    (fun j => I.coefficient (P.normalizedSplit (.inr j)))
  q_eq := by
    cases P <;>
      simp_all [EffectiveDisplayedF3PairTriple.q_val_eq,
        EffectiveDisplayedF3PairTriple.placement,
        EffectiveDisplayedF3PairTriple.leftIndex,
        EffectiveDisplayedF3PairTriple.rightIndex,
        DisplayedF3PairTriple.atomAt_val]
  original_relation := I.signed_relation
  originalCoefficients_ne_zero := by
    intro hz
    have hslot := congrFun hz (I.slots (.inl 0))
    simpa only [DisplayedF3PairTriple.coefficient, I.slots.symm_apply_apply,
      Pi.zero_apply, one_ne_zero] using hslot
  match_left := by
    rw [P.normalizedSplit_left_zero]
    change I.coefficient P.leftIndex = I.coefficient P.leftIndex * 1
    exact (mul_one _).symm
  match_right := by
    rw [P.normalizedSplit_left_one]
    cases P with
    | sourceSource u v huv hfirst hsecond pair =>
        simp [EffectiveDisplayedF3PairTriple.placement,
          EffectiveDisplayedF3PairTriple.leftIndex,
          EffectiveDisplayedF3PairTriple.rightIndex,
          DisplayedF3PairTriple.coefficient, hfirst, hsecond]
    | targetTarget u v huv hfirst hsecond pair =>
        simp [EffectiveDisplayedF3PairTriple.placement,
          EffectiveDisplayedF3PairTriple.leftIndex,
          EffectiveDisplayedF3PairTriple.rightIndex,
          DisplayedF3PairTriple.coefficient, hfirst, hsecond]
    | oppositeForward u v hfirst hsecond pair =>
        simp [EffectiveDisplayedF3PairTriple.placement,
          EffectiveDisplayedF3PairTriple.leftIndex,
          EffectiveDisplayedF3PairTriple.rightIndex,
          DisplayedF3PairTriple.coefficient, hfirst, hsecond]
    | oppositeReverse u v hfirst hsecond pair =>
        simp [EffectiveDisplayedF3PairTriple.placement,
          EffectiveDisplayedF3PairTriple.leftIndex,
          EffectiveDisplayedF3PairTriple.rightIndex,
          DisplayedF3PairTriple.coefficient, hfirst, hsecond]
  match_rest := by intro j; rfl }

@[simp] theorem EffectiveDisplayedF3PairTriple.contraction_residualCoefficients_zero
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) :
    P.contraction.residualCoefficients 0 = I.coefficient P.leftIndex := rfl

@[simp] theorem EffectiveDisplayedF3PairTriple.contraction_residualCoefficients_succ
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) (j : Fin 3) :
    P.contraction.residualCoefficients j.succ =
      I.coefficient (P.normalizedSplit (.inr j)) := rfl

/-- The contraction atom is nonzero, derived from five-circuit minimality. -/
theorem EffectiveDisplayedF3PairTriple.q_ne_zero
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) : P.q.val ≠ 0 := by
  simpa only [EffectiveDisplayedF3PairTriple.contraction] using
    P.contraction.q_ne_zero (minimalFive_vanishingRelation I.x I.y I.z I.minimal)

/-- The contraction atom is outside every original endpoint ray. -/
theorem EffectiveDisplayedF3PairTriple.q_not_proportional
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) (i : Fin 5) :
    Nonproportional (k := F3) P.q.val (I.atomAt i).val := by
  simpa only [EffectiveDisplayedF3PairTriple.contraction,
    DisplayedF3PairTriple.atomAt_val] using
    P.contraction.q_not_proportional
      (minimalFive_vanishingRelation I.x I.y I.z I.minimal) i

/-- The residual four-family is minimally dependent with its actual coefficients. -/
theorem EffectiveDisplayedF3PairTriple.residual_minimal
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) :
    IsMinimalFourCircuit (k := F3) P.contraction.residualFamily :=
  P.contraction.residual_isMinimalFourCircuit
    (minimalFive_vanishingRelation I.x I.y I.z I.minimal)

/-- A computable permutation moving two distinct residual positions to positions zero and one. -/
def pairFrontPerm4 (i j : Fin 4) : Equiv.Perm (Fin 4) :=
  (Equiv.swap 1 ((Equiv.swap 0 i) j)).trans (Equiv.swap 0 i)

/-- Canonical residual reindexing for the target/target placement. -/
def targetTargetResidualReindex (u v : Fin 3) : Equiv.Perm (Fin 4) :=
  if u = 0 then
    if v = 1 then pairFrontPerm4 1 2 else pairFrontPerm4 1 3
  else if u = 1 then
    if v = 0 then pairFrontPerm4 1 2 else pairFrontPerm4 2 3
  else if v = 0 then pairFrontPerm4 1 3 else pairFrontPerm4 2 3

/-- Reindex the actual contraction residual into its signed endpoint order. -/
def EffectiveDisplayedF3PairTriple.residualReindex
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) : Equiv.Perm (Fin 4) :=
  match P with
  | .sourceSource .. => Equiv.refl _
  | .targetTarget u v .. => targetTargetResidualReindex u v
  | .oppositeForward _ v .. => Equiv.swap 1 v.succ
  | .oppositeReverse _ v .. => Equiv.swap 1 v.succ

/-- The endpoint shape of the normalized contraction. Opposite placement leaves the contraction
atom and one source against the two uncontracted targets, hence is also two-versus-two. -/
def EffectiveDisplayedF3PairTriple.residualShape
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) : FourFamilyShape :=
  match P.placement with
  | .sourceSource => .oneThree
  | .targetTarget | .opposite => .twoTwo

/-- The signed coefficient attached to one logical displayed endpoint slot. -/
def logicalCoefficient : Fin 2 ⊕ Fin 3 → F3
  | .inl _ => 1
  | .inr _ => -1

/-- The logical endpoint slot occupying `z` after bringing `x,y` to the contraction front. -/
def logicalSlotAfterPairFront (x y z : Fin 2 ⊕ Fin 3) : Fin 2 ⊕ Fin 3 :=
  finSumFinEquiv.symm (pairFrontSplit (finSumFinEquiv x) (finSumFinEquiv y) z)

/-- Displayed coefficients reduce to their logical endpoint sign. -/
@[simp] theorem DisplayedF3PairTriple.coefficient_slots
    (I : DisplayedF3PairTriple a b c) (x : Fin 2 ⊕ Fin 3) :
    I.coefficient (I.slots x) = logicalCoefficient x := by
  cases x <;> simp [DisplayedF3PairTriple.coefficient, logicalCoefficient]

/-- A normalized split can be evaluated through logical endpoint coordinates without reducing
constructor equality proofs. -/
theorem EffectiveDisplayedF3PairTriple.coefficient_normalizedSplit_of_indices
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan)
    {x y : Fin 2 ⊕ Fin 3}
    (hleft : P.leftIndex = I.slots x)
    (hright : P.rightIndex = I.slots y)
    (z : Fin 2 ⊕ Fin 3) :
    I.coefficient (P.normalizedSplit z) =
      logicalCoefficient (logicalSlotAfterPairFront x y z) := by
  unfold EffectiveDisplayedF3PairTriple.normalizedSplit
    DisplayedF3PairTriple.logicalSlots logicalSlotAfterPairFront
  simp only [Equiv.trans_apply, hleft, hright, Equiv.symm_apply_apply,
    DisplayedF3PairTriple.coefficient_slots]

/-- Contraction residual coefficients can be computed entirely in logical endpoint coordinates. -/
theorem EffectiveDisplayedF3PairTriple.contraction_residualCoefficients_of_indices
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan)
    {x y : Fin 2 ⊕ Fin 3}
    (hleft : P.leftIndex = I.slots x)
    (hright : P.rightIndex = I.slots y)
    (i : Fin 4) :
    P.contraction.residualCoefficients i =
      Fin.cases (logicalCoefficient x)
        (fun j => logicalCoefficient (logicalSlotAfterPairFront x y (.inr j))) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [EffectiveDisplayedF3PairTriple.contraction_residualCoefficients_zero,
      hleft, DisplayedF3PairTriple.coefficient_slots]
    rfl
  · rw [EffectiveDisplayedF3PairTriple.contraction_residualCoefficients_succ]
    exact P.coefficient_normalizedSplit_of_indices hleft hright (.inr j)

/-- Actual contraction coefficients agree with the canonical signed coefficients after the
explicit endpoint-aware residual permutation. -/
theorem EffectiveDisplayedF3PairTriple.residual_coefficients_reindex
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) (i : Fin 4) :
    P.contraction.residualCoefficients (P.residualReindex i) =
      signedFourCoefficients (k := F3) P.residualShape i := by
  cases P with
  | sourceSource u v huv hfirst hsecond pair =>
      let P : EffectiveDisplayedF3PairTriple I scan :=
        .sourceSource u v huv hfirst hsecond pair
      change P.contraction.residualCoefficients (P.residualReindex i) =
        signedFourCoefficients P.residualShape i
      have hleft : P.leftIndex = I.slots (.inl u) := by
        change scan.candidate.first = I.slots (.inl u)
        exact hfirst
      have hright : P.rightIndex = I.slots (.inl v) := by
        change scan.candidate.second = I.slots (.inl v)
        exact hsecond
      rw [P.contraction_residualCoefficients_of_indices hleft hright]
      dsimp [P, EffectiveDisplayedF3PairTriple.residualReindex,
        EffectiveDisplayedF3PairTriple.residualShape,
        EffectiveDisplayedF3PairTriple.placement]
      fin_cases u <;> fin_cases v <;> fin_cases i <;>
        first | omega | decide
  | targetTarget u v huv hfirst hsecond pair =>
      let P : EffectiveDisplayedF3PairTriple I scan :=
        .targetTarget u v huv hfirst hsecond pair
      change P.contraction.residualCoefficients (P.residualReindex i) =
        signedFourCoefficients P.residualShape i
      have hleft : P.leftIndex = I.slots (.inr u) := by
        change scan.candidate.first = I.slots (.inr u)
        exact hfirst
      have hright : P.rightIndex = I.slots (.inr v) := by
        change scan.candidate.second = I.slots (.inr v)
        exact hsecond
      rw [P.contraction_residualCoefficients_of_indices hleft hright]
      dsimp [P, EffectiveDisplayedF3PairTriple.residualReindex,
        EffectiveDisplayedF3PairTriple.residualShape,
        EffectiveDisplayedF3PairTriple.placement]
      fin_cases u <;> fin_cases v <;> fin_cases i <;>
        first | omega | decide
  | oppositeForward u v hfirst hsecond pair =>
      let P : EffectiveDisplayedF3PairTriple I scan :=
        .oppositeForward u v hfirst hsecond pair
      change P.contraction.residualCoefficients (P.residualReindex i) =
        signedFourCoefficients P.residualShape i
      have hleft : P.leftIndex = I.slots (.inl u) := by
        change scan.candidate.first = I.slots (.inl u)
        exact hfirst
      have hright : P.rightIndex = I.slots (.inr v) := by
        change scan.candidate.second = I.slots (.inr v)
        exact hsecond
      rw [P.contraction_residualCoefficients_of_indices hleft hright]
      dsimp [P, EffectiveDisplayedF3PairTriple.residualReindex,
        EffectiveDisplayedF3PairTriple.residualShape,
        EffectiveDisplayedF3PairTriple.placement]
      fin_cases u <;> fin_cases v <;> fin_cases i <;>
        first | omega | decide
  | oppositeReverse u v hfirst hsecond pair =>
      let P : EffectiveDisplayedF3PairTriple I scan :=
        .oppositeReverse u v hfirst hsecond pair
      change P.contraction.residualCoefficients (P.residualReindex i) =
        signedFourCoefficients P.residualShape i
      have hleft : P.leftIndex = I.slots (.inl u) := by
        change scan.candidate.second = I.slots (.inl u)
        exact hsecond
      have hright : P.rightIndex = I.slots (.inr v) := by
        change scan.candidate.first = I.slots (.inr v)
        exact hfirst
      rw [P.contraction_residualCoefficients_of_indices hleft hright]
      dsimp [P, EffectiveDisplayedF3PairTriple.residualReindex,
        EffectiveDisplayedF3PairTriple.residualShape,
        EffectiveDisplayedF3PairTriple.placement]
      fin_cases u <;> fin_cases v <;> fin_cases i <;>
        first | omega | decide

/-- The coefficient-correct residual in canonical one/three or two/two endpoint order. -/
def EffectiveDisplayedF3PairTriple.signedResidual
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) :
    SignedMinimalFour F3 (Tensor F3 a b c) :=
  P.contraction.signedMinimalFour
    (minimalFive_vanishingRelation I.x I.y I.z I.minimal)
    P.residualReindex P.residualShape P.residual_coefficients_reindex

/-- The actual rank-one atoms underlying the unpermuted contraction residual. -/
def EffectiveDisplayedF3PairTriple.residualAtomFamily
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) : Fin 4 → Atom F3 a b c :=
  Fin.cases P.q (fun j => I.atomAt (P.normalizedSplit (.inr j)))

/-- Evaluation of the residual atom family is the contraction residual tensor family. -/
@[simp] theorem EffectiveDisplayedF3PairTriple.residualAtomFamily_val
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) (i : Fin 4) :
    (P.residualAtomFamily i).val = P.contraction.residualFamily i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

/-- The actual rank-one atoms in canonical signed endpoint order. -/
def EffectiveDisplayedF3PairTriple.signedResidualAtom
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) (i : Fin 4) : Atom F3 a b c :=
  P.residualAtomFamily (P.residualReindex i)

/-- Atom evaluation identifies the canonical atom family with the terms of the signed residual. -/
@[simp] theorem EffectiveDisplayedF3PairTriple.signedResidualAtom_val
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) (i : Fin 4) :
    (P.signedResidualAtom i).val = P.signedResidual.term i := by
  change (P.residualAtomFamily (P.residualReindex i)).val =
    P.contraction.residualFamily (P.residualReindex i)
  exact P.residualAtomFamily_val (P.residualReindex i)

/-- The signed index occupied by the contraction atom. -/
def EffectiveDisplayedF3PairTriple.qSignedIndex
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) : Fin 4 := P.residualReindex.symm 0

/-- The calculated signed residual position really contains the contraction atom. -/
@[simp] theorem EffectiveDisplayedF3PairTriple.signedResidualAtom_qSignedIndex
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) :
    P.signedResidualAtom P.qSignedIndex = P.q := by
  simp [EffectiveDisplayedF3PairTriple.signedResidualAtom,
    EffectiveDisplayedF3PairTriple.qSignedIndex,
    EffectiveDisplayedF3PairTriple.residualAtomFamily]

/-- The source state of the canonical signed four-family. -/
noncomputable def EffectiveDisplayedF3PairTriple.signedResidualSource
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) : State F3 a b c :=
  match P.residualShape with
  | .oneThree => singletonState (P.signedResidualAtom 0)
  | .twoTwo => pairState (P.signedResidualAtom 0) (P.signedResidualAtom 1)

/-- The target state of the canonical signed four-family. -/
noncomputable def EffectiveDisplayedF3PairTriple.signedResidualTarget
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) : State F3 a b c :=
  match P.residualShape with
  | .oneThree => tripleState (P.signedResidualAtom 1)
      (P.signedResidualAtom 2) (P.signedResidualAtom 3)
  | .twoTwo => pairState (P.signedResidualAtom 2) (P.signedResidualAtom 3)

/-- Total scanner-driven five-to-four data. The candidate and gauge cannot be selected by the
caller: both are produced by `certifiedScanGauge`. -/
structure CertifiedFiveToFour (I : DisplayedF3PairTriple a b c) where
  scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne
  normalized : EffectiveDisplayedF3PairTriple I scan

/-- Run the bounded certified scan and normalize its actual pair by endpoint placement. -/
def certifiedFiveToFour (I : DisplayedF3PairTriple a b c) : CertifiedFiveToFour I := by
  let scan := certifiedScanGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne I.minimal
  exact ⟨scan, effectiveDisplayedF3PairTriple I scan⟩

namespace CertifiedFiveToFour

/-- The actual rank-one contraction factors. -/
def qFactors {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I) :
    FactorTriple F3 a b c := B.normalized.qFactors

/-- The actual contraction atom. -/
def q {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I) :
    Atom F3 a b c := B.normalized.q

/-- The coefficient-correct residual family, with the contraction atom first. -/
def residualFamily {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I) :
    Fin 4 → Tensor F3 a b c := B.normalized.contraction.residualFamily

/-- The canonical signed residual, reindexed into its actual one/three or two/two endpoint
shape. -/
def signedResidual {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I) :
    SignedMinimalFour F3 (Tensor F3 a b c) := B.normalized.signedResidual

/-- The canonical signed residual term is the actual contraction residual under the explicit
endpoint permutation. -/
@[simp] theorem signedResidual_term {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (i : Fin 4) :
    B.signedResidual.term i = B.residualFamily (B.normalized.residualReindex i) := rfl

/-- The shape recorded by the canonical signed residual is the placement-computed shape. -/
@[simp] theorem signedResidual_shape {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) :
    B.signedResidual.shape = B.normalized.residualShape := rfl

/-- The actual rank-one atom at one canonical signed residual position. -/
def signedResidualAtom {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (i : Fin 4) : Atom F3 a b c :=
  B.normalized.signedResidualAtom i

/-- The canonical signed position occupied by the contraction atom. -/
def qSignedIndex {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I) : Fin 4 :=
  B.normalized.qSignedIndex

/-- The calculated canonical position really contains the scanner-driven contraction atom. -/
@[simp] theorem signedResidualAtom_qSignedIndex {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) : B.signedResidualAtom B.qSignedIndex = B.q :=
  B.normalized.signedResidualAtom_qSignedIndex

/-- The canonical residual source state determined by the actual signed shape. -/
noncomputable def signedResidualSource {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) : State F3 a b c := B.normalized.signedResidualSource

/-- The canonical residual target state determined by the actual signed shape. -/
noncomputable def signedResidualTarget {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) : State F3 a b c := B.normalized.signedResidualTarget

/-- Atom evaluation identifies the B-level canonical atom family with its signed terms. -/
@[simp] theorem signedResidualAtom_val {I : DisplayedF3PairTriple a b c}
    (B : CertifiedFiveToFour I) (i : Fin 4) :
    (B.signedResidualAtom i).val = B.signedResidual.term i :=
  B.normalized.signedResidualAtom_val i

/-- The first factor of the B-level contraction atom lies in the selected original-factor
span. -/
theorem qFactors_first_mem {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I) :
    B.qFactors.first.1 ∈ Submodule.span F3
      ({(I.factors B.normalized.leftIndex).first.1,
        (I.factors B.normalized.rightIndex).first.1} : Set (Fin a → F3)) :=
  B.normalized.qFactors_first_mem

/-- The second factor of the B-level contraction atom lies in the selected original-factor
span. -/
theorem qFactors_second_mem {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I) :
    B.qFactors.second.1 ∈ Submodule.span F3
      ({(I.factors B.normalized.leftIndex).second.1,
        (I.factors B.normalized.rightIndex).second.1} : Set (Fin b → F3)) :=
  B.normalized.qFactors_second_mem

/-- The third factor of the B-level contraction atom lies in the selected original-factor
span. -/
theorem qFactors_third_mem {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I) :
    B.qFactors.third.1 ∈ Submodule.span F3
      ({(I.factors B.normalized.leftIndex).third.1,
        (I.factors B.normalized.rightIndex).third.1} : Set (Fin c → F3)) :=
  B.normalized.qFactors_third_mem

/-- The scanner-driven contraction atom is nonzero. -/
theorem q_ne_zero {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I) :
    B.q.val ≠ 0 := B.normalized.q_ne_zero

/-- The scanner-driven residual family is minimally dependent. -/
theorem residual_minimal {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I) :
    IsMinimalFourCircuit (k := F3) B.residualFamily := B.normalized.residual_minimal

/-- The checked outer native primitive in its endpoint-correct direction. -/
theorem outer {I : DisplayedF3PairTriple a b c} (B : CertifiedFiveToFour I) :
    match B.normalized.placement with
    | .sourceSource => NativeReplacement
        (pairState (I.atomAt B.normalized.leftIndex) (I.atomAt B.normalized.rightIndex))
        (singletonState B.q)
    | .targetTarget => NativeReplacement
        (singletonState B.q)
        (pairState (I.atomAt B.normalized.leftIndex) (I.atomAt B.normalized.rightIndex))
    | .opposite => NativeReplacement
        (singletonState (I.atomAt B.normalized.leftIndex))
        (pairState (I.atomAt B.normalized.rightIndex) B.q) :=
  B.normalized.outer

end CertifiedFiveToFour

end FieldFiveToFour
end BilinearComplexity
