import BilinearComplexity.FieldCircuitContraction
import BilinearComplexity.FieldNativePairBridge
import BilinearComplexity.FieldThreeProductCircuit
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module

set_option autoImplicit false

open scoped BigOperators

namespace BilinearComplexity
namespace FieldFiveToFour

open FieldRankOne FieldContextual FieldNativeMoves FieldNativePath
open FieldFiveCircuitProfile FieldCircuitContraction FieldNativePairBridge

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

/-- Coefficient-correct contraction data for an endpoint-aware normalized pair. -/
def EffectiveDisplayedF3PairTriple.contraction
    {I : DisplayedF3PairTriple a b c}
    {scan : ScannedPairGauge I.x I.y I.z I.x_ne I.y_ne I.z_ne}
    (P : EffectiveDisplayedF3PairTriple I scan) :
    ContractionData F3 (productFamily I.x I.y I.z) := {
  split := pairFrontSplit P.leftIndex P.rightIndex
  q := P.q.val
  leftScale := 1
  rightScale := match P.placement with | .opposite => -1 | _ => 1
  originalCoefficients := I.coefficient
  residualCoefficients := Fin.cases (I.coefficient P.leftIndex)
    (fun j => I.coefficient (pairFrontSplit P.leftIndex P.rightIndex (.inr j)))
  q_eq := by
    cases P <;>
      simp_all [EffectiveDisplayedF3PairTriple.q_val_eq,
        EffectiveDisplayedF3PairTriple.placement,
        EffectiveDisplayedF3PairTriple.leftIndex,
        EffectiveDisplayedF3PairTriple.rightIndex,
        pairFrontSplit_left_zero, pairFrontSplit_left_one,
        DisplayedF3PairTriple.atomAt_val]
  original_relation := I.signed_relation
  originalCoefficients_ne_zero := by
    intro hz
    have hslot := congrFun hz (I.slots (.inl 0))
    simpa only [DisplayedF3PairTriple.coefficient, I.slots.symm_apply_apply,
      Pi.zero_apply, one_ne_zero] using hslot
  match_left := by
    rw [pairFrontSplit_left_zero P.leftIndex P.rightIndex P.indices_ne]
    change I.coefficient P.leftIndex = I.coefficient P.leftIndex * 1
    exact (mul_one _).symm
  match_right := by
    rw [pairFrontSplit_left_one P.leftIndex P.rightIndex P.indices_ne]
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
