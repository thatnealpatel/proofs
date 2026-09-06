import BilinearComplexity.FieldNativePath
import BilinearComplexity.FieldTernaryFiveCircuitPair
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace BilinearComplexity
namespace FieldNativePairBridge

open FieldRankOne FieldContextual FieldNativeMoves FieldNativePath

variable {k : Type*} {a b c : ℕ} [Field k]

/-- Effective nonzero factors displaying one rank-one atom. -/
structure FactorTriple (k : Type*) [Field k] (a b c : ℕ) where
  /-- First factor. -/
  first : Factor k a
  /-- Second factor. -/
  second : Factor k b
  /-- Third factor. -/
  third : Factor k c

namespace FactorTriple

/-- The semantic atom evaluated by a displayed factor triple. -/
def atom (p : FactorTriple k a b c) : Atom k a b c :=
  FieldNativeMoves.atom p.first p.second p.third

/-- The displayed atom evaluates to the product of its displayed factors. -/
@[simp] theorem atom_val (p : FactorTriple k a b c) :
    p.atom.val = evalFactors 1 p.first.1 p.second.1 p.third.1 := rfl

end FactorTriple

/-- Checked scalar gauges saying that two displayed atoms share two factor rays.
The orientation records exactly which factor remains variable. -/
inductive PairGauge (p r : FactorTriple k a b c) : Type _
  | xy (firstScalar secondScalar : k)
      (firstScalar_ne : firstScalar ≠ 0) (secondScalar_ne : secondScalar ≠ 0)
      (first_eq : p.first.1 = firstScalar • r.first.1)
      (second_eq : p.second.1 = secondScalar • r.second.1) : PairGauge p r
  | xz (firstScalar thirdScalar : k)
      (firstScalar_ne : firstScalar ≠ 0) (thirdScalar_ne : thirdScalar ≠ 0)
      (first_eq : p.first.1 = firstScalar • r.first.1)
      (third_eq : p.third.1 = thirdScalar • r.third.1) : PairGauge p r
  | yz (secondScalar thirdScalar : k)
      (secondScalar_ne : secondScalar ≠ 0) (thirdScalar_ne : thirdScalar ≠ 0)
      (second_eq : p.second.1 = secondScalar • r.second.1)
      (third_eq : p.third.1 = thirdScalar • r.third.1) : PairGauge p r

/-- Bundle one displayed slot into effective nonzero factor data. -/
def factorTripleAt (x : Fin 5 → Fin a → k) (y : Fin 5 → Fin b → k)
    (z : Fin 5 → Fin c → k) (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (hz : ∀ i, z i ≠ 0) (i : Fin 5) : FactorTriple k a b c :=
  ⟨⟨x i, hx i⟩, ⟨y i, hy i⟩, ⟨z i, hz i⟩⟩

/-- Bundling a displayed slot preserves its three factor functions definitionally. -/
theorem factorTripleAt_factors (x : Fin 5 → Fin a → k) (y : Fin 5 → Fin b → k)
    (z : Fin 5 → Fin c → k) (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (hz : ∀ i, z i ≠ 0) (i : Fin 5) :
    (factorTripleAt x y z hx hy hz i).first.1 = x i ∧
      (factorTripleAt x y z hx hy hz i).second.1 = y i ∧
      (factorTripleAt x y z hx hy hz i).third.1 = z i := by
  exact ⟨rfl, rfl, rfl⟩

/-- Convert one valid ternary scan candidate into checked native pair gauges without choosing
new representatives. The candidate's actual two scalars are retained. -/
def candidateGauge {a b c : ℕ}
    (x : Fin 5 → Fin a → FieldTernaryFiveCircuitPair.F3)
    (y : Fin 5 → Fin b → FieldTernaryFiveCircuitPair.F3)
    (z : Fin 5 → Fin c → FieldTernaryFiveCircuitPair.F3)
    (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0) (hz : ∀ i, z i ≠ 0)
    (candidate : FieldTernaryFiveCircuitPair.Candidate)
    (hvalid : candidate.Valid x y z) :
    PairGauge (factorTripleAt x y z hx hy hz candidate.first)
      (factorTripleAt x y z hx hy hz candidate.second) := by
  rcases hvalid with ⟨_hindices, _hfirst, _hsecond, hs, ht, hrelations⟩
  cases ho : candidate.orientation with
  | xy =>
      rw [ho] at hrelations
      exact .xy candidate.firstScalar candidate.secondScalar hs ht hrelations.1 hrelations.2
  | xz =>
      rw [ho] at hrelations
      exact .xz candidate.firstScalar candidate.secondScalar hs ht hrelations.1 hrelations.2
  | yz =>
      rw [ho] at hrelations
      exact .yz candidate.firstScalar candidate.secondScalar hs ht hrelations.1 hrelations.2

/-- Effective scan output together with its directly usable native pair gauge. -/
structure ScannedPairGauge {a b c : ℕ}
    (x : Fin 5 → Fin a → FieldTernaryFiveCircuitPair.F3)
    (y : Fin 5 → Fin b → FieldTernaryFiveCircuitPair.F3)
    (z : Fin 5 → Fin c → FieldTernaryFiveCircuitPair.F3)
    (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0) (hz : ∀ i, z i ≠ 0) where
  /-- Candidate selected by the existing bounded scan. -/
  candidate : FieldTernaryFiveCircuitPair.Candidate
  /-- Kernel-checked validity of the selected candidate. -/
  valid : candidate.Valid x y z
  /-- Native pair gauge built from the displayed factors and actual scanned scalars. -/
  gauge : PairGauge (factorTripleAt x y z hx hy hz candidate.first)
    (factorTripleAt x y z hx hy hz candidate.second)

/-- Run the existing total certified scan and normalize its checked scalar equalities into a
native pair gauge. No pair, `q`, basis, or gauge oracle is supplied by the caller. -/
def certifiedScanGauge {a b c : ℕ}
    (x : Fin 5 → Fin a → FieldTernaryFiveCircuitPair.F3)
    (y : Fin 5 → Fin b → FieldTernaryFiveCircuitPair.F3)
    (z : Fin 5 → Fin c → FieldTernaryFiveCircuitPair.F3)
    (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0) (hz : ∀ i, z i ≠ 0)
    (hminimal : FieldFiveCircuitProfile.IsMinimalFiveProductCircuit x y z) :
    ScannedPairGauge x y z hx hy hz := by
  let scan := FieldTernaryFiveCircuitPair.certifiedScan x y z hx hy hz hminimal
  exact {
    candidate := scan.1
    valid := scan.2
    gauge := candidateGauge x y z hx hy hz scan.1 scan.2 }


/-- The permitted side condition: the one unshared displayed factor pair is nonproportional.
It implies both the normalized sum and normalized difference factors are nonzero. -/
def PairGauge.VaryingNonproportional {p r : FactorTriple k a b c}
    (g : PairGauge p r) : Prop :=
  match g with
  | .xy _ _ _ _ _ _ => ∀ t : k, p.third.1 ≠ t • r.third.1
  | .xz _ _ _ _ _ _ => ∀ t : k, p.second.1 ≠ t • r.second.1
  | .yz _ _ _ _ _ _ => ∀ t : k, p.first.1 ≠ t • r.first.1

/-- Nonproportionality of the two semantic atoms forces nonproportionality in the
one varying displayed factor mode selected by any checked two-ray gauge. -/
theorem PairGauge.varyingNonproportional_of_atom {p r : FactorTriple k a b c}
    (g : PairGauge p r) (hatom : ∀ s : k, p.atom.val ≠ s • r.atom.val) :
    g.VaryingNonproportional := by
  cases g with
  | xy s t hs ht hfirst hsecond =>
      intro u hthird
      apply hatom (s * t * u)
      funext i j l
      simp only [FactorTriple.atom_val, evalFactors, one_mul, hfirst, hsecond, hthird,
        Pi.smul_apply, smul_eq_mul]
      ring
  | xz s t hs ht hfirst hthird =>
      intro u hsecond
      apply hatom (s * t * u)
      funext i j l
      simp only [FactorTriple.atom_val, evalFactors, one_mul, hfirst, hsecond, hthird,
        Pi.smul_apply, smul_eq_mul]
      ring
  | yz s t hs ht hsecond hthird =>
      intro u hfirst
      apply hatom (s * t * u)
      funext i j l
      simp only [FactorTriple.atom_val, evalFactors, one_mul, hfirst, hsecond, hthird,
        Pi.smul_apply, smul_eq_mul]
      ring

/-- Linear independence of the semantic atom pair supplies the same varying-factor
nonproportionality condition without exposing gauge normalization algebra to callers. -/
theorem PairGauge.varyingNonproportional_of_linearIndependent
    {p r : FactorTriple k a b c} (g : PairGauge p r)
    (hli : LinearIndependent k ![p.atom.val, r.atom.val]) : g.VaryingNonproportional := by
  apply g.varyingNonproportional_of_atom
  intro s heq
  have hzero : (1 : k) • p.atom.val + (-s) • r.atom.val = 0 := by
    rw [one_smul, heq, neg_smul, add_neg_cancel]
  exact one_ne_zero (hli.eq_zero_of_pair hzero).1

/-- The named nonproportionality condition unfolds to the varying third-factor condition
for an `xy` gauge. -/
theorem PairGauge.varyingNonproportional_xy_iff {p r : FactorTriple k a b c}
    {s t : k} {hs : s ≠ 0} {ht : t ≠ 0}
    {hfirst : p.first.1 = s • r.first.1}
    {hsecond : p.second.1 = t • r.second.1} :
    (PairGauge.xy (p := p) (r := r) s t hs ht hfirst hsecond).VaryingNonproportional ↔
      ∀ u : k, p.third.1 ≠ u • r.third.1 := by
  rfl


/-- A normalized sum pair stores the constructed factor data, semantic atom, exact native
formula, and membership of every new factor in the corresponding original pair span. -/
structure SumPair (p r : FactorTriple k a b c) where
  /-- The effectively constructed factors for the sum atom. -/
  qFactors : FactorTriple k a b c
  /-- The effectively constructed semantic sum atom. -/
  q : Atom k a b c
  /-- The semantic atom is exactly the displayed new factor triple. -/
  q_eq : q = qFactors.atom
  /-- The exact one-to-two native formula `q → p+r`. -/
  formula : SplitFormula q p.atom r.atom
  /-- Exact evaluated sum, recorded independently of the formula representation. -/
  eval_eq : q.val = p.atom.val + r.atom.val
  /-- The new first factor stays in the original first-factor pair span. -/
  first_mem : qFactors.first.1 ∈ Submodule.span k ({p.first.1, r.first.1} : Set (Fin a → k))
  /-- The new second factor stays in the original second-factor pair span. -/
  second_mem : qFactors.second.1 ∈ Submodule.span k ({p.second.1, r.second.1} : Set (Fin b → k))
  /-- The new third factor stays in the original third-factor pair span. -/
  third_mem : qFactors.third.1 ∈ Submodule.span k ({p.third.1, r.third.1} : Set (Fin c → k))

/-- A normalized difference pair stores the constructed `q = p-r` data and, with the
actual signs, the native Split formula `p → r+q`. -/
structure DifferencePair (p r : FactorTriple k a b c) where
  /-- The effectively constructed factors for the difference atom. -/
  qFactors : FactorTriple k a b c
  /-- The effectively constructed semantic difference atom. -/
  q : Atom k a b c
  /-- The semantic atom is exactly the displayed new factor triple. -/
  q_eq : q = qFactors.atom
  /-- The exact opposite-side native formula `p → r+q`. -/
  formula : SplitFormula p.atom r.atom q
  /-- Exact evaluated difference with genuine field subtraction. -/
  eval_eq : q.val = p.atom.val - r.atom.val
  /-- The new first factor stays in the original first-factor pair span. -/
  first_mem : qFactors.first.1 ∈ Submodule.span k ({p.first.1, r.first.1} : Set (Fin a → k))
  /-- The new second factor stays in the original second-factor pair span. -/
  second_mem : qFactors.second.1 ∈ Submodule.span k ({p.second.1, r.second.1} : Set (Fin b → k))
  /-- The new third factor stays in the original third-factor pair span. -/
  third_mem : qFactors.third.1 ∈ Submodule.span k ({p.third.1, r.third.1} : Set (Fin c → k))

/-- Effectively rescale a nonzero factor by a checked nonzero scalar. -/
def scaleFactor (s : k) (hs : s ≠ 0) (u : Factor k a) : Factor k a :=
  ⟨s • u.1, smul_ne_zero hs u.2⟩

/-- Scaling by one leaves a bundled factor unchanged. -/
@[simp] theorem scaleFactor_one (u : Factor k a) : scaleFactor 1 one_ne_zero u = u := by
  apply Subtype.ext
  simp only [scaleFactor, one_smul]

private theorem scaled_add_ne_zero {n : ℕ} (x y : Factor k n) (s : k) (hs : s ≠ 0)
    (hnprop : ∀ t : k, x.1 ≠ t • y.1) : s • x.1 + y.1 ≠ 0 := by
  intro hzero
  apply hnprop (-s⁻¹)
  have hscaled : s • x.1 = -y.1 := eq_neg_of_add_eq_zero_left hzero
  calc
    x.1 = (s⁻¹ * s) • x.1 := by rw [inv_mul_cancel₀ hs, one_smul]
    _ = s⁻¹ • (s • x.1) := by rw [smul_smul]
    _ = s⁻¹ • (-y.1) := by rw [hscaled]
    _ = (-s⁻¹) • y.1 := by simp

private theorem scaled_sub_ne_zero {n : ℕ} (x y : Factor k n) (s : k) (hs : s ≠ 0)
    (hnprop : ∀ t : k, x.1 ≠ t • y.1) : s • x.1 - y.1 ≠ 0 := by
  intro hzero
  apply hnprop s⁻¹
  have hscaled : s • x.1 = y.1 := sub_eq_zero.mp hzero
  calc
    x.1 = (s⁻¹ * s) • x.1 := by rw [inv_mul_cancel₀ hs, one_smul]
    _ = s⁻¹ • (s • x.1) := by rw [smul_smul]
    _ = s⁻¹ • y.1 := by rw [hscaled]

private theorem atom_xy_normalized (p r : FactorTriple k a b c) (s t : k)
    (hsn : s ≠ 0) (htn : t ≠ 0)
    (hs : p.first.1 = s • r.first.1) (ht : p.second.1 = t • r.second.1) :
    p.atom = atom r.first r.second (scaleFactor (s * t) (mul_ne_zero hsn htn) p.third) := by
  apply Atom.ext
  funext i j l
  simp only [FactorTriple.atom, FieldNativeMoves.atom_val, evalFactors, one_mul,
    hs, ht, scaleFactor, Pi.smul_apply, smul_eq_mul]
  ring

private theorem atom_xz_normalized (p r : FactorTriple k a b c) (s t : k)
    (hsn : s ≠ 0) (htn : t ≠ 0)
    (hs : p.first.1 = s • r.first.1) (ht : p.third.1 = t • r.third.1) :
    p.atom = atom r.first (scaleFactor (s * t) (mul_ne_zero hsn htn) p.second) r.third := by
  apply Atom.ext
  funext i j l
  simp only [FactorTriple.atom, FieldNativeMoves.atom_val, evalFactors, one_mul,
    hs, ht, scaleFactor, Pi.smul_apply, smul_eq_mul]
  ring

private theorem atom_yz_normalized (p r : FactorTriple k a b c) (s t : k)
    (hsn : s ≠ 0) (htn : t ≠ 0)
    (hs : p.second.1 = s • r.second.1) (ht : p.third.1 = t • r.third.1) :
    p.atom = atom (scaleFactor (s * t) (mul_ne_zero hsn htn) p.first) r.second r.third := by
  apply Atom.ext
  funext i j l
  simp only [FactorTriple.atom, FieldNativeMoves.atom_val, evalFactors, one_mul,
    hs, ht, scaleFactor, Pi.smul_apply, smul_eq_mul]
  ring

private theorem mem_pair_left {n : ℕ} (x y : Factor k n) :
    x.1 ∈ Submodule.span k ({x.1, y.1} : Set (Fin n → k)) :=
  Submodule.subset_span (by simp)

private theorem mem_pair_right {n : ℕ} (x y : Factor k n) :
    y.1 ∈ Submodule.span k ({x.1, y.1} : Set (Fin n → k)) :=
  Submodule.subset_span (by simp)

private theorem mem_pair_scaled_add {n : ℕ} (x y : Factor k n) (s : k) :
    s • x.1 + y.1 ∈ Submodule.span k ({x.1, y.1} : Set (Fin n → k)) := by
  exact Submodule.add_mem _ (Submodule.smul_mem _ s (mem_pair_left x y)) (mem_pair_right x y)

private theorem mem_pair_scaled_sub {n : ℕ} (x y : Factor k n) (s : k) :
    s • x.1 - y.1 ∈ Submodule.span k ({x.1, y.1} : Set (Fin n → k)) := by
  exact Submodule.sub_mem _ (Submodule.smul_mem _ s (mem_pair_left x y)) (mem_pair_right x y)

/-- Construct the actual normalized sum atom from checked two-ray gauges. The sole extra
hypothesis is nonproportionality of the original varying factors, not a supplied `q` or gauge. -/
def PairGauge.sum {p r : FactorTriple k a b c} (g : PairGauge p r)
    (hnprop : g.VaryingNonproportional) : SumPair p r := by
  cases g with
  | xy s t hs ht hfirst hsecond =>
      let hst : s * t ≠ 0 := mul_ne_zero hs ht
      let x := scaleFactor (s * t) hst p.third
      let hsum : x.1 + r.third.1 ≠ 0 := scaled_add_ne_zero p.third r.third (s * t) hst hnprop
      let qv := Factor.add x r.third hsum
      let qf : FactorTriple k a b c := ⟨r.first, r.second, qv⟩
      let q := qf.atom
      have hfirstAtom : p.atom = atom r.first r.second x :=
        atom_xy_normalized p r s t hs ht hfirst hsecond
      let formula : SplitFormula q p.atom r.atom := .third r.first r.second {
        x := x
        y := r.third
        sum_ne := hsum
        source_eq := rfl
        left_eq := hfirstAtom
        right_eq := rfl }
      exact {
        qFactors := qf
        q := q
        q_eq := rfl
        formula := formula
        eval_eq := formula.eval_eq
        first_mem := mem_pair_right p.first r.first
        second_mem := mem_pair_right p.second r.second
        third_mem := mem_pair_scaled_add p.third r.third (s * t) }
  | xz s t hs ht hfirst hthird =>
      let hst : s * t ≠ 0 := mul_ne_zero hs ht
      let x := scaleFactor (s * t) hst p.second
      let hsum : x.1 + r.second.1 ≠ 0 := scaled_add_ne_zero p.second r.second (s * t) hst hnprop
      let qv := Factor.add x r.second hsum
      let qf : FactorTriple k a b c := ⟨r.first, qv, r.third⟩
      let q := qf.atom
      have hfirstAtom : p.atom = atom r.first x r.third :=
        atom_xz_normalized p r s t hs ht hfirst hthird
      let formula : SplitFormula q p.atom r.atom := .second r.first r.third {
        x := x
        y := r.second
        sum_ne := hsum
        source_eq := rfl
        left_eq := hfirstAtom
        right_eq := rfl }
      exact {
        qFactors := qf
        q := q
        q_eq := rfl
        formula := formula
        eval_eq := formula.eval_eq
        first_mem := mem_pair_right p.first r.first
        second_mem := mem_pair_scaled_add p.second r.second (s * t)
        third_mem := mem_pair_right p.third r.third }
  | yz s t hs ht hsecond hthird =>
      let hst : s * t ≠ 0 := mul_ne_zero hs ht
      let x := scaleFactor (s * t) hst p.first
      let hsum : x.1 + r.first.1 ≠ 0 := scaled_add_ne_zero p.first r.first (s * t) hst hnprop
      let qv := Factor.add x r.first hsum
      let qf : FactorTriple k a b c := ⟨qv, r.second, r.third⟩
      let q := qf.atom
      have hfirstAtom : p.atom = atom x r.second r.third :=
        atom_yz_normalized p r s t hs ht hsecond hthird
      let formula : SplitFormula q p.atom r.atom := .first r.second r.third {
        x := x
        y := r.first
        sum_ne := hsum
        source_eq := rfl
        left_eq := hfirstAtom
        right_eq := rfl }
      exact {
        qFactors := qf
        q := q
        q_eq := rfl
        formula := formula
        eval_eq := formula.eval_eq
        first_mem := mem_pair_scaled_add p.first r.first (s * t)
        second_mem := mem_pair_right p.second r.second
        third_mem := mem_pair_right p.third r.third }

/-- Construct the actual normalized difference atom. Its native formula has the
coefficient-correct direction `p → r + (p-r)`. -/
def PairGauge.difference {p r : FactorTriple k a b c} (g : PairGauge p r)
    (hnprop : g.VaryingNonproportional) : DifferencePair p r := by
  cases g with
  | xy s t hs ht hfirst hsecond =>
      let hst : s * t ≠ 0 := mul_ne_zero hs ht
      let x := scaleFactor (s * t) hst p.third
      let hdiff : x.1 - r.third.1 ≠ 0 := scaled_sub_ne_zero p.third r.third (s * t) hst hnprop
      let qv := Factor.sub x r.third hdiff
      have hback : r.third.1 + qv.1 ≠ 0 := by
        intro hzero
        apply x.2
        calc
          x.1 = r.third.1 + qv.1 := by simp only [qv, Factor.sub]; abel
          _ = 0 := hzero
      let back := Factor.add r.third qv hback
      let qf : FactorTriple k a b c := ⟨r.first, r.second, qv⟩
      let q := qf.atom
      have hfirstAtom : p.atom = atom r.first r.second x :=
        atom_xy_normalized p r s t hs ht hfirst hsecond
      have hbackAtom : p.atom = atom r.first r.second back := by
        calc
          p.atom = atom r.first r.second x := hfirstAtom
          _ = atom r.first r.second back := by
            congr 1
            apply Subtype.ext
            simp only [back, qv, Factor.add, Factor.sub]
            abel
      let formula : SplitFormula p.atom r.atom q := .third r.first r.second {
        x := r.third
        y := qv
        sum_ne := hback
        source_eq := hbackAtom
        left_eq := rfl
        right_eq := rfl }
      exact {
        qFactors := qf
        q := q
        q_eq := rfl
        formula := formula
        eval_eq := by have he := formula.eval_eq; rw [he]; abel
        first_mem := mem_pair_right p.first r.first
        second_mem := mem_pair_right p.second r.second
        third_mem := mem_pair_scaled_sub p.third r.third (s * t) }
  | xz s t hs ht hfirst hthird =>
      let hst : s * t ≠ 0 := mul_ne_zero hs ht
      let x := scaleFactor (s * t) hst p.second
      let hdiff : x.1 - r.second.1 ≠ 0 := scaled_sub_ne_zero p.second r.second (s * t) hst hnprop
      let qv := Factor.sub x r.second hdiff
      have hback : r.second.1 + qv.1 ≠ 0 := by
        intro hzero
        apply x.2
        calc
          x.1 = r.second.1 + qv.1 := by simp only [qv, Factor.sub]; abel
          _ = 0 := hzero
      let back := Factor.add r.second qv hback
      let qf : FactorTriple k a b c := ⟨r.first, qv, r.third⟩
      let q := qf.atom
      have hfirstAtom : p.atom = atom r.first x r.third :=
        atom_xz_normalized p r s t hs ht hfirst hthird
      have hbackAtom : p.atom = atom r.first back r.third := by
        calc
          p.atom = atom r.first x r.third := hfirstAtom
          _ = atom r.first back r.third := by
            congr 1
            apply Subtype.ext
            simp only [back, qv, Factor.add, Factor.sub]
            abel
      let formula : SplitFormula p.atom r.atom q := .second r.first r.third {
        x := r.second
        y := qv
        sum_ne := hback
        source_eq := hbackAtom
        left_eq := rfl
        right_eq := rfl }
      exact {
        qFactors := qf
        q := q
        q_eq := rfl
        formula := formula
        eval_eq := by have he := formula.eval_eq; rw [he]; abel
        first_mem := mem_pair_right p.first r.first
        second_mem := mem_pair_scaled_sub p.second r.second (s * t)
        third_mem := mem_pair_right p.third r.third }
  | yz s t hs ht hsecond hthird =>
      let hst : s * t ≠ 0 := mul_ne_zero hs ht
      let x := scaleFactor (s * t) hst p.first
      let hdiff : x.1 - r.first.1 ≠ 0 := scaled_sub_ne_zero p.first r.first (s * t) hst hnprop
      let qv := Factor.sub x r.first hdiff
      have hback : r.first.1 + qv.1 ≠ 0 := by
        intro hzero
        apply x.2
        calc
          x.1 = r.first.1 + qv.1 := by simp only [qv, Factor.sub]; abel
          _ = 0 := hzero
      let back := Factor.add r.first qv hback
      let qf : FactorTriple k a b c := ⟨qv, r.second, r.third⟩
      let q := qf.atom
      have hfirstAtom : p.atom = atom x r.second r.third :=
        atom_yz_normalized p r s t hs ht hsecond hthird
      have hbackAtom : p.atom = atom back r.second r.third := by
        calc
          p.atom = atom x r.second r.third := hfirstAtom
          _ = atom back r.second r.third := by
            congr 1
            apply Subtype.ext
            simp only [back, qv, Factor.add, Factor.sub]
            abel
      let formula : SplitFormula p.atom r.atom q := .first r.second r.third {
        x := r.first
        y := qv
        sum_ne := hback
        source_eq := hbackAtom
        left_eq := rfl
        right_eq := rfl }
      exact {
        qFactors := qf
        q := q
        q_eq := rfl
        formula := formula
        eval_eq := by have he := formula.eval_eq; rw [he]; abel
        first_mem := mem_pair_scaled_sub p.first r.first (s * t)
        second_mem := mem_pair_right p.second r.second
        third_mem := mem_pair_right p.third r.third }


/-- Package a normalized sum as an actual one-to-two native Split. -/
theorem SumPair.nativeSplit {p r : FactorTriple k a b c} (h : SumPair p r)
    (hne : p.atom ≠ r.atom) :
    NativeReplacement (singletonState h.q) (pairState p.atom r.atom) :=
  .split h.formula hne

/-- Package a normalized sum as the actual reverse two-to-one native Reduction. -/
theorem SumPair.nativeReduction {p r : FactorTriple k a b c} (h : SumPair p r)
    (hne : p.atom ≠ r.atom) :
    NativeReplacement (pairState p.atom r.atom) (singletonState h.q) :=
  .reduction h.formula hne

/-- Package a normalized difference as the coefficient-correct opposite-side Split
`p → r + q`, rather than as a Reduction of `p` and `r`. -/
theorem DifferencePair.nativeSplit {p r : FactorTriple k a b c} (h : DifferencePair p r)
    (hne : r.atom ≠ h.q) :
    NativeReplacement (singletonState p.atom) (pairState r.atom h.q) :=
  .split h.formula hne

/-- Every local native replacement removes at least one atom. -/
theorem nativeReplacement_source_nonempty {A B : State k a b c}
    (h : NativeReplacement A B) : A.Nonempty := by
  cases h with
  | split _ _ => simp [singletonState]
  | reduction _ hne => simp [pairState]
  | flip _ hsource _ => simp [pairState]

private theorem disjoint_left_of_union {C A B : State k a b c}
    (h : Disjoint C (stateUnion A B)) : Disjoint C A := by
  classical
  rw [Finset.disjoint_left] at h ⊢
  intro x hxC hxA
  exact h hxC (by simp only [stateUnion, Finset.mem_union]; exact Or.inl hxA)

private theorem disjoint_right_of_union {C A B : State k a b c}
    (h : Disjoint C (stateUnion A B)) : Disjoint C B := by
  classical
  rw [Finset.disjoint_left] at h ⊢
  intro x hxC hxB
  exact h hxC (by simp only [stateUnion, Finset.mem_union]; exact Or.inr hxB)

/-- Lift a local native replacement through a context disjoint from the union of its local
endpoints. This checks source presence, target freshness, and the exact erase/insert state. -/
noncomputable def contextualStep {C A B : State k a b c} (native : NativeReplacement A B)
    (hcontext : Disjoint C (stateUnion A B)) :
    NativeStep (stateUnion C A) (stateUnion C B) := by
  let hCA : Disjoint C A := disjoint_left_of_union hcontext
  let hCB : Disjoint C B := disjoint_right_of_union hcontext
  refine {
    source := A
    target := B
    native := native
    source_subset := ?_
    target_fresh := ?_
    result_eq := ?_ }
  · intro x hxA
    classical
    simp only [stateUnion, Finset.mem_union]
    exact Or.inr hxA
  · rw [erase_endpoint_restores_context hCA]
    exact hCB.symm
  · rw [erase_endpoint_restores_context hCA]

/-- Lift a locally endpoint-disjoint native replacement to a strict contextual step. Local
nonemptiness proves that adjoining a disjoint context cannot identify the whole endpoints. -/
noncomputable def contextualStrictStep {C A B : State k a b c}
    (native : NativeReplacement A B) (hendpoints : Disjoint A B)
    (hcontext : Disjoint C (stateUnion A B)) :
    StrictNativeStep (stateUnion C A) (stateUnion C B) := by
  refine {
    step := contextualStep native hcontext
    endpoints_disjoint := hendpoints
    ne := ?_ }
  intro heq
  obtain ⟨x, hxA⟩ := nativeReplacement_source_nonempty native
  have hxC : x ∉ C := by
    intro hxC
    exact Finset.disjoint_left.mp (disjoint_left_of_union hcontext) hxC hxA
  have hxB : x ∉ B := Finset.disjoint_left.mp hendpoints hxA
  have hxleft : x ∈ stateUnion C A := by
    classical
    simp only [stateUnion, Finset.mem_union]
    exact Or.inr hxA
  have hxright : x ∈ stateUnion C B := heq ▸ hxleft
  classical
  simp only [stateUnion, Finset.mem_union] at hxright
  exact hxright.elim hxC hxB

namespace Path

/-- The primitive-step length of a strict native path. -/
def length {D E : State k a b c} : StrictNativePath D E → ℕ
  | .nil _ => 0
  | .cons _ tail => length tail + 1

/-- The stationary path has primitive length zero. -/
example (D : State k a b c) : length (.nil D) = 0 := rfl

/-- Concatenate two checked strict native paths with an exactly matching middle state. -/
noncomputable def append {D E F : State k a b c} : StrictNativePath D E →
    StrictNativePath E F → StrictNativePath D F
  | .nil _, second => second
  | .cons step tail, second => .cons step (append tail second)

/-- Appending paths adds their primitive lengths. -/
theorem length_append {D E F : State k a b c} (first : StrictNativePath D E)
    (second : StrictNativePath E F) :
    length (append first second) = length first + length second := by
  induction first with
  | nil _ => simp only [append, length, Nat.zero_add]
  | cons step tail ih =>
      simp only [append, length, ih]
      omega

/-- Append one strict native step to the end of a strict native path. -/
noncomputable def snoc {D E F : State k a b c} (path : StrictNativePath D E)
    (last : StrictNativeStep E F) : StrictNativePath D F :=
  append path (.cons last (.nil F))

/-- Appending one strict step increases primitive length by one. -/
theorem length_snoc {D E F : State k a b c} (path : StrictNativePath D E)
    (last : StrictNativeStep E F) : length (snoc path last) = length path + 1 := by
  simp only [snoc, length_append, length, Nat.zero_add]

/-- A path has altitude at most `H` when every vertex has cardinality at most `H`.
The endpoint case is included, so this predicate is stable under splicing and reversal. -/
inductive HeightBound (H : ℕ) : {D E : State k a b c} → StrictNativePath D E → Prop
  | nil (D : State k a b c) (hD : D.card ≤ H) : HeightBound H (.nil D)
  | cons {D E F : State k a b c} {first : StrictNativeStep D E}
      {tail : StrictNativePath E F} (hD : D.card ≤ H)
      (htail : HeightBound H tail) : HeightBound H (.cons first tail)

/-- The initial vertex of a height-bounded path satisfies the bound. -/
theorem HeightBound.start {H : ℕ} {D E : State k a b c} {path : StrictNativePath D E}
    (hpath : HeightBound H path) : D.card ≤ H := by
  cases hpath with
  | nil _ hD => exact hD
  | cons hD _ => exact hD

/-- The terminal vertex of a height-bounded path satisfies the bound. -/
theorem HeightBound.finish {H : ℕ} {D E : State k a b c} {path : StrictNativePath D E}
    (hpath : HeightBound H path) : E.card ≤ H := by
  induction hpath with
  | nil _ hD => exact hD
  | cons _ htail ih => exact ih

/-- Height bounds are inherited by concatenation. -/
theorem HeightBound.append {H : ℕ} {D E F : State k a b c}
    {first : StrictNativePath D E} {second : StrictNativePath E F}
    (hfirst : HeightBound H first) (hsecond : HeightBound H second) :
    HeightBound H (append first second) := by
  induction hfirst with
  | nil _ hD => exact hsecond
  | cons hD htail ih => exact .cons hD (ih hsecond)

/-- Appending one step preserves an altitude bound when its new endpoint satisfies it. -/
theorem HeightBound.snoc {H : ℕ} {D E F : State k a b c}
    {path : StrictNativePath D E} (hpath : HeightBound H path)
    (last : StrictNativeStep E F) (hF : F.card ≤ H) :
    HeightBound H (snoc path last) := by
  exact hpath.append (.cons hpath.finish (.nil F hF))


/-- Reverse a strict native path, reversing every coefficient-correct native step. -/
noncomputable def reverse {D E : State k a b c} : StrictNativePath D E →
    StrictNativePath E D
  | .nil D => .nil D
  | .cons first tail => snoc (reverse tail) first.reverse

/-- Reversing a path preserves its primitive length. -/
theorem length_reverse {D E : State k a b c} (path : StrictNativePath D E) :
    length (reverse path) = length path := by
  induction path with
  | nil D => rfl
  | cons first tail ih =>
      simp only [reverse, length_snoc, length, ih]

/-- Reversal inherits exactly the same altitude bound. -/
theorem HeightBound.reverse {H : ℕ} {D E : State k a b c}
    {path : StrictNativePath D E} (hpath : HeightBound H path) :
    HeightBound H (reverse path) := by
  induction hpath with
  | nil D hD => exact .nil D hD
  | @cons D E F first tail hD htail ih => exact ih.snoc first.reverse hD

end Path

namespace Execution

open FieldTernaryFiveCircuitPair

#eval
  let one : Factor F3 1 := ⟨![1], by decide⟩
  let e0 : Factor F3 2 := ⟨![1, 0], by decide⟩
  let e1 : Factor F3 2 := ⟨![0, 1], by decide⟩
  let p : FactorTriple F3 1 1 2 := ⟨one, one, e0⟩
  let r : FactorTriple F3 1 1 2 := ⟨one, one, e1⟩
  let g : PairGauge p r := .xy 1 1 (by decide) (by decide) (by simp [p, r]) (by simp [p, r])
  let hn : g.VaryingNonproportional := by
    dsimp only [PairGauge.VaryingNonproportional, g]
    intro t heq
    have hcoord := congrFun heq 0
    norm_num [p, r, e0, e1] at hcoord
  let sum := g.sum hn
  let difference := g.difference hn
  (sum.qFactors.third.1 0, sum.qFactors.third.1 1,
    difference.qFactors.third.1 0, difference.qFactors.third.1 1)

#eval
  let one : Factor F3 1 := ⟨![1], by decide⟩
  let e0 : Factor F3 2 := ⟨![1, 0], by decide⟩
  let e1 : Factor F3 2 := ⟨![0, 1], by decide⟩
  let p : FactorTriple F3 1 2 1 := ⟨one, e0, one⟩
  let r : FactorTriple F3 1 2 1 := ⟨one, e1, one⟩
  let g : PairGauge p r := .xz 1 1 (by decide) (by decide) (by simp [p, r]) (by simp [p, r])
  let hn : g.VaryingNonproportional := by
    dsimp only [PairGauge.VaryingNonproportional, g]
    intro t heq
    have hcoord := congrFun heq 0
    norm_num [p, r, e0, e1] at hcoord
  let sum := g.sum hn
  let difference := g.difference hn
  (sum.qFactors.second.1 0, sum.qFactors.second.1 1,
    difference.qFactors.second.1 0, difference.qFactors.second.1 1)

#eval
  let one : Factor F3 1 := ⟨![1], by decide⟩
  let e0 : Factor F3 2 := ⟨![1, 0], by decide⟩
  let e1 : Factor F3 2 := ⟨![0, 1], by decide⟩
  let p : FactorTriple F3 2 1 1 := ⟨e0, one, one⟩
  let r : FactorTriple F3 2 1 1 := ⟨e1, one, one⟩
  let g : PairGauge p r := .yz 1 1 (by decide) (by decide) (by simp [p, r]) (by simp [p, r])
  let hn : g.VaryingNonproportional := by
    dsimp only [PairGauge.VaryingNonproportional, g]
    intro t heq
    have hcoord := congrFun heq 0
    norm_num [p, r, e0, e1] at hcoord
  let sum := g.sum hn
  let difference := g.difference hn
  (sum.qFactors.first.1 0, sum.qFactors.first.1 1,
    difference.qFactors.first.1 0, difference.qFactors.first.1 1)

end Execution

#check @FactorTriple.atom
#check @factorTripleAt
#check @candidateGauge
#check @certifiedScanGauge
#check @PairGauge.varyingNonproportional_of_atom
#check @PairGauge.varyingNonproportional_of_linearIndependent
#check @PairGauge.sum
#check @PairGauge.difference
#check @SumPair.nativeReduction
#check @DifferencePair.nativeSplit
#check @contextualStrictStep
#check @Path.append
#check @Path.HeightBound.append
#check @Path.HeightBound.reverse
#check @Path.reverse
#print axioms PairGauge.varyingNonproportional_of_atom
#print axioms PairGauge.varyingNonproportional_of_linearIndependent
#print axioms certifiedScanGauge
#print axioms PairGauge.sum
#print axioms PairGauge.difference
#print axioms contextualStrictStep
#print axioms Path.HeightBound.reverse
#print axioms Path.reverse

end FieldNativePairBridge
end BilinearComplexity
