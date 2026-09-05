import BilinearComplexity.NormalizedBinaryCompactEnumerationBridge
import BilinearComplexity.NormalizedBinaryCompactMaskSemantics

set_option autoImplicit false

/-!
# Semantic reflection for compact normalized binary support masks

This module proves the representation-independent mask lemmas used to connect
the compact support checker to normalized tensor and factor-span semantics. It
reflects the compact existential range loop, identifies `spans5` with abstract
binary linear span, and proves that row-major tensor masks preserve XOR and
detect zero while they remain in range.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.NormalizedBinaryCompactSupportSemantics

open NormalizedBinaryCarrier
open NormalizedBinaryCompactEnumeration
open NormalizedBinaryCompactMaskSemantics

private theorem foldRange_or_eq_true_iff (predicate : Nat → Bool)
    (acc : Bool) (start length : Nat) :
    foldRange (fun result i => result || predicate i) acc start length = true ↔
      acc = true ∨ ∃ i, start ≤ i ∧ i < start + length ∧ predicate i = true := by
  induction length generalizing acc start with
  | zero =>
      simp only [foldRange, Nat.add_zero]
      constructor
      · exact fun h => Or.inl h
      · rintro (h | ⟨i, hle, hlt, _⟩)
        · exact h
        · exact False.elim (Nat.not_lt_of_ge hle hlt)
  | succ length ih =>
      rw [foldRange, ih]
      simp only [Bool.or_eq_true]
      constructor
      · rintro ((hacc | hstart) | htail)
        · exact Or.inl hacc
        · exact Or.inr ⟨start, Nat.le_refl start, by omega, hstart⟩
        · rcases htail with ⟨i, hle, hlt, hi⟩
          exact Or.inr ⟨i, by omega, by omega, hi⟩
      · rintro (hacc | ⟨i, hle, hlt, hi⟩)
        · exact Or.inl (Or.inl hacc)
        · by_cases hieq : i = start
          · subst i
            exact Or.inl (Or.inr hi)
          · exact Or.inr ⟨i, by omega, by omega, hi⟩

/-- Existential interval reflection for the primitive non-materializing fold. -/
theorem anyRange_eq_true_iff (start length : Nat) (predicate : Nat → Bool) :
    anyRange start length predicate = true ↔
      ∃ i, start ≤ i ∧ i < start + length ∧ predicate i = true := by
  rw [anyRange, foldRange_or_eq_true_iff]
  simp only [Bool.false_eq_true, false_or]

/-- The compact five-mask spanning check reflects full semantic span. -/
theorem spans5_eq_true_iff_span_eq_top {d x0 x1 x2 x3 x4 : Nat}
    (hx0 : x0 < 2 ^ d) (hx1 : x1 < 2 ^ d) (hx2 : x2 < 2 ^ d)
    (hx3 : x3 < 2 ^ d) (hx4 : x4 < 2 ^ d) :
    spans5 d x0 x1 x2 x3 x4 = true ↔
      Submodule.span F2
        (Set.range (fiveMaskVectors d x0 x1 x2 x3 x4)) = ⊤ := by
  rw [span_five_maskVectors_eq_top_iff hx0 hx1 hx2 hx3 hx4]
  simp only [spans5, allRange_eq_true_iff, anyRange_eq_true_iff,
    Nat.zero_le, true_implies, Nat.zero_add, beq_iff_eq, true_and, selectedXor5]

/-- XOR of mask tensors is pointwise tensor addition over `F2`. -/
theorem tensorOfMask_xor (p : Profile) (m n : Nat) :
    NormalizedBinaryCompactEnumerationBridge.tensorOfMask p (Nat.xor m n) =
      NormalizedBinaryCompactEnumerationBridge.tensorOfMask p m +
        NormalizedBinaryCompactEnumerationBridge.tensorOfMask p n := by
  funext i j k
  simp only [NormalizedBinaryCompactEnumerationBridge.tensorOfMask, Pi.add_apply]
  cases hm : m.testBit ((i.val * p.second + j.val) * p.third + k.val) <;>
    cases hn : n.testBit ((i.val * p.second + j.val) * p.third + k.val) <;>
    simp [hm, hn, ZModModule.add_self]

/-- Canonical row-major indexing equivalence for tensor coordinates. -/
def tensorIndexEquiv (p : Profile) :
    (Fin p.first × Fin p.second) × Fin p.third ≃
      Fin ((p.first * p.second) * p.third) :=
  (Equiv.prodCongr finProdFinEquiv (Equiv.refl _)).trans finProdFinEquiv

example :
    (tensorIndexEquiv profile222
      (((0 : Fin 2), (1 : Fin 2)), (1 : Fin 2))).val = 3 := rfl

/-- Flatten a tensor according to the packed row-major coordinate order. -/
def flattenTensor (p : Profile) (T : Tensor F2 p.first p.second p.third) :
    CoordinateVector ((p.first * p.second) * p.third) :=
  fun l =>
    let ijk := (tensorIndexEquiv p).symm l
    T ijk.1.1 ijk.1.2 ijk.2

example : flattenTensor profile222
    (NormalizedBinaryCompactEnumerationBridge.tensorOfMask profile222 5) =
      ![1, 0, 1, 0, 0, 0, 0, 0] := by
  funext i
  fin_cases i <;> decide

/-- Flattening a mask tensor recovers its little-endian mask vector. -/
theorem flattenTensor_tensorOfMask (p : Profile) (m : Nat) :
    flattenTensor p
        (NormalizedBinaryCompactEnumerationBridge.tensorOfMask p m) =
      maskVector ((p.first * p.second) * p.third) m := by
  funext l
  let ijk := (tensorIndexEquiv p).symm l
  have hindex :
      ((ijk.1.1.val * p.second + ijk.1.2.val) * p.third + ijk.2.val) = l.val := by
    have heq := congrArg Fin.val ((tensorIndexEquiv p).apply_symm_apply l)
    change ((tensorIndexEquiv p) ijk).val = l.val at heq
    simp only [tensorIndexEquiv, Equiv.trans_apply, Equiv.prodCongr_apply,
      finProdFinEquiv] at heq
    calc
      _ = ijk.2.val + p.third * (ijk.1.2.val + p.second * ijk.1.1.val) := by ring
      _ = l.val := heq
  simp only [flattenTensor, NormalizedBinaryCompactEnumerationBridge.tensorOfMask,
    maskVector]
  rw [hindex]

/-- An in-range packed tensor mask is zero exactly when the mask is zero. -/
theorem tensorOfMask_eq_zero_iff (p : Profile) {m : Nat}
    (hm : m < 2 ^ ((p.first * p.second) * p.third)) :
    NormalizedBinaryCompactEnumerationBridge.tensorOfMask p m = 0 ↔ m = 0 := by
  constructor
  · intro hzero
    have hmaskzero :
        NormalizedBinaryCompactEnumerationBridge.tensorOfMask p 0 = 0 := by
      funext i j k
      simp [NormalizedBinaryCompactEnumerationBridge.tensorOfMask]
    have hvector : maskVector ((p.first * p.second) * p.third) m =
        maskVector ((p.first * p.second) * p.third) 0 := by
      rw [← flattenTensor_tensorOfMask, hzero, ← hmaskzero,
        flattenTensor_tensorOfMask]
    exact maskVector_injective_of_lt hm (by simp) hvector
  · rintro rfl
    funext i j k
    simp [NormalizedBinaryCompactEnumerationBridge.tensorOfMask]

example : spans5 2 1 2 0 0 0 = true ↔
    Submodule.span F2
      (Set.range (fiveMaskVectors 2 1 2 0 0 0)) = ⊤ := by
  exact spans5_eq_true_iff_span_eq_top (by decide) (by decide) (by decide)
    (by decide) (by decide)

#check @anyRange_eq_true_iff
#check @spans5_eq_true_iff_span_eq_top
#check @tensorOfMask_xor
#check @flattenTensor_tensorOfMask
#check @tensorOfMask_eq_zero_iff
#print axioms spans5_eq_true_iff_span_eq_top
#print axioms tensorOfMask_xor
#print axioms flattenTensor_tensorOfMask
#print axioms tensorOfMask_eq_zero_iff

end BilinearComplexity.NormalizedBinaryCompactSupportSemantics
