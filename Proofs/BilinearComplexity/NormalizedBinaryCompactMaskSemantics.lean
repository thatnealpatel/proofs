import Mathlib.Data.Nat.Bitwise
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import BilinearComplexity.NormalizedBinaryFiveCircuitRows

set_option autoImplicit false

/-!
# Semantic bridge for compact binary masks

This module identifies little-endian natural-number masks with binary
coordinate vectors. It proves that XOR is vector addition, that bounded masks
and vectors are equivalent, and that the low five bits enumerate every binary
linear combination of five generators. These facts are independent of the
compact enumeration loops and frozen tables.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.NormalizedBinaryCompactMaskSemantics

open NormalizedBinaryCarrier
open NormalizedBinaryFiveCircuitRows
open scoped BigOperators

/-- Unbounded little-endian binary vector represented by a natural-number mask. -/
def maskVector (d m : ℕ) : CoordinateVector d :=
  fun i => if m.testBit i then 1 else 0

/-- On an in-range mask, `maskVector` agrees with the existing checked decoder. -/
theorem maskVector_eq_coordinateVectorOfMask (d m : ℕ) (hm : m < 2 ^ d) :
    maskVector d m = coordinateVectorOfMask d m hm := rfl

/-- Natural-number XOR is coordinatewise addition over `F2`. -/
theorem maskVector_xor (d m n : ℕ) :
    maskVector d (Nat.xor m n) = maskVector d m + maskVector d n := by
  funext i
  simp only [maskVector, Pi.add_apply]
  cases hm : m.testBit i <;> cases hn : n.testBit i <;>
    simp [hm, hn, ZModModule.add_self]

/-- Encode a binary coordinate vector as its little-endian natural-number mask. -/
def vectorMask {d : ℕ} (v : CoordinateVector d) : ℕ :=
  Nat.ofBits fun i => v i = 1

/-- The mask encoding of a `d`-dimensional vector lies below `2^d`. -/
theorem vectorMask_lt_two_pow {d : ℕ} (v : CoordinateVector d) :
    vectorMask v < 2 ^ d := by
  exact Nat.ofBits_lt_two_pow _

/-- Decoding the mask encoding of a binary coordinate vector recovers it. -/
theorem maskVector_vectorMask {d : ℕ} (v : CoordinateVector d) :
    maskVector d (vectorMask v) = v := by
  funext i
  simp only [maskVector, vectorMask, Nat.testBit_ofBits, i.isLt, ↓reduceDIte]
  have hval : (v i).val = 0 ∨ (v i).val = 1 := by
    have hvalLt : (v i).val < 2 := ZMod.val_lt (v i)
    omega
  rcases hval with hval | hval
  · have hi : v i = 0 := by
      rw [← ZMod.natCast_zmod_val (v i), hval]
      rfl
    simp [hi]
  · have hi : v i = 1 := by
      rw [← ZMod.natCast_zmod_val (v i), hval]
      rfl
    simp [hi]

/-- Every binary coordinate vector has an in-range mask representation. -/
theorem exists_maskVector_eq {d : ℕ} (v : CoordinateVector d) :
    ∃ m, m < 2 ^ d ∧ maskVector d m = v :=
  ⟨vectorMask v, vectorMask_lt_two_pow v, maskVector_vectorMask v⟩

/-- In-range masks are determined by their decoded binary vectors. -/
theorem maskVector_injective_of_lt {d m n : ℕ} (hm : m < 2 ^ d)
    (hn : n < 2 ^ d) (h : maskVector d m = maskVector d n) : m = n := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < d
  · have hat := congrFun h ⟨i, hi⟩
    simp only [maskVector] at hat
    cases hmBit : m.testBit i <;> cases hnBit : n.testBit i <;>
      simp [hmBit, hnBit] at hat ⊢
  · have hdi : d ≤ i := Nat.le_of_not_gt hi
    have hmpow : m < 2 ^ i := lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) hdi)
    have hnpow : n < 2 ^ i := lt_of_lt_of_le hn (Nat.pow_le_pow_right (by omega) hdi)
    rw [Nat.testBit_lt_two_pow hmpow, Nat.testBit_lt_two_pow hnpow]

#check @maskVector_xor
#check @vectorMask_lt_two_pow
#check @maskVector_vectorMask
#check @maskVector_injective_of_lt

/-- The five semantic generators corresponding to five natural-number masks. -/
def fiveMaskVectors (d x0 x1 x2 x3 x4 : ℕ) : Fin 5 → CoordinateVector d :=
  ![maskVector d x0, maskVector d x1, maskVector d x2,
    maskVector d x3, maskVector d x4]

/-- The five binary coefficients selected by the low five bits of a mask. -/
def coefficientsOfSelection5 (selection : ℕ) : Fin 5 → F2 :=
  maskVector 5 selection

/-- The in-range mask encoding a family of five binary coefficients. -/
def selectionOfCoefficients5 (coefficients : Fin 5 → F2) : ℕ :=
  vectorMask coefficients

/-- Every coefficient family has a selection mask below `32`. -/
theorem selectionOfCoefficients5_lt (coefficients : Fin 5 → F2) :
    selectionOfCoefficients5 coefficients < 32 := by
  simpa [selectionOfCoefficients5] using vectorMask_lt_two_pow coefficients

/-- Decoding the selection encoded from five coefficients recovers them. -/
theorem coefficientsOfSelection5_selectionOfCoefficients5
    (coefficients : Fin 5 → F2) :
    coefficientsOfSelection5 (selectionOfCoefficients5 coefficients) =
      coefficients := by
  exact maskVector_vectorMask coefficients

/-- Encoding an in-range five-bit selection after decoding recovers the
selection. -/
theorem selectionOfCoefficients5_coefficientsOfSelection5 {selection : ℕ}
    (hselection : selection < 32) :
    selectionOfCoefficients5 (coefficientsOfSelection5 selection) =
      selection := by
  exact maskVector_injective_of_lt (d := 5)
    (by simpa using (selectionOfCoefficients5_lt
      (coefficientsOfSelection5 selection)))
    (by simpa using hselection)
    (coefficientsOfSelection5_selectionOfCoefficients5 _)

/-- The semantic linear combination selected by the low five bits. -/
def selectedSum5 {d : ℕ} (generators : Fin 5 → CoordinateVector d)
    (selection : ℕ) : CoordinateVector d :=
  ∑ i, coefficientsOfSelection5 selection i • generators i

/-- The zero mask decodes to the zero vector. -/
@[simp] theorem maskVector_zero (d : ℕ) : maskVector d 0 = 0 := by
  funext i
  simp [maskVector]

/-- Decoding an optionally selected mask commutes with the selection. -/
theorem maskVector_ite (d x : ℕ) (b : Bool) :
    maskVector d (if b then x else 0) =
      if b then maskVector d x else 0 := by
  cases b <;> simp

/-- Decoding the nested XOR of five optionally selected masks gives the
corresponding five-term binary linear combination. -/
theorem maskVector_selectedXor5 (d x0 x1 x2 x3 x4 selection : ℕ) :
    maskVector d
        (Nat.xor (if selection.testBit 0 then x0 else 0)
          (Nat.xor (if selection.testBit 1 then x1 else 0)
            (Nat.xor (if selection.testBit 2 then x2 else 0)
              (Nat.xor (if selection.testBit 3 then x3 else 0)
                (if selection.testBit 4 then x4 else 0))))) =
      selectedSum5 (fiveMaskVectors d x0 x1 x2 x3 x4) selection := by
  simp only [maskVector_xor, maskVector_ite, selectedSum5,
    coefficientsOfSelection5, fiveMaskVectors, Fin.sum_univ_succ]
  simp [maskVector]

#check @selectionOfCoefficients5_lt
#check @coefficientsOfSelection5_selectionOfCoefficients5
#check @selectionOfCoefficients5_coefficientsOfSelection5
#check @maskVector_selectedXor5

/-- A low-bit XOR selection of five `d`-bit masks is itself a `d`-bit mask. -/
theorem selectedXor5_lt_two_pow {d x0 x1 x2 x3 x4 selection : ℕ}
    (hx0 : x0 < 2 ^ d) (hx1 : x1 < 2 ^ d) (hx2 : x2 < 2 ^ d)
    (hx3 : x3 < 2 ^ d) (hx4 : x4 < 2 ^ d) :
    Nat.xor (if selection.testBit 0 then x0 else 0)
        (Nat.xor (if selection.testBit 1 then x1 else 0)
          (Nat.xor (if selection.testBit 2 then x2 else 0)
            (Nat.xor (if selection.testBit 3 then x3 else 0)
              (if selection.testBit 4 then x4 else 0)))) < 2 ^ d := by
  have hzero : 0 < 2 ^ d := pow_pos (by omega) _
  have h0 : (if selection.testBit 0 then x0 else 0) < 2 ^ d := by
    split
    · exact hx0
    · exact hzero
  have h1 : (if selection.testBit 1 then x1 else 0) < 2 ^ d := by
    split
    · exact hx1
    · exact hzero
  have h2 : (if selection.testBit 2 then x2 else 0) < 2 ^ d := by
    split
    · exact hx2
    · exact hzero
  have h3 : (if selection.testBit 3 then x3 else 0) < 2 ^ d := by
    split
    · exact hx3
    · exact hzero
  have h4 : (if selection.testBit 4 then x4 else 0) < 2 ^ d := by
    split
    · exact hx4
    · exact hzero
  exact Nat.xor_lt_two_pow h0
    (Nat.xor_lt_two_pow h1
      (Nat.xor_lt_two_pow h2 (Nat.xor_lt_two_pow h3 h4)))

/-- Five in-range mask vectors span the coordinate space exactly when every
in-range target is the nested XOR selected by one of the `32` low-bit
selection masks. -/
theorem span_five_maskVectors_eq_top_iff {d x0 x1 x2 x3 x4 : ℕ}
    (hx0 : x0 < 2 ^ d) (hx1 : x1 < 2 ^ d) (hx2 : x2 < 2 ^ d)
    (hx3 : x3 < 2 ^ d) (hx4 : x4 < 2 ^ d) :
    Submodule.span F2
        (Set.range (fiveMaskVectors d x0 x1 x2 x3 x4)) = ⊤ ↔
      ∀ target, target < 2 ^ d →
        ∃ selection, selection < 32 ∧
          (Nat.xor (if selection.testBit 0 then x0 else 0)
            (Nat.xor (if selection.testBit 1 then x1 else 0)
              (Nat.xor (if selection.testBit 2 then x2 else 0)
                (Nat.xor (if selection.testBit 3 then x3 else 0)
                  (if selection.testBit 4 then x4 else 0)))) = target) := by
  constructor
  · intro hspan target htarget
    have hmem : maskVector d target ∈ Submodule.span F2
        (Set.range (fiveMaskVectors d x0 x1 x2 x3 x4)) := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨coefficients, hcoefficients⟩ :=
      Finsupp.mem_span_range_iff_exists_finsupp.mp hmem
    let selection := selectionOfCoefficients5 (fun i : Fin 5 => coefficients i)
    have hselection : selection < 32 :=
      selectionOfCoefficients5_lt _
    have hselectedVector :
        maskVector d
            (Nat.xor (if selection.testBit 0 then x0 else 0)
              (Nat.xor (if selection.testBit 1 then x1 else 0)
                (Nat.xor (if selection.testBit 2 then x2 else 0)
                  (Nat.xor (if selection.testBit 3 then x3 else 0)
                    (if selection.testBit 4 then x4 else 0))))) =
          maskVector d target := by
      rw [maskVector_selectedXor5]
      change (∑ i : Fin 5, maskVector 5 selection i •
        fiveMaskVectors d x0 x1 x2 x3 x4 i) = maskVector d target
      rw [show maskVector 5 selection = (fun i : Fin 5 => coefficients i) by
        exact coefficientsOfSelection5_selectionOfCoefficients5 _]
      rw [← hcoefficients]
      exact (Finsupp.sum_fintype coefficients
        (fun i x => x • fiveMaskVectors d x0 x1 x2 x3 x4 i)
        (fun i => zero_smul F2 (fiveMaskVectors d x0 x1 x2 x3 x4 i))).symm
    refine ⟨selection, hselection, ?_⟩
    exact maskVector_injective_of_lt
      (selectedXor5_lt_two_pow hx0 hx1 hx2 hx3 hx4)
      htarget hselectedVector
  · intro htargets
    apply top_unique
    intro vector _
    let target := vectorMask vector
    have htarget : target < 2 ^ d := vectorMask_lt_two_pow vector
    have hdecode : maskVector d target = vector := maskVector_vectorMask vector
    obtain ⟨selection, _, hselection⟩ := htargets target htarget
    rw [← hdecode, ← hselection, maskVector_selectedXor5]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self i))

example : maskVector 3 5 = ![1, 0, 1] := by decide

example :
    Submodule.span F2
      (Set.range (fiveMaskVectors 2 1 2 3 1 2)) = ⊤ := by
  rw [span_five_maskVectors_eq_top_iff (by decide) (by decide)
    (by decide) (by decide) (by decide)]
  decide

#check @maskVector_eq_coordinateVectorOfMask
#check @maskVector_xor
#check @exists_maskVector_eq
#check @maskVector_injective_of_lt
#check @coefficientsOfSelection5_selectionOfCoefficients5
#check @selectionOfCoefficients5_coefficientsOfSelection5
#check @maskVector_selectedXor5
#check @selectedXor5_lt_two_pow
#check @span_five_maskVectors_eq_top_iff
#print axioms maskVector_xor
#print axioms exists_maskVector_eq
#print axioms maskVector_injective_of_lt
#print axioms coefficientsOfSelection5_selectionOfCoefficients5
#print axioms span_five_maskVectors_eq_top_iff

end BilinearComplexity.NormalizedBinaryCompactMaskSemantics
