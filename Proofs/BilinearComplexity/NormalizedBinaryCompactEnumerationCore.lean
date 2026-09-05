import Mathlib.Data.Nat.Bitwise
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option maxRecDepth 1000000

/-!
# Compact normalized binary support enumeration core

This module implements a semantic-free hot loop over strictly increasing
five-tuples of canonical term indices. It uses literal tensor XOR masks and
mixed-radix factor masks. Separate frozen modules certify concrete tables,
and a semantic bridge connects this representation to normalized carriers.
-/

namespace BilinearComplexity.NormalizedBinaryCompactEnumeration

/-- Primitive data needed by the compact five-support checker. -/
structure PackedProfile where
  first : Nat
  second : Nat
  third : Nat
  termCount : Nat
  tensorMask : Nat → Nat

/-- The packed profile corresponding to normalized profile `221`. -/
def packed221 : PackedProfile where
  first := 2
  second := 2
  third := 1
  termCount := 9
  tensorMask
    | 0 => 1
    | 1 => 2
    | 2 => 3
    | 3 => 4
    | 4 => 8
    | 5 => 12
    | 6 => 5
    | 7 => 10
    | 8 => 15
    | _ => 0

/-- The packed profile corresponding to normalized profile `411`. -/
def packed411 : PackedProfile where
  first := 4
  second := 1
  third := 1
  termCount := 15
  tensorMask
    | 0 => 1
    | 1 => 2
    | 2 => 3
    | 3 => 4
    | 4 => 5
    | 5 => 6
    | 6 => 7
    | 7 => 8
    | 8 => 9
    | 9 => 10
    | 10 => 11
    | 11 => 12
    | 12 => 13
    | 13 => 14
    | 14 => 15
    | _ => 0

/-- The packed profile corresponding to normalized profile `321`. -/
def packed321 : PackedProfile where
  first := 3
  second := 2
  third := 1
  termCount := 21
  tensorMask
    | 0 => 1
    | 1 => 2
    | 2 => 3
    | 3 => 4
    | 4 => 8
    | 5 => 12
    | 6 => 5
    | 7 => 10
    | 8 => 15
    | 9 => 16
    | 10 => 32
    | 11 => 48
    | 12 => 17
    | 13 => 34
    | 14 => 51
    | 15 => 20
    | 16 => 40
    | 17 => 60
    | 18 => 21
    | 19 => 42
    | 20 => 63
    | _ => 0

/-- The packed profile corresponding to normalized profile `222`. -/
def packed222 : PackedProfile where
  first := 2
  second := 2
  third := 2
  termCount := 27
  tensorMask
    | 0 => 1
    | 1 => 2
    | 2 => 3
    | 3 => 4
    | 4 => 8
    | 5 => 12
    | 6 => 5
    | 7 => 10
    | 8 => 15
    | 9 => 16
    | 10 => 32
    | 11 => 48
    | 12 => 64
    | 13 => 128
    | 14 => 192
    | 15 => 80
    | 16 => 160
    | 17 => 240
    | 18 => 17
    | 19 => 34
    | 20 => 51
    | 21 => 68
    | 22 => 136
    | 23 => 204
    | 24 => 85
    | 25 => 170
    | 26 => 255
    | _ => 0

example : packed221.termCount = 9 := rfl
example : packed411.tensorMask 14 = 15 := rfl
example : packed321.tensorMask 20 = 63 := rfl
example : packed222.tensorMask 26 = 255 := rfl
example : packed222.tensorMask 27 = 0 := rfl

/-- Fold a function over `length` consecutive natural numbers without
materializing an intermediate range. -/
def foldRange {α : Type} (f : α → Nat → α) : α → Nat → Nat → α
  | acc, _, 0 => acc
  | acc, start, length + 1 =>
      foldRange f (f acc start) (start + 1) length

example : foldRange (fun acc i => acc + i) 0 3 4 = 18 := by decide

/-- Universal Boolean quantification over a consecutive natural interval. -/
def allRange (start length : Nat) (predicate : Nat → Bool) : Bool :=
  foldRange (fun result i => result && predicate i) true start length

/-- Existential Boolean quantification over a consecutive natural interval. -/
def anyRange (start length : Nat) (predicate : Nat → Bool) : Bool :=
  foldRange (fun result i => result || predicate i) false start length

private theorem foldRange_and_eq_true_iff (predicate : Nat → Bool)
    (acc : Bool) (start length : Nat) :
    foldRange (fun result i => result && predicate i) acc start length = true ↔
      acc = true ∧ ∀ i, start ≤ i → i < start + length → predicate i = true := by
  induction length generalizing acc start with
  | zero =>
      simp only [foldRange, Nat.add_zero]
      constructor
      · intro hacc
        exact ⟨hacc, fun i hle hlt => False.elim (Nat.not_lt_of_ge hle hlt)⟩
      · exact fun h => h.1
  | succ length ih =>
      rw [foldRange, ih]
      simp only [Bool.and_eq_true]
      constructor
      · rintro ⟨⟨hacc, hstart⟩, htail⟩
        refine ⟨hacc, fun i hle hlt => ?_⟩
        by_cases hieq : i = start
        · simpa only [hieq] using hstart
        · apply htail i <;> omega
      · rintro ⟨hacc, hall⟩
        refine ⟨⟨hacc, hall start (Nat.le_refl start) (by omega)⟩,
          fun i hle hlt => hall i (by omega) (by omega)⟩

/-- Universal interval reflection for the primitive non-materializing fold. -/
theorem allRange_eq_true_iff (start length : Nat) (predicate : Nat → Bool) :
    allRange start length predicate = true ↔
      ∀ i, start ≤ i → i < start + length → predicate i = true := by
  rw [allRange, foldRange_and_eq_true_iff]
  simp only [true_and]

example : allRange 2 3 (fun i => i < 5) = true := by decide
example : anyRange 4 3 (fun i => i == 5) = true := by decide

/-- The five input masks XORed according to the low five bits of `selection`. -/
def selectedXor5 (x0 x1 x2 x3 x4 selection : Nat) : Nat :=
  Nat.xor (if selection.testBit 0 then x0 else 0)
    (Nat.xor (if selection.testBit 1 then x1 else 0)
      (Nat.xor (if selection.testBit 2 then x2 else 0)
        (Nat.xor (if selection.testBit 3 then x3 else 0)
          (if selection.testBit 4 then x4 else 0))))

example : selectedXor5 1 2 4 8 16 21 = 21 := by decide

/-- Whether five packed binary vectors generate every mask below `2^d`. -/
def spans5 (d x0 x1 x2 x3 x4 : Nat) : Bool :=
  allRange 0 (2 ^ d) fun target =>
    anyRange 0 32 fun selection =>
      selectedXor5 x0 x1 x2 x3 x4 selection == target

example : spans5 2 1 2 0 0 0 = true := by decide
example : spans5 2 1 1 1 1 1 = false := by decide

/-- Mixed-radix factor masks of the canonical term with the given index. -/
def termFactors (p : PackedProfile) (index : Nat) : Nat × Nat × Nat :=
  let thirdCount := 2 ^ p.third - 1
  let secondCount := 2 ^ p.second - 1
  let third := index % thirdCount + 1
  let quotient := index / thirdCount
  let second := quotient % secondCount + 1
  let first := quotient / secondCount + 1
  (first, second, third)

example : termFactors packed221 0 = (1, 1, 1) := by decide
example : termFactors packed221 8 = (3, 3, 1) := by decide
example : termFactors packed222 26 = (3, 3, 3) := by decide

/-- Exact-factor-profile reflection for five canonical term indices. -/
def exactProfile5 (p : PackedProfile) (a b c d e : Nat) : Bool :=
  let fa := termFactors p a
  let fb := termFactors p b
  let fc := termFactors p c
  let fd := termFactors p d
  let fe := termFactors p e
  spans5 p.first fa.1 fb.1 fc.1 fd.1 fe.1 &&
    spans5 p.second fa.2.1 fb.2.1 fc.2.1 fd.2.1 fe.2.1 &&
    spans5 p.third fa.2.2 fb.2.2 fc.2.2 fd.2.2 fe.2.2

/-- Whether five canonical terms have zero packed tensor evaluation and exact
factor profile. The XOR gate precedes all span work. -/
def accepts5 (p : PackedProfile) (a b c d e : Nat) : Bool :=
  Nat.xor (p.tensorMask a)
    (Nat.xor (p.tensorMask b)
      (Nat.xor (p.tensorMask c)
        (Nat.xor (p.tensorMask d) (p.tensorMask e)))) == 0 &&
    exactProfile5 p a b c d e

example : accepts5 packed221 0 1 3 4 8 = true := by decide

/-- A compact code for five canonical term indices. -/
structure FiveCode where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
  deriving DecidableEq, Repr

/-- Whether a five-code is strictly increasing and lies in a packed carrier. -/
def FiveCode.Valid (p : PackedProfile) (q : FiveCode) : Prop :=
  q.a < q.b ∧ q.b < q.c ∧ q.c < q.d ∧ q.d < q.e ∧ q.e < p.termCount

instance (p : PackedProfile) (q : FiveCode) : Decidable (q.Valid p) := by
  unfold FiveCode.Valid
  infer_instance

/-- Whether the packed support represented by a five-code passes the exact
support checker. -/
def FiveCode.accepted (p : PackedProfile) (q : FiveCode) : Bool :=
  accepts5 p q.a q.b q.c q.d q.e

example : FiveCode.Valid packed221 ⟨0, 1, 3, 4, 8⟩ := by decide
example : FiveCode.accepted packed221 ⟨0, 1, 3, 4, 8⟩ = true := by decide

/-- Whether every supplied code is valid and accepted and the table has no
duplicate codes. -/
def exactTableSound (p : PackedProfile) (table : List FiveCode) : Bool :=
  decide table.Nodup && table.all fun q => decide (q.Valid p) && q.accepted p

/-- Whether every accepted increasing five-code occurs in the supplied literal
table. This checks the full canonical five-subset search without constructing
its output list. -/
def exactTableComplete (p : PackedProfile) (table : List FiveCode) : Bool :=
  allRange 0 p.termCount fun a =>
    allRange (a + 1) (p.termCount - (a + 1)) fun b =>
      allRange (b + 1) (p.termCount - (b + 1)) fun c =>
        allRange (c + 1) (p.termCount - (c + 1)) fun d =>
          allRange (d + 1) (p.termCount - (d + 1)) fun e =>
            !accepts5 p a b c d e || table.contains ⟨a, b, c, d, e⟩

/-- Complete exact-table check: no duplicate or false entries and no omitted
accepted increasing five-code. -/
def exactTableCheck (p : PackedProfile) (table : List FiveCode) : Bool :=
  exactTableSound p table && exactTableComplete p table

example : exactTableSound packed221 [⟨0, 1, 3, 4, 8⟩] = true := by decide

/-- Count accepted strictly increasing five-tuples of term indices. -/
def exactSupportCount (p : PackedProfile) : Nat :=
  foldRange (fun total a =>
    foldRange (fun total b =>
      foldRange (fun total c =>
        foldRange (fun total d =>
          foldRange (fun total e =>
            if accepts5 p a b c d e then total + 1 else total)
            total (d + 1) (p.termCount - (d + 1)))
          total (c + 1) (p.termCount - (c + 1)))
        total (b + 1) (p.termCount - (b + 1)))
      total (a + 1) (p.termCount - (a + 1)))
    0 0 p.termCount

/-- Count accepted increasing five-tuples whose first index is fixed. -/
def exactSupportCountAtFirst (p : PackedProfile) (a : Nat) : Nat :=
  foldRange (fun total b =>
    foldRange (fun total c =>
      foldRange (fun total d =>
        foldRange (fun total e =>
          if accepts5 p a b c d e then total + 1 else total)
          total (d + 1) (p.termCount - (d + 1)))
        total (c + 1) (p.termCount - (c + 1)))
      total (b + 1) (p.termCount - (b + 1)))
    0 (a + 1) (p.termCount - (a + 1))

/-- Count accepted increasing five-tuples over a consecutive range of first
indices. -/
def exactSupportCountFirstBlock (p : PackedProfile) (start length : Nat) : Nat :=
  foldRange (fun total a => total + exactSupportCountAtFirst p a)
    0 start length

end BilinearComplexity.NormalizedBinaryCompactEnumeration
