import NumberComplexity.AdditionChain
import ShearEC.ShearCircuit

/-!
# Addition chains as fresh-target monomial shear programs

This file proves the exact bridge between shortest addition chains and a
faithful multiplication-register model.  The model has one input register
containing `x`.  Every counted operation chooses two existing registers,
allocates a fresh register initialized to zero, and applies a shear
`z ← z + u * v`.  Thus the new register contains the product and all old
registers are retained as permitted garbage.  Registers are never mixed by
free affine operations in this model.

The restriction is essential to the contract: `ShearCircuit.Circuit` also
allows arbitrary free affine layers, so the theorem below does not identify
`NumberComplexity.l` with an infimum over all such broad circuits.  It also
makes no clean-scratch claim.
-/

set_option autoImplicit false

namespace ShearEC.ShearAdditionChain

open NumberComplexity

/-- A fresh-target monomial shear program, indexed by the exponents in its
registers (newest register first).  `input` supplies `x = x^1`; `shear` retains
all old registers and puts `x^(a+b)` in a fresh zero target by multiplying
registers containing `x^a` and `x^b`.  The source indices are proof-relevant
program data, not merely an existential validity certificate. -/
inductive MonomialShearProgram : List ℕ → Type
  | input : MonomialShearProgram [1]
  | shear {exponents : List ℕ} (program : MonomialShearProgram exponents)
      (left right : Fin exponents.length) :
      MonomialShearProgram
        ((exponents.get left + exponents.get right) :: exponents)

namespace MonomialShearProgram

/-- The number of fresh-target multiply-add shears in a monomial program. -/
def shearCount : {exponents : List ℕ} → MonomialShearProgram exponents → ℕ
  | _, .input => 0
  | _, .shear program _ _ => shearCount program + 1

/-- Forgetting source-register indices from a monomial program gives an
addition chain with the same newest-first exponent list. -/
theorem isAddChain : {exponents : List ℕ} →
    MonomialShearProgram exponents → IsAddChain exponents
  | _, .input => .one
  | _, .shear program left right =>
      .add (List.get_mem _ left) (List.get_mem _ right) (isAddChain program)

/-- The program's counted shears equal the number of addition steps in its
exponent list. -/
theorem shearCount_eq_chainSteps {exponents : List ℕ}
    (program : MonomialShearProgram exponents) :
    program.shearCount = chainSteps exponents := by
  induction program with
  | input => rfl
  | @shear exponents program left right ih =>
      rw [shearCount, ih, chainSteps_cons,
        program.isAddChain.length_eq_chainSteps_add_one]

end MonomialShearProgram

-- Joint satisfiability and boundary checks for the indexed program model.
example : Nonempty (MonomialShearProgram [1]) := ⟨.input⟩
example : Nonempty (MonomialShearProgram [2, 1]) := by
  exact ⟨.shear .input ⟨0, by decide⟩ ⟨0, by decide⟩⟩
example (program : MonomialShearProgram [2, 1]) : program.shearCount = 1 := by
  rw [program.shearCount_eq_chainSteps]
  rfl

/-- Every addition chain can be equipped with concrete source-register indices
to make a fresh-target monomial shear program. -/
theorem nonempty_monomialShearProgram_of_isAddChain {exponents : List ℕ}
    (hchain : IsAddChain exponents) :
    Nonempty (MonomialShearProgram exponents) := by
  induction hchain with
  | one => exact ⟨.input⟩
  | @add exponents a b ha hb hchain ih =>
      obtain ⟨program⟩ := ih
      obtain ⟨left, hleft⟩ := List.get_of_mem ha
      obtain ⟨right, hright⟩ := List.get_of_mem hb
      refine ⟨?_⟩
      simpa only [hleft, hright] using
        (MonomialShearProgram.shear program left right)

/-- A list is the exponent trace of a source-indexed monomial shear program if
and only if it is an addition chain. -/
theorem nonempty_monomialShearProgram_iff_isAddChain {exponents : List ℕ} :
    Nonempty (MonomialShearProgram exponents) ↔ IsAddChain exponents := by
  constructor
  · rintro ⟨program⟩
    exact program.isAddChain
  · exact nonempty_monomialShearProgram_of_isAddChain

/-- A monomial shear computation producing `x^n`: its newest (output) register
has exponent `n`.  Older registers are unrestricted garbage powers and remain
available throughout the computation. -/
structure MonomialShearComputation (n : ℕ) where
  exponents : List ℕ
  program : MonomialShearProgram exponents
  output_eq : exponents.head? = some n

/-- The minimum number of fresh-target monomial shears that produce `x^n`.
This is an infimum over proof-relevant programs.  At `n = 0` the program type
is empty and the value is the documented `Nat.iInf` junk value `0`, matching
`NumberComplexity.l 0`; the theorem of interest is honest for `n ≠ 0`. -/
noncomputable def minimumMonomialShears (n : ℕ) : ℕ :=
  ⨅ computation : MonomialShearComputation n, computation.program.shearCount

/-- Any concrete monomial shear computation bounds its minimum cost from
above. -/
theorem minimumMonomialShears_le {n : ℕ}
    (computation : MonomialShearComputation n) :
    minimumMonomialShears n ≤ computation.program.shearCount :=
  Nat.sInf_le (Set.mem_range_self computation)

/-- There is no monomial shear computation of `x^0` from the sole input `x`:
all exponents in a valid program are positive. -/
instance instIsEmptyMonomialShearComputationZero :
    IsEmpty (MonomialShearComputation 0) :=
  ⟨fun computation => by
    let chain : AdditionChain 0 :=
      ⟨computation.exponents, computation.program.isAddChain,
        computation.output_eq⟩
    exact isEmptyElim chain⟩

/-- Every positive exponent has a monomial shear computation, obtained by
putting source indices on an addition chain. -/
theorem nonempty_monomialShearComputation_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    Nonempty (MonomialShearComputation n) := by
  let ⟨chain⟩ := nonempty_additionChain_of_ne_zero hn
  obtain ⟨program⟩ :=
    nonempty_monomialShearProgram_of_isAddChain chain.property.1
  exact ⟨⟨chain.val, program, chain.property.2⟩⟩

/-- For a positive exponent, the minimum monomial-shear cost is attained by a
concrete computation. -/
theorem exists_shearCount_eq_minimumMonomialShears {n : ℕ} (hn : n ≠ 0) :
    ∃ computation : MonomialShearComputation n,
      computation.program.shearCount = minimumMonomialShears n := by
  haveI hnonempty : Nonempty (MonomialShearComputation n) :=
    nonempty_monomialShearComputation_of_ne_zero hn
  have hmem : minimumMonomialShears n ∈
      Set.range fun computation : MonomialShearComputation n =>
        computation.program.shearCount :=
    Nat.sInf_mem (Set.range_nonempty _)
  rwa [Set.mem_range] at hmem

/-- A broad-model shear with a fresh zero target distinct from both source
registers produces the product of those sources.  If they contain `x^a` and
`x^b`, the target contains `x^(a+b)`.  This is the operational justification
for one constructor of `MonomialShearProgram` costing one
`ShearCircuit.Gate.shear`. -/
theorem gate_shear_zero_target_pow {R : Type*} [CommSemiring R] {m : ℕ}
    (registers : Fin m → R) (target left right : Fin m)
    (_htl : target ≠ left) (_htr : target ≠ right) (x : R) (a b : ℕ)
    (htarget : registers target = 0) (hleft : registers left = x ^ a)
    (hright : registers right = x ^ b) :
    (ShearCircuit.Gate.shear left right target).app registers target =
      x ^ (a + b) := by
  simp [ShearCircuit.Gate.app, htarget, hleft, hright, pow_add]

/-- The three register indices of one shear-only instruction. -/
structure ShearInstruction (m : ℕ) where
  left : Fin m
  right : Fin m
  target : Fin m

namespace ShearInstruction

variable {m : ℕ}

/-- Interpret a shear-only instruction as an actual `ShearCircuit.Gate.shear`. -/
def gate (instruction : ShearInstruction m) (R : Type*) :
    ShearCircuit.Gate m R :=
  .shear instruction.left instruction.right instruction.target

/-- Shift an instruction into the tail of a register file with one new leading
register. -/
def succ (instruction : ShearInstruction m) : ShearInstruction (m + 1) :=
  ⟨instruction.left.succ, instruction.right.succ, instruction.target.succ⟩

/-- Execute a list of shear-only instructions using the actual operational
semantics of `ShearCircuit.Gate.shear`. -/
def run {R : Type*} [CommSemiring R] (instructions : List (ShearInstruction m))
    (registers : Fin m → R) : Fin m → R :=
  instructions.foldl
    (fun state instruction => (instruction.gate R).app state) registers

/-- Running concatenated instruction lists runs the left list first and the
right list second. -/
theorem run_append {R : Type*} [CommSemiring R]
    (first second : List (ShearInstruction m)) (registers : Fin m → R) :
    run (first ++ second) registers = run second (run first registers) := by
  simp only [run, List.foldl_append]

/-- Converting instructions to a broad-model circuit does not change their
operational behavior. -/
theorem run_eq_circuit_run {R : Type*} [CommSemiring R]
    (instructions : List (ShearInstruction m)) (registers : Fin m → R) :
    run instructions registers =
      ShearCircuit.Circuit.run (instructions.map fun instruction => instruction.gate R)
        registers := by
  simp only [run, ShearCircuit.Circuit.run, List.foldl_map]

/-- Shifting a shear instruction preserves a leading register and performs the
original shear on the tail registers. -/
theorem succ_gate_app {R : Type*} [CommSemiring R]
    (instruction : ShearInstruction m) (z : R) (registers : Fin m → R) :
    (instruction.succ.gate R).app (Fin.cases z registers) =
      Fin.cases z ((instruction.gate R).app registers) := by
  funext index
  refine Fin.cases ?_ (fun i => ?_) index
  · simp [succ, gate, ShearCircuit.Gate.app,
      (Fin.succ_ne_zero instruction.target).symm]
  · simp [succ, gate, ShearCircuit.Gate.app]

/-- Shifting every instruction preserves a leading register and executes the
original instruction list on the tail. -/
theorem run_map_succ {R : Type*} [CommSemiring R]
    (instructions : List (ShearInstruction m)) (z : R)
    (registers : Fin m → R) :
    run (instructions.map succ) (Fin.cases z registers) =
      Fin.cases z (run instructions registers) := by
  induction instructions generalizing registers with
  | nil => rfl
  | cons instruction instructions ih =>
      change run (instructions.map succ)
          ((instruction.succ.gate R).app (Fin.cases z registers)) =
        Fin.cases z
          (run instructions ((instruction.gate R).app registers))
      rw [instruction.succ_gate_app]
      exact ih ((instruction.gate R).app registers)

end ShearInstruction

namespace MonomialShearProgram

/-- Compile a monomial program to fixed-width shear instructions.  Older
instructions are shifted right and each constructor uses register `0` as its
fresh target. -/
def instructions : {exponents : List ℕ} → MonomialShearProgram exponents →
    List (ShearInstruction exponents.length)
  | _, .input => []
  | _, .shear program left right =>
      (instructions program).map ShearInstruction.succ ++
        [⟨left.succ, right.succ, 0⟩]

/-- The fixed-width initial register file: the oldest register contains `x`,
and every target that will be allocated by the program starts at zero. -/
def initialRegisters {R : Type*} [Zero R] : {exponents : List ℕ} →
    MonomialShearProgram exponents → R → Fin exponents.length → R
  | _, .input, x => fun _ => x
  | _, .shear program _ _, x => Fin.cases 0 (initialRegisters program x)

/-- Compile a monomial program into the broad circuit syntax.  The resulting
circuit contains only `Gate.shear` gates and no affine layers. -/
def circuit (R : Type*) {exponents : List ℕ}
    (program : MonomialShearProgram exponents) :
    ShearCircuit.Circuit exponents.length R :=
  program.instructions.map fun instruction => instruction.gate R

/-- Compilation emits exactly one instruction for each program shear. -/
theorem length_instructions {exponents : List ℕ}
    (program : MonomialShearProgram exponents) :
    program.instructions.length = program.shearCount := by
  induction program with
  | input => rfl
  | shear program left right ih =>
      simp [instructions, shearCount, ih]

/-- A list converted to actual shear gates has shear count equal to its
instruction-list length. -/
theorem shearCount_map_gate (R : Type*) {m : ℕ}
    (instructions : List (ShearInstruction m)) :
    ShearCircuit.Circuit.shearCount
        (instructions.map fun instruction => instruction.gate R) =
      instructions.length := by
  induction instructions with
  | nil => rfl
  | cons instruction instructions ih =>
      change
        ShearCircuit.Circuit.shearCount
            (instructions.map fun instruction => instruction.gate R) + 1 =
          instructions.length + 1
      rw [ih]

/-- A circuit obtained by compilation has exactly the program's shear count. -/
theorem shearCount_circuit (R : Type*) {exponents : List ℕ}
    (program : MonomialShearProgram exponents) :
    ShearCircuit.Circuit.shearCount (program.circuit R) = program.shearCount := by
  rw [circuit, shearCount_map_gate,
    program.length_instructions]

/-- Running the compiled actual shear circuit from its one-input/all-zero-scratch
initial state leaves `x^e` in every register whose indexed exponent is `e`.
This is the operational realization theorem for the full source-indexed
program, not just a one-gate identity. -/
theorem run_circuit_eq_pow {R : Type*} [CommSemiring R]
    {exponents : List ℕ} (program : MonomialShearProgram exponents) (x : R) :
    ShearCircuit.Circuit.run (program.circuit R) (program.initialRegisters x) =
      fun index => x ^ exponents.get index := by
  rw [circuit, ← ShearInstruction.run_eq_circuit_run]
  induction program with
  | input =>
      funext index
      fin_cases index
      simp [instructions, initialRegisters, ShearInstruction.run]
  | @shear exponents program left right ih =>
      rw [instructions, initialRegisters, ShearInstruction.run_append,
        ShearInstruction.run_map_succ, ih]
      funext index
      refine Fin.cases ?_ (fun i => ?_) index
      · simp [ShearInstruction.run, ShearInstruction.gate,
          ShearCircuit.Gate.app, pow_add]
      · simp [ShearInstruction.run, ShearInstruction.gate,
          ShearCircuit.Gate.app]

end MonomialShearProgram

-- The operational hypotheses are jointly satisfiable with distinct sources
-- and a fresh zero target.
example :
    let registers : Fin 3 → ℕ := ![2, 2, 0]
    (ShearCircuit.Gate.shear 0 1 2).app registers 2 = 2 ^ 2 := by
  decide

/-- **Addition-chain / monomial-shear bridge.**  For every positive `n`, the
minimum number of fresh-zero-target multiplication shears needed to produce
`x^n`, retaining arbitrary garbage power registers, is exactly the shortest
addition-chain length `l n`.

This equality is for the explicit monomial register model above, not for the
broader `ShearCircuit.Circuit` language with free affine mixing, and it makes
no assertion about returning scratch registers to zero. -/
theorem minimumMonomialShears_eq_l (n : ℕ) (hn : n ≠ 0) :
    minimumMonomialShears n = l n := by
  apply le_antisymm
  · obtain ⟨chain, hchain⟩ := exists_chainSteps_eq_l hn
    obtain ⟨program⟩ :=
      nonempty_monomialShearProgram_of_isAddChain chain.property.1
    let computation : MonomialShearComputation n :=
      ⟨chain.val, program, chain.property.2⟩
    calc
      minimumMonomialShears n ≤ computation.program.shearCount :=
        minimumMonomialShears_le computation
      _ = chainSteps chain.val := program.shearCount_eq_chainSteps
      _ = l n := hchain
  · obtain ⟨computation, hcomputation⟩ :=
      exists_shearCount_eq_minimumMonomialShears hn
    rw [← hcomputation, computation.program.shearCount_eq_chainSteps]
    exact l_le_chainSteps
      ⟨computation.exponents, computation.program.isAddChain,
        computation.output_eq⟩

/-- A shortest positive-exponent computation is realized by an actual
shear-only `ShearCircuit.Circuit`: its syntactic shear count is `l n`, it has
no affine gates by construction, and its complete run has the specified power
in every register (including permitted garbage registers). -/
theorem exists_optimal_shear_circuit_realization {R : Type*} [CommSemiring R]
    {n : ℕ} (hn : n ≠ 0) :
    ∃ (exponents : List ℕ) (program : MonomialShearProgram exponents),
      exponents.head? = some n ∧
        ShearCircuit.Circuit.shearCount (program.circuit R) = l n ∧
          ∀ x : R,
            ShearCircuit.Circuit.run (program.circuit R)
                (program.initialRegisters x) =
              fun index => x ^ exponents.get index := by
  obtain ⟨computation, hcost⟩ :=
    exists_shearCount_eq_minimumMonomialShears hn
  refine ⟨computation.exponents, computation.program, computation.output_eq, ?_, ?_⟩
  · rw [computation.program.shearCount_circuit, hcost,
      minimumMonomialShears_eq_l n hn]
  · exact fun x => computation.program.run_circuit_eq_pow x

/-- Extending the equality to all naturals using the empty-`iInf` convention:
at `n = 0`, both sides are the default value `0` because no computation or
addition chain exists.  This is bookkeeping at zero, not an operational bridge;
use `minimumMonomialShears_eq_l` for the nondegenerate claim. -/
theorem minimumMonomialShears_eq_l_all_with_empty_infimum_at_zero (n : ℕ) :
    minimumMonomialShears n = l n := by
  by_cases hn : n = 0
  · subst n
    rw [l_zero]
    exact Nat.iInf_of_empty _
  · exact minimumMonomialShears_eq_l n hn

-- Ground checks for the computation type and both boundary conventions.
example : Nonempty (MonomialShearComputation 1) :=
  ⟨⟨[1], .input, rfl⟩⟩
example : Nonempty (MonomialShearComputation 2) := by
  exact ⟨⟨[2, 1], .shear .input ⟨0, by decide⟩ ⟨0, by decide⟩, rfl⟩⟩
example : minimumMonomialShears 0 = 0 := by
  exact Nat.iInf_of_empty _
example : minimumMonomialShears 1 = 0 := by
  rw [minimumMonomialShears_eq_l_all_with_empty_infimum_at_zero, l_one]
example : minimumMonomialShears 2 = 1 := by
  rw [minimumMonomialShears_eq_l_all_with_empty_infimum_at_zero, l_two]

#check @minimumMonomialShears_eq_l
#check @minimumMonomialShears_eq_l_all_with_empty_infimum_at_zero
#print axioms MonomialShearProgram.isAddChain
#print axioms MonomialShearProgram.shearCount_eq_chainSteps
#print axioms nonempty_monomialShearProgram_of_isAddChain
#print axioms nonempty_monomialShearProgram_iff_isAddChain
#print axioms gate_shear_zero_target_pow
#print axioms MonomialShearProgram.shearCount_circuit
#print axioms MonomialShearProgram.run_circuit_eq_pow
#print axioms exists_optimal_shear_circuit_realization
#print axioms minimumMonomialShears_eq_l
#print axioms minimumMonomialShears_eq_l_all_with_empty_infimum_at_zero

end ShearEC.ShearAdditionChain
