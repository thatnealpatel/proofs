import BilinearComplexity.BinaryCircuit
import BilinearComplexity.BinaryKMIndexedData
import BilinearComplexity.BinaryKMNativeToggle

set_option autoImplicit false

/-!
# Effective contextual compilation of indexed binary KM reductions

The working factor order is `(b,c,a)`, with the literally common factor third.
`compile` computes the changed-index order, uses suffix sums to represent the
binary residual walk, and concatenates occupancy-selected native paths from
`BinaryKMNativeToggle`. The suffix invariant permits zero or repeated residuals
and arbitrary admissible endpoint context, including occupied auxiliary atoms.

The public certificate contains its actual `MovePath`, the selected local costs,
and a finite carrier. Theorems prove exact endpoint coverage and evaluation,
`m ≤ length ≤ 2m ≤ 2n`, source-card altitude, outside-carrier preservation,
endpoint restoration, original-factor-span containment, and composition.
-/

namespace BilinearComplexity.BinaryKMReduction

open scoped symmDiff
open BinaryCircuit
open BinaryAmbientCarrier
open BinaryKMNativeToggle
open BinaryAmbientMoves
open NormalizedBinaryCarrier (F2)

universe u uB uC uA v

variable {α : Type u} [DecidableEq α]
variable {B : Type uB} {C : Type uC} {A : Type uA}
variable [AddCommGroup B] [AddCommGroup C] [AddCommGroup A]
variable [Module F2 B] [Module F2 C] [Module F2 A]
variable [DecidableEq B] [DecidableEq C] [DecidableEq A]

/-- The admissible indexed binary KM input, in working factor order `(b,c,a)`. -/
abbrev KMData (n : Nat) :=
  BinaryKMIndexedData.Data (B := B) (C := C) (A := A) n

/-- The deterministic order used by the compiler is the native order of the
effectively filtered changed-index finset. -/
def changedList {n : Nat} (d : KMData (B := B) (C := C) (A := A) n) : List (Fin n) :=
  d.changedIndices.sort (· ≤ ·)

/-- The carrier atom represented by a nonzero residual. -/
def residualAtom {n : Nat} (d : KMData (B := B) (C := C) (A := A) n)
    (x : B) (hx : x ≠ 0) : Carrier B C A :=
  (⟨x, hx⟩, ⟨d.c0, d.c0_ne_zero⟩, ⟨d.a, d.a_ne_zero⟩)

/-- The always-nonzero bridge atom attached to an active index. -/
def bridgeAtom {n : Nat} (d : KMData (B := B) (C := C) (A := A) n)
    (i : Fin n) : Carrier B C A :=
  (⟨d.b i, d.b_ne_zero i⟩, ⟨d.c0, d.c0_ne_zero⟩, ⟨d.a, d.a_ne_zero⟩)

/-- A zero residual has no carrier atom; a nonzero residual gives the unique
common-`c0,a` pivot atom. -/
def residualPivot {n : Nat} (d : KMData (B := B) (C := C) (A := A) n)
    (x : B) : State B C A :=
  if hx : x = 0 then ∅ else {residualAtom d x hx}

example {n : Nat} (d : KMData (B := B) (C := C) (A := A) n) :
    residualAtom d d.b0 d.b0_ne_zero = d.pivot := rfl

example {n : Nat} (d : KMData (B := B) (C := C) (A := A) n) (i : Fin n) :
    bridgeAtom d i = residualAtom d (d.b i) (d.b_ne_zero i) := rfl

example {n : Nat} (d : KMData (B := B) (C := C) (A := A) n) :
    residualPivot d 0 = ∅ := by simp [residualPivot]

/-- The deterministic changed list has exactly as many entries as there are
changed indices. -/
theorem changedList_length {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) :
    (changedList d).length = d.changedIndices.card := by
  exact Finset.length_sort (s := d.changedIndices) (· ≤ ·)

/-- The deterministic changed list contains no repeated index. -/
theorem changedList_nodup {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) :
    (changedList d).Nodup := by
  exact Finset.sort_nodup d.changedIndices (· ≤ ·)

/-- The initial nonzero residual pivot is exactly the indexed KM pivot. -/
theorem residualPivot_b0 {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) :
    residualPivot d d.b0 = {d.pivot} := by
  simp only [residualPivot, d.b0_ne_zero, ↓reduceDIte, residualAtom,
    BinaryKMIndexedData.Data.pivot]


/-- The residual after consuming an ordered list is obtained by adding each
indexed contribution to the supplied initial residual. -/
def residual {ι : Type*} {G : Type v} [Add G]
    (b : ι → G) (initial : G) : List ι → G
  | [] => initial
  | i :: indices => residual b (initial + b i) indices

example {ι : Type*} {G : Type v} [Add G]
    (b : ι → G) (initial : G) : residual b initial [] = initial := rfl

/-- A recursively computed residual is the initial value plus the ordered sum
of the consumed contributions. -/
theorem residual_eq_initial_add_sum
    {ι : Type*} {G : Type v} [AddCommMonoid G]
    (b : ι → G) (initial : G) (indices : List ι) :
    residual b initial indices = initial + (indices.map b).sum := by
  induction indices generalizing initial with
  | nil => simp only [residual, List.map_nil, List.sum_nil, add_zero]
  | cons i indices ih =>
      rw [residual, ih]
      simp only [List.map_cons, List.sum_cons, add_assoc]

/-- Over `F2`, consuming contributions whose sum is the initial residual ends
at zero; no intermediate residual is required to be nonzero. -/
theorem residual_eq_zero_of_eq_sum
    {ι : Type*} {G : Type v} [AddCommGroup G]
    [Module (ZMod 2) G]
    (b : ι → G) (initial : G) (indices : List ι)
    (hsum : initial = (indices.map b).sum) :
    residual b initial indices = 0 := by
  rw [residual_eq_initial_add_sum, hsum]
  exact BinaryCircuit.add_self_eq_zero _

/-- The effective changed-index order consumes the initial residual exactly,
including inputs whose intermediate residuals are zero or repeated. -/
theorem residual_changedList_eq_zero {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) :
    residual d.b d.b0 (changedList d) = 0 := by
  apply residual_eq_zero_of_eq_sum
  rw [← d.changed_b_sum_eq_b0]
  have hmultiset := congrArg (Multiset.map d.b)
    (Finset.sort_eq d.changedIndices (· ≤ ·))
  exact (congrArg Multiset.sum hmultiset).symm

/-- The residual attached to a recursion suffix is the sum of its unprocessed
first factors. -/
def suffixResidual {n : Nat} (d : KMData (B := B) (C := C) (A := A) n)
    (indices : List (Fin n)) : B :=
  (indices.map d.b).sum

/-- The source atoms indexed by an unprocessed recursion suffix. -/
def remainingSource {n : Nat} (d : KMData (B := B) (C := C) (A := A) n)
    (indices : List (Fin n)) : State B C A :=
  indices.toFinset.image d.sourceTerm

/-- The target atoms whose changed indices have already been processed. -/
def processedTarget {n : Nat} (d : KMData (B := B) (C := C) (A := A) n)
    (indices : List (Fin n)) : State B C A :=
  (d.changedIndices \ indices.toFinset).image d.targetTerm

/-- The non-residual part of the compiler state at a recursion suffix. -/
def baseState {n : Nat} (d : KMData (B := B) (C := C) (A := A) n)
    (context : State B C A) (indices : List (Fin n)) : State B C A :=
  d.fixedState context ∪ remainingSource d indices ∪ processedTarget d indices

/-- The exact compiler boundary at a recursion suffix. -/
def boundaryState {n : Nat} (d : KMData (B := B) (C := C) (A := A) n)
    (context : State B C A) (indices : List (Fin n)) : State B C A :=
  baseState d context indices ∆ residualPivot d (suffixResidual d indices)

/-- A suffix cursor records exactly the recursion facts needed to identify its
remaining and processed changed indices. -/
structure SuffixValid {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (indices : List (Fin n)) : Prop where
  nodup : indices.Nodup
  subset_changed : indices.toFinset ⊆ d.changedIndices

example {n : Nat} (d : KMData (B := B) (C := C) (A := A) n)
    (context : State B C A) :
    boundaryState d context [] = d.fixedState context ∪ d.workTarget := by
  simp only [boundaryState, baseState, remainingSource, processedTarget,
    suffixResidual, residualPivot, List.map_nil, List.sum_nil, ↓reduceDIte,
    List.toFinset_nil, Finset.image_empty, Finset.union_empty,
    Finset.sdiff_empty, BinaryKMIndexedData.Data.workTarget,
    BinaryKMIndexedData.Data.changedTarget]
  exact symmDiff_bot _

/-- A changed source atom cannot collide with any residual atom because its
second factor differs from `c0`. -/
theorem sourceTerm_ne_residualAtom {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (i : Fin n)
    (x : B) (hx : x ≠ 0) :
    d.sourceTerm i ≠ residualAtom d x hx := by
  intro heq
  have hc := congrArg (fun z : Carrier B C A => z.2.1.1) heq
  simp only [BinaryKMIndexedData.Data.sourceTerm, residualAtom] at hc
  apply d.outputC_ne_zero i
  rw [hc]
  exact BinaryCircuit.add_self_eq_zero _

/-- A changed target atom cannot collide with any residual atom because its
nonzero source second factor would otherwise vanish. -/
theorem targetTerm_ne_residualAtom {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (i : Fin n)
    (x : B) (hx : x ≠ 0) :
    d.targetTerm i ≠ residualAtom d x hx := by
  intro heq
  have hc := congrArg (fun z : Carrier B C A => z.2.1.1) heq
  simp only [BinaryKMIndexedData.Data.targetTerm, residualAtom] at hc
  apply d.c_ne_zero i
  have hcancel := congrArg (fun z : C => z + d.c0) hc
  simpa only [add_assoc, BinaryCircuit.add_self_eq_zero, add_zero] using hcancel

/-- The bridge differs from its source atom. -/
theorem bridgeAtom_ne_sourceTerm {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (i : Fin n) :
    bridgeAtom d i ≠ d.sourceTerm i := by
  intro heq
  have hc := congrArg (fun z : Carrier B C A => z.2.1.1) heq
  simp only [bridgeAtom, BinaryKMIndexedData.Data.sourceTerm] at hc
  apply d.outputC_ne_zero i
  rw [← hc]
  exact BinaryCircuit.add_self_eq_zero _

/-- The bridge differs from its target atom. -/
theorem bridgeAtom_ne_targetTerm {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (i : Fin n) :
    bridgeAtom d i ≠ d.targetTerm i := by
  intro heq
  have hc := congrArg (fun z : Carrier B C A => z.2.1.1) heq
  simp only [bridgeAtom, BinaryKMIndexedData.Data.targetTerm] at hc
  apply d.c_ne_zero i
  have hcancel := congrArg (fun z : C => z + d.c0) hc
  simpa only [add_assoc, BinaryCircuit.add_self_eq_zero, zero_add, add_zero] using hcancel.symm

/-- A changed source differs from its target. -/
theorem sourceTerm_ne_targetTerm {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (i : Fin n) :
    d.sourceTerm i ≠ d.targetTerm i := by
  intro heq
  have hc := congrArg (fun z : Carrier B C A => z.2.1.1) heq
  simp only [BinaryKMIndexedData.Data.sourceTerm,
    BinaryKMIndexedData.Data.targetTerm] at hc
  apply d.c0_ne_zero
  apply add_left_cancel (a := d.c i)
  simpa only [add_zero] using hc.symm

/-- Distinct nonzero coefficients give distinct residual atoms. -/
theorem residualAtom_ne_residualAtom {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n)
    (x y : B) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    residualAtom d x hx ≠ residualAtom d y hy := by
  intro heq
  exact hxy (congrArg (fun z : Carrier B C A => z.1.1) heq)

/-- The three-support local law used whenever either adjacent residual is zero. -/
theorem threeSupportLaws {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (i : Fin n) :
    ThreeSupportLaws (bridgeAtom d i) (d.sourceTerm i) (d.targetTerm i) := by
  refine {
    join := {
      first_eq := rfl
      third_eq := rfl
      output_first := rfl
      output_second := add_comm _ _
      output_third := rfl }
    p_ne_t := bridgeAtom_ne_sourceTerm d i
    p_ne_u := bridgeAtom_ne_targetTerm d i
    t_ne_u := sourceTerm_ne_targetTerm d i }

/-- The four-support local law for two adjacent nonzero residuals. -/
theorem fourSupportLaws {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (i : Fin n)
    (x : B) (hx : x ≠ 0) (hnext : x + d.b i ≠ 0) :
    FourSupportLaws
      (residualAtom d x hx)
      (residualAtom d (x + d.b i) hnext)
      (d.sourceTerm i) (d.targetTerm i) (bridgeAtom d i) := by
  have hpq : residualAtom d x hx ≠ residualAtom d (x + d.b i) hnext := by
    apply residualAtom_ne_residualAtom d x (x + d.b i) hx hnext
    intro hxb
    apply d.b_ne_zero i
    have hzero : 0 = d.b i := calc
      0 = x + x := (BinaryCircuit.add_self_eq_zero x).symm
      _ = x + (x + d.b i) := congrArg (fun z : B => x + z) hxb
      _ = d.b i := by rw [← add_assoc, BinaryCircuit.add_self_eq_zero, zero_add]
    exact hzero.symm
  have hpv : residualAtom d x hx ≠ bridgeAtom d i := by
    intro heq
    apply hnext
    have hxb := congrArg (fun z : Carrier B C A => z.1.1) heq
    simp only [residualAtom, bridgeAtom] at hxb
    rw [hxb]
    exact BinaryCircuit.add_self_eq_zero _
  have hqv : residualAtom d (x + d.b i) hnext ≠ bridgeAtom d i := by
    intro heq
    apply hx
    have hxb := congrArg (fun z : Carrier B C A => z.1.1) heq
    simp only [residualAtom, bridgeAtom] at hxb
    have hcancel := congrArg (fun z : B => z + d.b i) hxb
    simpa only [add_assoc, BinaryCircuit.add_self_eq_zero, add_zero] using hcancel
  refine {
    flip := {
      common_third := rfl
      target_left_first := rfl
      target_left_second := rfl
      target_left_third := rfl
      target_right_first := rfl
      target_right_second := ?_
      target_right_third := rfl }
    pivot_join := {
      second_eq := rfl
      third_eq := rfl
      output_first := ?_
      output_second := rfl
      output_third := rfl }
    bridge_join := (threeSupportLaws d i).join
    p_ne_q := hpq
    p_ne_t := (sourceTerm_ne_residualAtom d i x hx).symm
    p_ne_u := (targetTerm_ne_residualAtom d i x hx).symm
    p_ne_v := hpv
    q_ne_t := (sourceTerm_ne_residualAtom d i (x + d.b i) hnext).symm
    q_ne_u := (targetTerm_ne_residualAtom d i (x + d.b i) hnext).symm
    q_ne_v := hqv
    t_ne_u := sourceTerm_ne_targetTerm d i
    t_ne_v := (bridgeAtom_ne_sourceTerm d i).symm
    u_ne_v := (bridgeAtom_ne_targetTerm d i).symm }
  · exact (ZModModule.sub_eq_add _ _).symm
  · calc
      d.b i = 0 + d.b i := (zero_add _).symm
      _ = (x + x) + d.b i := by rw [BinaryCircuit.add_self_eq_zero]
      _ = x + (x + d.b i) := add_assoc _ _ _

/-- The deterministic full suffix has exactly the changed index finset. -/
theorem changedList_toFinset {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) :
    (changedList d).toFinset = d.changedIndices := by
  ext i
  simp only [List.mem_toFinset, changedList, Finset.mem_sort]

/-- The deterministic full suffix is a valid compiler cursor. -/
theorem changedList_valid {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) :
    SuffixValid d (changedList d) := by
  refine ⟨changedList_nodup d, ?_⟩
  rw [changedList_toFinset]

/-- The common core on the two sides of one indexed exchange. -/
def stepCore {n : Nat} (d : KMData (B := B) (C := C) (A := A) n)
    (context : State B C A) (i : Fin n) (indices : List (Fin n)) : State B C A :=
  d.fixedState context ∪ remainingSource d indices ∪ processedTarget d (i :: indices)

/-- A valid nonempty cursor has a valid tail. -/
theorem SuffixValid.tail {n : Nat}
    {d : KMData (B := B) (C := C) (A := A) n} {i : Fin n} {indices : List (Fin n)}
    (h : SuffixValid d (i :: indices)) : SuffixValid d indices := by
  refine ⟨h.nodup.tail, ?_⟩
  intro j hj
  apply h.subset_changed
  simpa only [List.toFinset_cons, Finset.mem_insert] using Or.inr hj

/-- The head of a valid cursor is a changed index. -/
theorem SuffixValid.head_mem_changed {n : Nat}
    {d : KMData (B := B) (C := C) (A := A) n} {i : Fin n} {indices : List (Fin n)}
    (h : SuffixValid d (i :: indices)) : i ∈ d.changedIndices := by
  apply h.subset_changed
  simp only [List.toFinset_cons, Finset.mem_insert, true_or]

/-- The head of a valid cursor does not recur in its tail. -/
theorem SuffixValid.head_not_mem_tail {n : Nat}
    {d : KMData (B := B) (C := C) (A := A) n} {i : Fin n} {indices : List (Fin n)}
    (h : SuffixValid d (i :: indices)) : i ∉ indices.toFinset := by
  simpa only [List.mem_toFinset] using (List.nodup_cons.mp h.nodup).1

/-- Processing the head inserts exactly its target into the processed-target
state. -/
theorem processedTarget_tail_eq_insert {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n)
    (i : Fin n) (indices : List (Fin n)) (h : SuffixValid d (i :: indices)) :
    processedTarget d indices =
      insert (d.targetTerm i) (processedTarget d (i :: indices)) := by
  ext x
  simp only [processedTarget, Finset.mem_image, List.toFinset_cons,
    Finset.mem_sdiff, Finset.mem_insert]
  constructor
  · rintro ⟨j, ⟨hjChanged, hjTail⟩, rfl⟩
    by_cases hji : j = i
    · exact Or.inl (congrArg d.targetTerm hji)
    · exact Or.inr ⟨j, ⟨hjChanged, not_or.mpr ⟨hji, hjTail⟩⟩, rfl⟩
  · rintro (rfl | ⟨j, ⟨hjChanged, hjCons⟩, rfl⟩)
    · exact ⟨i, ⟨h.head_mem_changed, h.head_not_mem_tail⟩, rfl⟩
    · exact ⟨j, ⟨hjChanged, fun hjTail => hjCons (Or.inr hjTail)⟩, rfl⟩

/-- Before one exchange the base state is the common core with its source
inserted. -/
theorem baseState_cons_eq_insert {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (context : State B C A)
    (i : Fin n) (indices : List (Fin n)) :
    baseState d context (i :: indices) =
      insert (d.sourceTerm i) (stepCore d context i indices) := by
  ext x
  simp only [baseState, stepCore, remainingSource, List.toFinset_cons,
    Finset.image_insert, Finset.mem_union, Finset.mem_insert]
  tauto

/-- After one exchange the base state is the same common core with its target
inserted. -/
theorem baseState_tail_eq_insert {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (context : State B C A)
    (i : Fin n) (indices : List (Fin n)) (h : SuffixValid d (i :: indices)) :
    baseState d context indices =
      insert (d.targetTerm i) (stepCore d context i indices) := by
  rw [baseState, processedTarget_tail_eq_insert d i indices h]
  ext x
  simp only [stepCore, Finset.mem_union, Finset.mem_insert]
  tauto

/-- The source of a valid step is absent from its common core. -/
theorem sourceTerm_not_mem_stepCore {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (context : State B C A)
    (i : Fin n) (indices : List (Fin n)) (h : SuffixValid d (i :: indices))
    (hcontext : d.ContextAdmissible context) :
    d.sourceTerm i ∉ stepCore d context i indices := by
  simp only [stepCore, Finset.mem_union, not_or]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro hfixed
    apply Finset.disjoint_left.mp (d.fixedState_disjoint_workSource context hcontext)
      hfixed
    rw [BinaryKMIndexedData.Data.workSource, Finset.mem_insert]
    exact Or.inr (Finset.mem_image.mpr ⟨i, h.head_mem_changed, rfl⟩)
  · intro hremaining
    rcases Finset.mem_image.mp hremaining with ⟨j, hj, heq⟩
    have hji : j = i := d.sourceTerm_injective heq
    subst j
    exact h.head_not_mem_tail hj
  · intro hprocessed
    apply Finset.disjoint_left.mp d.changedSource_disjoint_changedTarget
      (Finset.mem_image.mpr ⟨i, h.head_mem_changed, rfl⟩)
    rcases Finset.mem_image.mp hprocessed with ⟨j, hj, heq⟩
    exact Finset.mem_image.mpr ⟨j, (Finset.mem_sdiff.mp hj).1, heq⟩

/-- The target of a valid step is absent from its common core. -/
theorem targetTerm_not_mem_stepCore {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (context : State B C A)
    (i : Fin n) (indices : List (Fin n)) (h : SuffixValid d (i :: indices))
    (hcontext : d.ContextAdmissible context) :
    d.targetTerm i ∉ stepCore d context i indices := by
  simp only [stepCore, Finset.mem_union, not_or]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro hfixed
    apply Finset.disjoint_left.mp (d.fixedState_disjoint_workTarget context hcontext)
      hfixed
    exact Finset.mem_image.mpr ⟨i, h.head_mem_changed, rfl⟩
  · intro hremaining
    apply Finset.disjoint_left.mp d.changedSource_disjoint_changedTarget
    · rcases Finset.mem_image.mp hremaining with ⟨j, hj, heq⟩
      exact Finset.mem_image.mpr ⟨j, h.tail.subset_changed hj, heq⟩
    · exact Finset.mem_image.mpr ⟨i, h.head_mem_changed, rfl⟩
  · intro hprocessed
    rcases Finset.mem_image.mp hprocessed with ⟨j, hj, heq⟩
    have hji : j = i := d.targetTerm_injective heq
    subst j
    exact (Finset.mem_sdiff.mp hj).2 (by
      simp only [List.toFinset_cons, Finset.mem_insert, true_or])

/-- Toggling the source and target exchanges the two base states. -/
theorem baseState_step_toggle {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (context : State B C A)
    (i : Fin n) (indices : List (Fin n)) (h : SuffixValid d (i :: indices))
    (hcontext : d.ContextAdmissible context) :
    baseState d context (i :: indices) ∆ {d.sourceTerm i, d.targetTerm i} =
      baseState d context indices := by
  rw [baseState_cons_eq_insert, baseState_tail_eq_insert d context i indices h]
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  have hsource := sourceTerm_not_mem_stepCore d context i indices h hcontext
  have htarget := targetTerm_not_mem_stepCore d context i indices h hcontext
  have hne := sourceTerm_ne_targetTerm d i
  by_cases hxs : x = d.sourceTerm i
  · subst x
    simp [hsource, hne]
  · by_cases hxt : x = d.targetTerm i
    · subst x
      simp [htarget, hne.symm]
    · simp [hxs, hxt]

/-- One indexed exchange carries the exact residual boundary to the next
suffix boundary. -/
theorem boundaryState_step_toggle {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (context : State B C A)
    (i : Fin n) (indices : List (Fin n)) (h : SuffixValid d (i :: indices))
    (hcontext : d.ContextAdmissible context) :
    boundaryState d context (i :: indices) ∆
        (residualPivot d (suffixResidual d (i :: indices)) ∆
          residualPivot d (suffixResidual d indices) ∆
          {d.sourceTerm i, d.targetTerm i}) =
      boundaryState d context indices := by
  rw [boundaryState, boundaryState]
  have hbase := baseState_step_toggle d context i indices h hcontext
  calc
    (baseState d context (i :: indices) ∆
          residualPivot d (suffixResidual d (i :: indices))) ∆
        (residualPivot d (suffixResidual d (i :: indices)) ∆
          residualPivot d (suffixResidual d indices) ∆
          {d.sourceTerm i, d.targetTerm i}) =
      (baseState d context (i :: indices) ∆ {d.sourceTerm i, d.targetTerm i}) ∆
        residualPivot d (suffixResidual d indices) := by
          rw [← symmDiff_assoc, ← symmDiff_assoc, symmDiff_symmDiff_cancel_right]
          ac_rfl
    _ = baseState d context indices ∆ residualPivot d (suffixResidual d indices) := by
      rw [hbase]

/-- Execute a list of residual-walk toggles. A step stores its next residual
pivot set and its non-pivot payload; its support is the symmetric difference of
the current pivot, next pivot, and payload. -/
def foldToggleState (D pivot : Finset α) :
    List (Finset α × Finset α) → Finset α
  | [] => D
  | (nextPivot, payload) :: steps =>
      foldToggleState (D ∆ (pivot ∆ nextPivot ∆ payload)) nextPivot steps

/-- The final residual-pivot set of a list of residual-walk steps. -/
def terminalPivot (pivot : Finset α) :
    List (Finset α × Finset α) → Finset α
  | [] => pivot
  | (nextPivot, _) :: steps => terminalPivot nextPivot steps

/-- The symmetric difference of all non-pivot payloads in a residual walk. -/
def payloadToggle : List (Finset α × Finset α) → Finset α
  | [] => ∅
  | (_, payload) :: steps => payload ∆ payloadToggle steps

example (D pivot : Finset α) : foldToggleState D pivot [] = D := rfl

example (pivot : Finset α) : terminalPivot pivot [] = pivot := rfl

example : payloadToggle ([] : List (Finset α × Finset α)) = ∅ := rfl

private theorem symmDiff_step_cancel
    (D pivot nextPivot payload final rest : Finset α) :
    (D ∆ (pivot ∆ nextPivot ∆ payload)) ∆ nextPivot ∆ final ∆ rest =
      D ∆ pivot ∆ final ∆ (payload ∆ rest) := by
  have hreorder : D ∆ (pivot ∆ nextPivot ∆ payload) =
      (D ∆ pivot ∆ payload) ∆ nextPivot := by
    ac_rfl
  rw [hreorder, symmDiff_symmDiff_cancel_right]
  ac_rfl

/-- Residual pivots in a fold cancel pairwise: only the initial and terminal
pivots and the accumulated payload remain. -/
theorem foldToggleState_eq
    (D pivot : Finset α) (steps : List (Finset α × Finset α)) :
    foldToggleState D pivot steps =
      D ∆ pivot ∆ terminalPivot pivot steps ∆ payloadToggle steps := by
  induction steps generalizing D pivot with
  | nil =>
      simp only [foldToggleState, terminalPivot, payloadToggle]
      rw [symmDiff_symmDiff_cancel_right]
      exact (symmDiff_bot D).symm
  | cons step steps ih =>
      rcases step with ⟨nextPivot, payload⟩
      rw [foldToggleState, ih]
      simp only [terminalPivot, payloadToggle]
      exact symmDiff_step_cancel D pivot nextPivot payload
        (terminalPivot nextPivot steps) (payloadToggle steps)

/-- If the residual walk ends at the empty pivot, the fold toggles precisely
its initial pivot and accumulated payload. -/
theorem foldToggleState_eq_of_terminal_empty
    (D pivot : Finset α) (steps : List (Finset α × Finset α))
    (hterminal : terminalPivot pivot steps = ∅) :
    foldToggleState D pivot steps = D ∆ pivot ∆ payloadToggle steps := by
  rw [foldToggleState_eq, hterminal]
  have hempty : D ∆ pivot ∆ ∅ = D ∆ pivot := symmDiff_bot (D ∆ pivot)
  rw [hempty]

/-- The terminal endpoint cardinality of a concrete path is at most its
altitude. -/
theorem end_card_le_altitude
    {R : Finset α → Finset α → Prop} {D E : Finset α}
    (path : MovePath R D E) : E.card ≤ path.altitude := by
  cases path with
  | singleton =>
      simp only [MovePath.altitude]
      exact Nat.le_refl _
  | snoc path edge =>
      simp only [MovePath.altitude]
      exact Nat.le_max_right _ _

/-- Concatenation adds the lengths of concrete paths. -/
theorem trans_length
    {R : Finset α → Finset α → Prop} {D E F : Finset α}
    (path : MovePath R D E) (tail : MovePath R E F) :
    (path.trans tail).length = path.length + tail.length := by
  induction tail with
  | singleton => simp only [MovePath.trans, MovePath.length, Nat.add_zero]
  | snoc tail edge ih =>
      simp only [MovePath.trans, MovePath.length, ih, Nat.add_assoc]

/-- Concatenation takes the maximum of the altitudes of concrete paths. -/
theorem trans_altitude
    {R : Finset α → Finset α → Prop} {D E F : Finset α}
    (path : MovePath R D E) (tail : MovePath R E F) :
    (path.trans tail).altitude = max path.altitude tail.altitude := by
  induction tail with
  | singleton =>
      simp only [MovePath.trans, MovePath.altitude]
      exact (Nat.max_eq_left (end_card_le_altitude path)).symm
  | snoc tail edge ih =>
      simp only [MovePath.trans, MovePath.altitude, ih, Nat.max_assoc]

/-- Paths whose altitudes share a common bound retain that bound after
concatenation. -/
theorem trans_altitude_le
    {R : Finset α → Finset α → Prop} {D E F : Finset α} {bound : ℕ}
    (path : MovePath R D E) (tail : MovePath R E F)
    (hpath : path.altitude ≤ bound) (htail : tail.altitude ≤ bound) :
    (path.trans tail).altitude ≤ bound := by
  rw [trans_altitude]
  exact Nat.max_le.mpr ⟨hpath, htail⟩

/-- Toggling a finite support increases cardinality by at most the support
cardinality. -/
theorem card_symmDiff_le_add (D support : Finset α) :
    (D ∆ support).card ≤ D.card + support.card := by
  calc
    (D ∆ support).card ≤ (D ∪ support).card := by
      apply Finset.card_le_card
      intro x hx
      rw [Finset.symmDiff_def] at hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mp hx).1)
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mp hx).1)
    _ ≤ D.card + support.card := Finset.card_union_le D support

/-- A state contained in a fixed part, two lists of current indexed terms, and
a residual-pivot set has the corresponding additive cardinality bound. -/
theorem card_le_fixed_union_lists
    (state fixed pivot : Finset α) (left right : List α)
    (hsubset : state ⊆ fixed ∪ left.toFinset ∪ right.toFinset ∪ pivot) :
    state.card ≤ fixed.card + left.length + right.length + pivot.card := by
  have hcard := Finset.card_le_card hsubset
  have h₁ := Finset.card_union_le (fixed ∪ left.toFinset ∪ right.toFinset) pivot
  have h₂ := Finset.card_union_le (fixed ∪ left.toFinset) right.toFinset
  have h₃ := Finset.card_union_le fixed left.toFinset
  have hleft := List.toFinset_card_le left
  have hright := List.toFinset_card_le right
  omega

/-- Concatenating a path of length at most `2m` with one local path of length at
most two gives the next doubled fold bound. -/
theorem trans_length_le_two_mul_succ
    {R : Finset α → Finset α → Prop} {D E F : Finset α} {m : ℕ}
    (path : MovePath R D E) (tail : MovePath R E F)
    (hpath : path.length ≤ 2 * m) (htail : tail.length ≤ 2) :
    (path.trans tail).length ≤ 2 * (m + 1) := by
  rw [trans_length]
  omega

/-- Concatenating a path with at least `m` edges and a nonempty local path gives
at least `m+1` edges. -/
theorem succ_le_trans_length
    {R : Finset α → Finset α → Prop} {D E F : Finset α} {m : ℕ}
    (path : MovePath R D E) (tail : MovePath R E F)
    (hpath : m ≤ path.length) (htail : 1 ≤ tail.length) :
    m + 1 ≤ (path.trans tail).length := by
  rw [trans_length]
  omega

/-- A single residual exchange uses only its two residual pivots, its source
and target, and the bridge for its index. -/
def stepCarrier {n : Nat} (d : KMData (B := B) (C := C) (A := A) n)
    (i : Fin n) (x : B) : State B C A :=
  residualPivot d x ∪ residualPivot d (x + d.b i) ∪
    {d.sourceTerm i, d.targetTerm i, bridgeAtom d i}

/-- An active source is never a residual pivot, including the zero residual. -/
theorem sourceTerm_not_mem_residualPivot {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (i : Fin n) (x : B) :
    d.sourceTerm i ∉ residualPivot d x := by
  unfold residualPivot
  split
  · exact Finset.notMem_empty _
  · simpa only [Finset.mem_singleton] using sourceTerm_ne_residualAtom d i x _

/-- An active target is never a residual pivot, including the zero residual. -/
theorem targetTerm_not_mem_residualPivot {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (i : Fin n) (x : B) :
    d.targetTerm i ∉ residualPivot d x := by
  unfold residualPivot
  split
  · exact Finset.notMem_empty _
  · simpa only [Finset.mem_singleton] using targetTerm_ne_residualAtom d i x _

/-- The residual recursion expressed in suffix coordinates is the specified
binary update, with no intermediate nonzero condition. -/
theorem suffixResidual_cons_add {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (i : Fin n) (indices : List (Fin n)) :
    suffixResidual d (i :: indices) + d.b i = suffixResidual d indices := by
  simp only [suffixResidual, List.map_cons, List.sum_cons]
  calc
    (d.b i + (indices.map d.b).sum) + d.b i =
        (d.b i + d.b i) + (indices.map d.b).sum := by ac_rfl
    _ = (indices.map d.b).sum := by rw [BinaryCircuit.add_self_eq_zero, zero_add]

/-- The moving source is present at every valid recursion boundary. -/
theorem sourceTerm_mem_boundaryState {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (context : State B C A)
    (i : Fin n) (indices : List (Fin n)) :
    d.sourceTerm i ∈ boundaryState d context (i :: indices) := by
  rw [boundaryState, Finset.mem_symmDiff]
  refine Or.inl ⟨?_, sourceTerm_not_mem_residualPivot d i _⟩
  rw [baseState_cons_eq_insert]
  exact Finset.mem_insert_self _ _

/-- The moving target is absent at every valid recursion boundary. -/
theorem targetTerm_not_mem_boundaryState {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (context : State B C A)
    (i : Fin n) (indices : List (Fin n)) (h : SuffixValid d (i :: indices))
    (hcontext : d.ContextAdmissible context) :
    d.targetTerm i ∉ boundaryState d context (i :: indices) := by
  have hcore := targetTerm_not_mem_stepCore d context i indices h hcontext
  have hpivot := targetTerm_not_mem_residualPivot d i (suffixResidual d (i :: indices))
  simp [boundaryState, Finset.mem_symmDiff, baseState_cons_eq_insert,
    hcore, hpivot, (sourceTerm_ne_targetTerm d i).symm]

private theorem residual_support_three {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (i : Fin n) (x : B)
    (hzero : x = 0 ∨ x + d.b i = 0) :
    residualPivot d x ∆ residualPivot d (x + d.b i) ∆
        {d.sourceTerm i, d.targetTerm i} =
      threeSupport (bridgeAtom d i) (d.sourceTerm i) (d.targetTerm i) := by
  have hxb : x = 0 ∨ x = d.b i := by
    rcases hzero with hzero | hzero
    · exact Or.inl hzero
    · right
      have hcancel := congrArg (fun z : B => z + d.b i) hzero
      simpa only [add_assoc, BinaryCircuit.add_self_eq_zero, zero_add, add_zero] using hcancel
  have hdisjoint : Disjoint ({bridgeAtom d i} : State B C A)
      {d.sourceTerm i, d.targetTerm i} := by
    simp [Finset.disjoint_singleton_left, bridgeAtom_ne_sourceTerm,
      bridgeAtom_ne_targetTerm]
  rcases hxb with rfl | rfl
  · simp only [residualPivot, dif_pos rfl, zero_add, d.b_ne_zero i, ↓reduceDIte]
    change (∅ : State B C A) ∆ {bridgeAtom d i} ∆ {d.sourceTerm i, d.targetTerm i} = _
    have hz : (∅ : State B C A) ∆ {bridgeAtom d i} = {bridgeAtom d i} := bot_symmDiff _
    rw [hz, Finset.symmDiff_eq_union hdisjoint]
    ext z
    simp only [threeSupport, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  · simp only [residualPivot, d.b_ne_zero i, ↓reduceDIte,
      BinaryCircuit.add_self_eq_zero, dif_pos rfl]
    change ({bridgeAtom d i} : State B C A) ∆ ∅ ∆ {d.sourceTerm i, d.targetTerm i} = _
    have hz : ({bridgeAtom d i} : State B C A) ∆ ∅ = {bridgeAtom d i} := symmDiff_bot _
    rw [hz, Finset.symmDiff_eq_union hdisjoint]
    ext z
    simp only [threeSupport, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]

private theorem residual_support_four {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (i : Fin n) (x : B)
    (hx : x ≠ 0) (hnext : x + d.b i ≠ 0) :
    residualPivot d x ∆ residualPivot d (x + d.b i) ∆
        {d.sourceTerm i, d.targetTerm i} =
      {residualAtom d x hx, residualAtom d (x + d.b i) hnext,
        d.sourceTerm i, d.targetTerm i} := by
  let laws := fourSupportLaws d i x hx hnext
  have h₁ : Disjoint ({residualAtom d x hx} : State B C A)
      {residualAtom d (x + d.b i) hnext} := by
    simpa only [Finset.disjoint_singleton_left, Finset.mem_singleton] using laws.p_ne_q
  have h₂ : Disjoint ({residualAtom d x hx, residualAtom d (x + d.b i) hnext} : State B C A)
      {d.sourceTerm i, d.targetTerm i} := by
    simp [Finset.disjoint_insert_left, Finset.disjoint_singleton_left,
      laws.p_ne_t, laws.p_ne_u, laws.q_ne_t, laws.q_ne_u,
      laws.p_ne_t.symm, laws.p_ne_u.symm, laws.q_ne_t.symm, laws.q_ne_u.symm]
  simp only [residualPivot, hx, hnext, ↓reduceDIte]
  rw [Finset.symmDiff_eq_union h₁]
  change ({residualAtom d x hx, residualAtom d (x + d.b i) hnext} : State B C A) ∆
    {d.sourceTerm i, d.targetTerm i} = _
  rw [Finset.symmDiff_eq_union h₂]
  ext z
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_assoc]

/-- Compile one indexed residual exchange by testing the two residuals and
then delegating occupancy selection to the native three/four-support compilers. -/
def compileResidualStep {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (D : State B C A)
    (i : Fin n) (x : B) (ht : d.sourceTerm i ∈ D) (hu : d.targetTerm i ∉ D) :
    LocalCompilation D
      (D ∆ (residualPivot d x ∆ residualPivot d (x + d.b i) ∆
        {d.sourceTerm i, d.targetTerm i})) (stepCarrier d i x) := by
  by_cases hx : x = 0
  · have heq := residual_support_three d i x (Or.inl hx)
    rw [heq]
    let lc := compileThreeSupportToggle D (bridgeAtom d i) (d.sourceTerm i)
      (d.targetTerm i) (threeSupportLaws d i) ht hu
    refine ⟨lc.path, lc.length_pos, lc.length_le_two, lc.altitude_le, ?_⟩
    intro X hX z hz
    apply lc.outside_fixed X hX z
    intro hsmall
    apply hz
    have hmember : z = bridgeAtom d i ∨ z = d.sourceTerm i ∨ z = d.targetTerm i := by
      simpa only [threeSupport, Finset.mem_insert, Finset.mem_singleton] using hsmall
    simp only [stepCarrier, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  · by_cases hnext : x + d.b i = 0
    · have heq := residual_support_three d i x (Or.inr hnext)
      rw [heq]
      let lc := compileThreeSupportToggle D (bridgeAtom d i) (d.sourceTerm i)
        (d.targetTerm i) (threeSupportLaws d i) ht hu
      refine ⟨lc.path, lc.length_pos, lc.length_le_two, lc.altitude_le, ?_⟩
      intro X hX z hz
      apply lc.outside_fixed X hX z
      intro hsmall
      apply hz
      have hmember : z = bridgeAtom d i ∨ z = d.sourceTerm i ∨ z = d.targetTerm i := by
        simpa only [threeSupport, Finset.mem_insert, Finset.mem_singleton] using hsmall
      simp only [stepCarrier, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    · rw [residual_support_four d i x hx hnext]
      let lc := compileFourSupportToggle D (residualAtom d x hx)
        (residualAtom d (x + d.b i) hnext) (d.sourceTerm i) (d.targetTerm i)
        (bridgeAtom d i) (fourSupportLaws d i x hx hnext) ht hu
      refine ⟨lc.path, lc.length_pos, lc.length_le_two, lc.altitude_le, ?_⟩
      intro X hX z hz
      apply lc.outside_fixed X hX z
      intro hsmall
      apply hz
      simpa only [stepCarrier, residualPivot, hx, hnext, ↓reduceDIte,
        fourSupport, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        or_assoc] using hsmall

/-- Compile the head of a valid suffix to the next exact boundary, without a
caller-supplied path or occupancy schedule. -/
def compileStep {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (context : State B C A)
    (i : Fin n) (indices : List (Fin n)) (h : SuffixValid d (i :: indices))
    (hcontext : d.ContextAdmissible context) :
    LocalCompilation (boundaryState d context (i :: indices))
      (boundaryState d context indices)
      (stepCarrier d i (suffixResidual d (i :: indices))) := by
  have heq : boundaryState d context (i :: indices) ∆
      (residualPivot d (suffixResidual d (i :: indices)) ∆
        residualPivot d (suffixResidual d (i :: indices) + d.b i) ∆
        {d.sourceTerm i, d.targetTerm i}) = boundaryState d context indices := by
    rw [suffixResidual_cons_add]
    exact boundaryState_step_toggle d context i indices h hcontext
  exact heq ▸ compileResidualStep d (boundaryState d context (i :: indices)) i
    (suffixResidual d (i :: indices)) (sourceTerm_mem_boundaryState d context i indices)
    (targetTerm_not_mem_boundaryState d context i indices h hcontext)

/-- The effective carrier accumulated along an entire residual suffix. -/
def foldCarrier {n : Nat} (d : KMData (B := B) (C := C) (A := A) n) :
    List (Fin n) → State B C A
  | [] => ∅
  | i :: indices => stepCarrier d i (suffixResidual d (i :: indices)) ∪ foldCarrier d indices

example {n : Nat} (d : KMData (B := B) (C := C) (A := A) n) :
    foldCarrier d [] = ∅ := rfl

/-- Residual pivot states contain at most one atom, including at zero. -/
theorem residualPivot_card_le_one {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (x : B) :
    (residualPivot d x).card ≤ 1 := by
  unfold residualPivot
  split <;> simp

/-- Valid suffixes retain at most one indexed atom for each changed index. -/
theorem baseState_card_le {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (context : State B C A)
    (indices : List (Fin n)) (h : SuffixValid d indices) :
    (baseState d context indices).card ≤ (d.fixedState context).card + d.changedIndices.card := by
  have hpartition := Finset.card_sdiff_add_card d.changedIndices indices.toFinset
  rw [Finset.union_eq_left.mpr h.subset_changed] at hpartition
  have hremaining : (remainingSource d indices).card ≤ indices.toFinset.card :=
    Finset.card_image_le
  have hprocessed : (processedTarget d indices).card ≤
      (d.changedIndices \ indices.toFinset).card := Finset.card_image_le
  have hfirst := Finset.card_union_le (d.fixedState context) (remainingSource d indices)
  have hsecond := Finset.card_union_le
    (d.fixedState context ∪ remainingSource d indices) (processedTarget d indices)
  change ((d.fixedState context ∪ remainingSource d indices) ∪ processedTarget d indices).card ≤ _
  omega

/-- The source endpoint cardinality is the fixed-state cardinality plus the
changed index count and its nonzero pivot. -/
theorem sourceEndpoint_card_eq_fixed_add {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (context : State B C A)
    (hcontext : d.ContextAdmissible context) :
    (d.sourceEndpoint context).card = (d.fixedState context).card + d.changedIndices.card + 1 := by
  rw [d.sourceEndpoint_eq_fixedState_union_workSource,
    Finset.card_union_of_disjoint (d.fixedState_disjoint_workSource context hcontext),
    d.workSource_card, Nat.add_assoc]

/-- Every macro boundary has cardinality no greater than the original source
endpoint, even when residual pivots meet the fixed context. -/
theorem boundaryState_card_le_source {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (context : State B C A)
    (indices : List (Fin n)) (h : SuffixValid d indices)
    (hcontext : d.ContextAdmissible context) :
    (boundaryState d context indices).card ≤ (d.sourceEndpoint context).card := by
  rw [sourceEndpoint_card_eq_fixed_add d context hcontext]
  have hbase := baseState_card_le d context indices h
  have hpivot := residualPivot_card_le_one d (suffixResidual d indices)
  have htoggle := card_symmDiff_le_add (baseState d context indices)
    (residualPivot d (suffixResidual d indices))
  change (baseState d context indices ∆ residualPivot d (suffixResidual d indices)).card ≤ _
  omega

private theorem mem_vertices_trans {R : Finset α → Finset α → Prop}
    {D E F X : Finset α} (p : MovePath R D E) (q : MovePath R E F)
    (hX : X ∈ (p.trans q).vertices) : X ∈ p.vertices ∨ X ∈ q.vertices := by
  induction q with
  | singleton => exact Or.inl hX
  | snoc q edge ih =>
    simp only [MovePath.trans, MovePath.vertices, List.mem_append, List.mem_singleton] at hX ⊢
    rcases hX with hX | hX
    · rcases ih hX with hp | hq
      · exact Or.inl hp
      · exact Or.inr (Or.inl hq)
    · exact Or.inr (Or.inr hX)

/-- An effective suffix compilation records the actual path and each selected
local primitive cost, together with quantitative and outside-carrier laws. -/
structure SuffixCompilation {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (context : State B C A)
    (indices : List (Fin n)) where
  path : MovePath (AllModeMove (U := B) (V := C) (W := A))
    (boundaryState d context indices) (boundaryState d context [])
  localCosts : List Nat
  costs_length : localCosts.length = indices.length
  costs_one_or_two : ∀ c ∈ localCosts, c = 1 ∨ c = 2
  length_eq_sum : path.length = localCosts.sum
  length_lower : indices.length ≤ path.length
  length_upper : path.length ≤ 2 * indices.length
  altitude_le : path.altitude ≤ (d.sourceEndpoint context).card
  outside_fixed : ∀ X, X ∈ path.vertices → ∀ z, z ∉ foldCarrier d indices →
    (z ∈ X ↔ z ∈ boundaryState d context indices)

/-- Compile all changed indices in a valid suffix by structural recursion,
concatenating the actual occupancy-selected native paths. -/
def compileSuffix {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (context : State B C A)
    (hcontext : d.ContextAdmissible context) :
    (indices : List (Fin n)) → SuffixValid d indices → SuffixCompilation d context indices
  | [], h => {
      path := .singleton (boundaryState d context [])
      localCosts := []
      costs_length := rfl
      costs_one_or_two := by simp
      length_eq_sum := by simp only [MovePath.length, List.sum_nil]
      length_lower := Nat.zero_le _
      length_upper := by simp only [MovePath.length, List.length_nil, Nat.mul_zero, le_refl]
      altitude_le := by
        simpa only [MovePath.altitude] using boundaryState_card_le_source d context [] h hcontext
      outside_fixed := by
        intro X hX z _
        have hXe : X = boundaryState d context [] := by
          simpa only [MovePath.vertices, List.mem_singleton] using hX
        rw [hXe] }
  | i :: indices, h => by
      let lc := compileStep d context i indices h hcontext
      let rest := compileSuffix d context hcontext indices h.tail
      refine {
        path := lc.path.trans rest.path
        localCosts := lc.path.length :: rest.localCosts
        costs_length := by simp only [List.length_cons, rest.costs_length]
        costs_one_or_two := ?_
        length_eq_sum := ?_
        length_lower := ?_
        length_upper := ?_
        altitude_le := ?_
        outside_fixed := ?_ }
      · intro c hc
        rcases List.mem_cons.mp hc with hc | hc
        · subst c
          have hlo := lc.length_pos
          have hhi := lc.length_le_two
          omega
        · exact rest.costs_one_or_two c hc
      · rw [trans_length, List.sum_cons, rest.length_eq_sum]
      · rw [trans_length, List.length_cons]
        have hlo := lc.length_pos
        have hr := rest.length_lower
        omega
      · rw [trans_length, List.length_cons]
        have hhi := lc.length_le_two
        have hr := rest.length_upper
        omega
      · apply trans_altitude_le
        · exact le_trans lc.altitude_le (Nat.max_le.mpr
            ⟨boundaryState_card_le_source d context (i :: indices) h hcontext,
              boundaryState_card_le_source d context indices h.tail hcontext⟩)
        · exact rest.altitude_le
      · intro X hX z hz
        have hz₁ : z ∉ stepCarrier d i (suffixResidual d (i :: indices)) := by
          intro hmem
          exact hz (Finset.mem_union_left _ hmem)
        have hz₂ : z ∉ foldCarrier d indices := by
          intro hmem
          exact hz (Finset.mem_union_right _ hmem)
        rcases mem_vertices_trans lc.path rest.path hX with hfirst | hrest
        · exact lc.outside_fixed X hfirst z hz₁
        · exact (rest.outside_fixed X hrest z hz₂).trans
            (lc.outside_fixed _ lc.path.end_mem_vertices z hz₁)

/-- The empty suffix is exactly the complete target endpoint. -/
theorem boundaryState_nil {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (context : State B C A) :
    boundaryState d context [] = d.targetEndpoint context := by
  rw [d.targetEndpoint_eq_fixedState_union_workTarget]
  simp only [boundaryState, baseState, remainingSource, processedTarget,
    suffixResidual, residualPivot, List.map_nil, List.sum_nil, ↓reduceDIte,
    List.toFinset_nil, Finset.image_empty, Finset.union_empty,
    Finset.sdiff_empty, BinaryKMIndexedData.Data.workTarget,
    BinaryKMIndexedData.Data.changedTarget]
  exact symmDiff_bot _

/-- The initial suffix sum equals the supplied nonzero pivot coefficient. -/
theorem suffixResidual_changedList {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) :
    suffixResidual d (changedList d) = d.b0 := by
  rw [← d.changed_b_sum_eq_b0]
  have hmultiset := congrArg (Multiset.map d.b)
    (Finset.sort_eq d.changedIndices (· ≤ ·))
  exact congrArg Multiset.sum hmultiset

/-- The full deterministic suffix is exactly the complete source endpoint. -/
theorem boundaryState_changedList {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (context : State B C A)
    (hcontext : d.ContextAdmissible context) :
    boundaryState d context (changedList d) = d.sourceEndpoint context := by
  rw [boundaryState, suffixResidual_changedList, residualPivot_b0,
    baseState, remainingSource, processedTarget, changedList_toFinset,
    Finset.sdiff_self, Finset.image_empty, Finset.union_empty,
    d.sourceEndpoint_eq_fixedState_union_workSource]
  have hpivot : d.pivot ∉ d.fixedState context := by
    intro hfixed
    exact Finset.disjoint_left.mp (d.fixedState_disjoint_workSource context hcontext)
      hfixed (Finset.mem_insert_self _ _)
  have hdisjoint : Disjoint (d.fixedState context ∪ d.changedSource) {d.pivot} := by
    simp [Finset.disjoint_singleton_right, hpivot, d.pivot_not_mem_changedSource]
  change (d.fixedState context ∪ d.changedSource) ∆ {d.pivot} = _
  rw [Finset.symmDiff_eq_union hdisjoint]
  ext z
  simp only [BinaryKMIndexedData.Data.workSource,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- The public indexed KM certificate contains an actual native path, the
computed support, and exact occupancy-selected costs with no-growth bounds. -/
structure Compilation {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (context : State B C A) where
  path : MovePath (AllModeMove (U := B) (V := C) (W := A))
    (d.sourceEndpoint context) (d.targetEndpoint context)
  localCosts : List Nat
  costs_length : localCosts.length = d.changedIndices.card
  costs_one_or_two : ∀ c ∈ localCosts, c = 1 ∨ c = 2
  length_eq_sum : path.length = localCosts.sum
  length_lower : d.changedIndices.card ≤ path.length
  length_upper : path.length ≤ 2 * d.changedIndices.card
  altitude_le : path.altitude ≤ (d.sourceEndpoint context).card
  carrier : State B C A
  carrier_eq : carrier = d.sourceState ∪ d.targetState ∪ foldCarrier d (changedList d)
  outside_fixed : ∀ X, X ∈ path.vertices → ∀ z, z ∉ carrier →
    (z ∈ X ↔ z ∈ d.sourceEndpoint context)

/-- Reindex a computed path by proved endpoint equalities, without changing
its vertex data. -/
def reindexPath {R : Finset α → Finset α → Prop} {D E D' E' : Finset α}
    (hs : D = D') (ht : E = E') (p : MovePath R D E) : MovePath R D' E' :=
  hs ▸ ht ▸ p

/-- Reindexing retains every executable path observation. -/
theorem reindexPath_observations {R : Finset α → Finset α → Prop}
    {D E D' E' : Finset α} (hs : D = D') (ht : E = E') (p : MovePath R D E) :
    (reindexPath hs ht p).length = p.length ∧
    (reindexPath hs ht p).altitude = p.altitude ∧
    (reindexPath hs ht p).vertices = p.vertices := by
  cases hs
  cases ht
  exact ⟨rfl, rfl, rfl⟩

/-- Compile an arbitrary admissible indexed binary KM family, preprocessing
endpoint overlap and executing each genuinely changed index exactly once. -/
def compile {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (context : State B C A)
    (hcontext : d.ContextAdmissible context) : Compilation d context := by
  let result := compileSuffix d context hcontext (changedList d) (changedList_valid d)
  have hstart := boundaryState_changedList d context hcontext
  have hfinish := boundaryState_nil d context
  let path := reindexPath hstart hfinish result.path
  have hlength : path.length = result.path.length :=
    (reindexPath_observations hstart hfinish result.path).1
  have haltitude : path.altitude = result.path.altitude :=
    (reindexPath_observations hstart hfinish result.path).2.1
  have hvertices : path.vertices = result.path.vertices :=
    (reindexPath_observations hstart hfinish result.path).2.2
  refine {
    path := path
    localCosts := result.localCosts
    costs_length := result.costs_length.trans (changedList_length d)
    costs_one_or_two := result.costs_one_or_two
    length_eq_sum := hlength.trans result.length_eq_sum
    length_lower := ?_
    length_upper := ?_
    altitude_le := haltitude.trans_le result.altitude_le
    carrier := d.sourceState ∪ d.targetState ∪ foldCarrier d (changedList d)
    carrier_eq := rfl
    outside_fixed := ?_ }
  · rw [hlength, ← changedList_length d]
    exact result.length_lower
  · rw [hlength, ← changedList_length d]
    exact result.length_upper
  · intro X hX z hz
    rw [hvertices] at hX
    rw [← hstart]
    exact result.outside_fixed X hX z (fun hmem => hz (Finset.mem_union_right _ hmem))

/-- Every genuinely changed index occurs exactly once in the compiler's
computed order, and every unchanged index occurs zero times. -/
theorem changedList_count {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (i : Fin n) :
    (changedList d).count i = if i ∈ d.changedIndices then 1 else 0 := by
  rw [(changedList_nodup d).count]
  simp only [changedList, Finset.mem_sort]

/-- The selected KM family has a nonempty changed index domain and the doubled
changed-index bound is at most twice the original active arity. -/
theorem changed_count_bounds {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) :
    0 < d.changedIndices.card ∧ d.changedIndices.card ≤ n ∧ 2 * d.changedIndices.card ≤ 2 * n := by
  have hpos := Finset.card_pos.mpr d.changedIndices_nonempty
  have hpartition := d.changedIndices_card_add_unchangedIndices_card
  exact ⟨hpos, by omega, by omega⟩

/-- The compiler's local costs are obtained from its actual recursively
compiled paths, not supplied as an external cost schedule. -/
theorem compileSuffix_localCosts_cons {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (context : State B C A)
    (hcontext : d.ContextAdmissible context) (i : Fin n) (indices : List (Fin n))
    (h : SuffixValid d (i :: indices)) :
    (compileSuffix d context hcontext (i :: indices) h).localCosts =
      (compileStep d context i indices h hcontext).path.length ::
        (compileSuffix d context hcontext indices h.tail).localCosts := rfl

/-- The public path is the exact recursive path with only its endpoint indices
transported through the proved endpoint equations. -/
theorem compile_path_eq {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (context : State B C A)
    (hcontext : d.ContextAdmissible context) :
    (compile d context hcontext).path =
      reindexPath (boundaryState_changedList d context hcontext) (boundaryState_nil d context)
        (compileSuffix d context hcontext (changedList d) (changedList_valid d)).path := rfl

/-- The final native compilation preserves the specified tensor evaluation. -/
theorem compile_endpoint_evaluation {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (context : State B C A)
    (hcontext : d.ContextAdmissible context) :
    stateEvaluation (d.sourceEndpoint context) = stateEvaluation (d.targetEndpoint context) :=
  d.context_endpoint_evaluation context hcontext

/-- The computed native path has the full promised changed-index length and
source-card altitude bounds. -/
theorem compile_bounds {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (context : State B C A)
    (hcontext : d.ContextAdmissible context) :
    0 < d.changedIndices.card ∧
    d.changedIndices.card ≤ (compile d context hcontext).path.length ∧
    (compile d context hcontext).path.length ≤ 2 * d.changedIndices.card ∧
    2 * d.changedIndices.card ≤ 2 * n ∧
    (compile d context hcontext).path.altitude ≤ context.card + n + 1 := by
  refine ⟨(changed_count_bounds d).1, (compile d context hcontext).length_lower,
    (compile d context hcontext).length_upper, (changed_count_bounds d).2.2, ?_⟩
  rw [← d.context_sourceEndpoint_card context hcontext]
  exact (compile d context hcontext).altitude_le

/-- Every context atom is restored at the final endpoint, with no promise that
an auxiliary context atom remains occupied at all intermediate vertices. -/
theorem context_restored {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (context : State B C A) :
    d.targetEndpoint context ∩ context = context := by
  exact Finset.inter_eq_right.mpr (Finset.subset_union_left)

/-- The fixed endpoint-overlap cycles, as well as the supplied context, are
present unchanged again at the final endpoint. -/
theorem fixedState_restored {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (context : State B C A) :
    d.targetEndpoint context ∩ d.fixedState context = d.fixedState context := by
  rw [d.targetEndpoint_eq_fixedState_union_workTarget]
  exact Finset.inter_eq_right.mpr (Finset.subset_union_left)

/-- Membership outside the computed finite carrier is unchanged at every
recorded native vertex. -/
theorem compile_outside_carrier {n : Nat}
    (d : KMData (B := B) (C := C) (A := A) n) (context : State B C A)
    (hcontext : d.ContextAdmissible context) (X : State B C A)
    (hX : X ∈ (compile d context hcontext).path.vertices) :
    X \ (compile d context hcontext).carrier =
      d.sourceEndpoint context \ (compile d context hcontext).carrier := by
  ext z
  simp only [Finset.mem_sdiff]
  by_cases hz : z ∈ (compile d context hcontext).carrier
  · simp [hz]
  · exact and_congr_left (fun _ => (compile d context hcontext).outside_fixed X hX z hz)

/-- Any submodules containing the original local factors contain every factor
of every atom in the effective compiler carrier. -/
theorem Compilation.carrier_factors_mem {n : Nat}
    {d : KMData (B := B) (C := C) (A := A) n} {context : State B C A}
    (cert : Compilation d context)
    (PB : Submodule F2 B) (PC : Submodule F2 C) (PA : Submodule F2 A)
    (hb0 : d.b0 ∈ PB) (hb : ∀ i, d.b i ∈ PB)
    (hc0 : d.c0 ∈ PC) (hc : ∀ i, d.c i ∈ PC) (ha : d.a ∈ PA) :
    ∀ z ∈ cert.carrier, z.1.1 ∈ PB ∧ z.2.1.1 ∈ PC ∧ z.2.2.1 ∈ PA := by
  have hres : ∀ indices : List (Fin n), suffixResidual d indices ∈ PB := by
    intro indices
    induction indices with
    | nil => exact PB.zero_mem
    | cons i indices ih => exact PB.add_mem (hb i) ih
  have hpivot : ∀ (x : B), x ∈ PB → ∀ z ∈ residualPivot d x,
      z.1.1 ∈ PB ∧ z.2.1.1 ∈ PC ∧ z.2.2.1 ∈ PA := by
    intro x hx z hz
    unfold residualPivot at hz
    split at hz
    · exact False.elim (Finset.notMem_empty z hz)
    · have hzEq := Finset.mem_singleton.mp hz
      subst z
      exact ⟨hx, hc0, ha⟩
  have hsource : ∀ z ∈ d.sourceState,
      z.1.1 ∈ PB ∧ z.2.1.1 ∈ PC ∧ z.2.2.1 ∈ PA := by
    intro z hz
    rcases Finset.mem_insert.mp hz with hz | hz
    · subst z
      exact ⟨hb0, hc0, ha⟩
    · rcases Finset.mem_image.mp hz with ⟨i, _, rfl⟩
      exact ⟨hb i, hc i, ha⟩
  have htarget : ∀ z ∈ d.targetState,
      z.1.1 ∈ PB ∧ z.2.1.1 ∈ PC ∧ z.2.2.1 ∈ PA := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, _, rfl⟩
    exact ⟨hb i, PC.add_mem (hc i) hc0, ha⟩
  have hfold : ∀ indices : List (Fin n), ∀ z ∈ foldCarrier d indices,
      z.1.1 ∈ PB ∧ z.2.1.1 ∈ PC ∧ z.2.2.1 ∈ PA := by
    intro indices
    induction indices with
    | nil => intro z hz; exact False.elim (Finset.notMem_empty z hz)
    | cons i indices ih =>
      intro z hz
      rcases Finset.mem_union.mp hz with hstep | htail
      · rcases Finset.mem_union.mp hstep with hpivots | hterms
        · rcases Finset.mem_union.mp hpivots with hbefore | hafter
          · exact hpivot _ (hres (i :: indices)) z hbefore
          · exact hpivot _ (PB.add_mem (hres (i :: indices)) (hb i)) z hafter
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hterms
          rcases hterms with rfl | rfl | rfl
          · exact ⟨hb i, hc i, ha⟩
          · exact ⟨hb i, PC.add_mem (hc i) hc0, ha⟩
          · exact ⟨hb i, hc0, ha⟩
      · exact ih z htail
  intro z hz
  rw [cert.carrier_eq] at hz
  rcases Finset.mem_union.mp hz with hendpoints | haux
  · rcases Finset.mem_union.mp hendpoints with hs | ht
    · exact hsource z hs
    · exact htarget z ht
  · exact hfold _ z haux

/-- All factors used by the effective carrier lie in the corresponding spans
of the original local indexed-KM factors. -/
theorem Compilation.carrier_factors_in_original_spans {n : Nat}
    {d : KMData (B := B) (C := C) (A := A) n} {context : State B C A}
    (cert : Compilation d context) :
    ∀ z ∈ cert.carrier,
      z.1.1 ∈ Submodule.span F2 (insert d.b0 (Set.range d.b)) ∧
      z.2.1.1 ∈ Submodule.span F2 (insert d.c0 (Set.range d.c)) ∧
      z.2.2.1 ∈ Submodule.span F2 {d.a} := by
  apply cert.carrier_factors_mem
  · exact Submodule.subset_span (Set.mem_insert _ _)
  · intro i
    exact Submodule.subset_span (Or.inr ⟨i, rfl⟩)
  · exact Submodule.subset_span (Set.mem_insert _ _)
  · intro i
    exact Submodule.subset_span (Or.inr ⟨i, rfl⟩)
  · exact Submodule.subset_span (Set.mem_singleton d.a)

/-- Compile two composable admissible indexed KM operations and concatenate
their computed native certificates. -/
def compilePair {n₁ n₂ : Nat}
    (d₁ : KMData (B := B) (C := C) (A := A) n₁)
    (d₂ : KMData (B := B) (C := C) (A := A) n₂)
    (context₁ context₂ : State B C A)
    (h₁ : d₁.ContextAdmissible context₁) (h₂ : d₂.ContextAdmissible context₂)
    (hjoin : d₁.targetEndpoint context₁ = d₂.sourceEndpoint context₂) :
    MovePath (AllModeMove (U := B) (V := C) (W := A))
      (d₁.sourceEndpoint context₁) (d₂.targetEndpoint context₂) :=
  (compile d₁ context₁ h₁).path.trans
    (reindexPath hjoin.symm rfl (compile d₂ context₂ h₂).path)

/-- Compiling two composable operations adds their actual primitive lengths
and takes the maximum of their actual altitudes. -/
theorem compilePair_observations {n₁ n₂ : Nat}
    (d₁ : KMData (B := B) (C := C) (A := A) n₁)
    (d₂ : KMData (B := B) (C := C) (A := A) n₂)
    (context₁ context₂ : State B C A)
    (h₁ : d₁.ContextAdmissible context₁) (h₂ : d₂.ContextAdmissible context₂)
    (hjoin : d₁.targetEndpoint context₁ = d₂.sourceEndpoint context₂) :
    (compilePair d₁ d₂ context₁ context₂ h₁ h₂ hjoin).length =
        (compile d₁ context₁ h₁).path.length + (compile d₂ context₂ h₂).path.length ∧
    (compilePair d₁ d₂ context₁ context₂ h₁ h₂ hjoin).altitude =
        max (compile d₁ context₁ h₁).path.altitude (compile d₂ context₂ h₂).path.altitude := by
  have hobs := reindexPath_observations hjoin.symm rfl (compile d₂ context₂ h₂).path
  constructor
  · exact (trans_length _ _).trans (congrArg _ hobs.1)
  · exact (trans_altitude _ _).trans (congrArg _ hobs.2.1)

/-- Successive compiled KM reductions retain the initial source-card altitude
bound, with one-or-two native edges for every changed index of either family. -/
theorem compilePair_bounds {n₁ n₂ : Nat}
    (d₁ : KMData (B := B) (C := C) (A := A) n₁)
    (d₂ : KMData (B := B) (C := C) (A := A) n₂)
    (context₁ context₂ : State B C A)
    (h₁ : d₁.ContextAdmissible context₁) (h₂ : d₂.ContextAdmissible context₂)
    (hjoin : d₁.targetEndpoint context₁ = d₂.sourceEndpoint context₂) :
    d₁.changedIndices.card + d₂.changedIndices.card ≤
        (compilePair d₁ d₂ context₁ context₂ h₁ h₂ hjoin).length ∧
    (compilePair d₁ d₂ context₁ context₂ h₁ h₂ hjoin).length ≤
        2 * (d₁.changedIndices.card + d₂.changedIndices.card) ∧
    (compilePair d₁ d₂ context₁ context₂ h₁ h₂ hjoin).altitude ≤
        (d₁.sourceEndpoint context₁).card := by
  have hobs := compilePair_observations d₁ d₂ context₁ context₂ h₁ h₂ hjoin
  have hlo₁ := (compile d₁ context₁ h₁).length_lower
  have hlo₂ := (compile d₂ context₂ h₂).length_lower
  have hhi₁ := (compile d₁ context₁ h₁).length_upper
  have hhi₂ := (compile d₂ context₂ h₂).length_upper
  refine ⟨?_, ?_, ?_⟩
  · rw [hobs.1]
    omega
  · rw [hobs.1]
    omega
  · rw [hobs.2]
    apply Nat.max_le.mpr
    refine ⟨(compile d₁ context₁ h₁).altitude_le, ?_⟩
    apply le_trans (compile d₂ context₂ h₂).altitude_le
    rw [← hjoin, d₁.context_targetEndpoint_card context₁ h₁,
      d₁.context_sourceEndpoint_card context₁ h₁]
    omega

/-- Every vertex of a composite compilation agrees with its initial source
outside the union of the two effective carriers. -/
theorem compilePair_outside_fixed {n₁ n₂ : Nat}
    (d₁ : KMData (B := B) (C := C) (A := A) n₁)
    (d₂ : KMData (B := B) (C := C) (A := A) n₂)
    (context₁ context₂ : State B C A)
    (h₁ : d₁.ContextAdmissible context₁) (h₂ : d₂.ContextAdmissible context₂)
    (hjoin : d₁.targetEndpoint context₁ = d₂.sourceEndpoint context₂)
    (X : State B C A) (hX : X ∈ (compilePair d₁ d₂ context₁ context₂ h₁ h₂ hjoin).vertices)
    (z : Carrier B C A)
    (hz : z ∉ (compile d₁ context₁ h₁).carrier ∪ (compile d₂ context₂ h₂).carrier) :
    z ∈ X ↔ z ∈ d₁.sourceEndpoint context₁ := by
  have hz₁ : z ∉ (compile d₁ context₁ h₁).carrier :=
    fun hm => hz (Finset.mem_union_left _ hm)
  have hz₂ : z ∉ (compile d₂ context₂ h₂).carrier :=
    fun hm => hz (Finset.mem_union_right _ hm)
  rcases mem_vertices_trans _ _ hX with hfirst | hsecond
  · exact (compile d₁ context₁ h₁).outside_fixed X hfirst z hz₁
  · have hobs := reindexPath_observations hjoin.symm rfl (compile d₂ context₂ h₂).path
    rw [hobs.2.2] at hsecond
    have hright := (compile d₂ context₂ h₂).outside_fixed X hsecond z hz₂
    have hleft := (compile d₁ context₁ h₁).outside_fixed _
      (compile d₁ context₁ h₁).path.end_mem_vertices z hz₁
    rw [hjoin] at hleft
    exact hright.trans hleft

example {n : Nat} (d : KMData (B := B) (C := C) (A := A) n) :
    suffixResidual d [] = 0 ∧ remainingSource d [] = ∅ ∧
      processedTarget d [] = d.changedTarget := by
  simp [suffixResidual, remainingSource, processedTarget, BinaryKMIndexedData.Data.changedTarget]

example {n : Nat} (d : KMData (B := B) (C := C) (A := A) n)
    (i : Fin n) (x : B) : d.sourceTerm i ∈ stepCarrier d i x := by
  simp [stepCarrier]

example {n : Nat} (d : KMData (B := B) (C := C) (A := A) n)
    (context : State B C A) (hcontext : d.ContextAdmissible context) :
    (compileSuffix d context hcontext [] ⟨List.nodup_nil, Finset.empty_subset _⟩).localCosts = [] := rfl

example : ∃ d : KMData (B := F2) (C := Fin 2 → F2) (A := F2) 1,
    d.ContextAdmissible ∅ ∧ d.changedIndices.card = 1 ∧
    Nonempty (Compilation d ∅) := by
  let d : KMData (B := F2) (C := Fin 2 → F2) (A := F2) 1 := {
    a := 1
    b0 := 1
    c0 := fun i => if i = 0 then 1 else 0
    b := fun _ => 1
    c := fun _ i => if i = 1 then 1 else 0
    a_ne_zero := by decide
    b0_ne_zero := by decide
    c0_ne_zero := by decide
    b_ne_zero := by intro; decide
    c_ne_zero := by intro; decide
    outputC_ne_zero := by intro; decide
    b0_eq_sum := by simp
    source_injective := fun _ _ _ => Subsingleton.elim _ _ }
  have hcontext : d.ContextAdmissible ∅ := by simp [BinaryKMIndexedData.Data.ContextAdmissible]
  exact ⟨d, hcontext, by decide, ⟨compile d ∅ hcontext⟩⟩

example : ∃ (d₁ d₂ : KMData (B := F2) (C := Fin 2 → F2) (A := Fin 2 → F2) 1)
    (context₁ context₂ : State F2 (Fin 2 → F2) (Fin 2 → F2)),
    d₁.ContextAdmissible context₁ ∧ d₂.ContextAdmissible context₂ ∧
    d₁.targetEndpoint context₁ = d₂.sourceEndpoint context₂ := by
  let make (a : Fin 2 → F2) (ha : a ≠ 0) :
      KMData (B := F2) (C := Fin 2 → F2) (A := Fin 2 → F2) 1 := {
    a := a
    b0 := 1
    c0 := fun i => if i = 0 then 1 else 0
    b := fun _ => 1
    c := fun _ i => if i = 1 then 1 else 0
    a_ne_zero := ha
    b0_ne_zero := by decide
    c0_ne_zero := by decide
    b_ne_zero := by intro; decide
    c_ne_zero := by intro; decide
    outputC_ne_zero := by intro; decide
    b0_eq_sum := by simp
    source_injective := fun _ _ _ => Subsingleton.elim _ _ }
  let d₁ := make (fun i => if i = 0 then 1 else 0) (by decide)
  let d₂ := make (fun i => if i = 1 then 1 else 0) (by decide)
  refine ⟨d₁, d₂, d₂.sourceState, d₁.targetState, ?_, ?_, by decide⟩
  · simp only [BinaryKMIndexedData.Data.ContextAdmissible,
      BinaryKMIndexedData.Data.sourceState, BinaryKMIndexedData.Data.sourceActive,
      BinaryKMIndexedData.Data.targetState, BinaryKMIndexedData.Data.targetActive,
      Finset.univ_unique, Finset.image_singleton,
      Finset.disjoint_insert_left, Finset.disjoint_singleton_left,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    repeat' apply And.intro
    all_goals
      intro heq
      have hbad := congrArg
        (fun z : Carrier F2 (Fin 2 → F2) (Fin 2 → F2) => z.2.2.1 0) heq
      exact (by decide : (0 : F2) ≠ 1) hbad
  · simp only [BinaryKMIndexedData.Data.ContextAdmissible,
      BinaryKMIndexedData.Data.sourceState, BinaryKMIndexedData.Data.sourceActive,
      BinaryKMIndexedData.Data.targetState, BinaryKMIndexedData.Data.targetActive,
      Finset.univ_unique, Finset.image_singleton,
      Finset.disjoint_insert_right, Finset.disjoint_singleton_right,
      Finset.mem_insert, Finset.mem_singleton]
    decide




end BilinearComplexity.BinaryKMReduction
