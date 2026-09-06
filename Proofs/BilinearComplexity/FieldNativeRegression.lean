import BilinearComplexity.FieldNativePath

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BilinearComplexity
namespace FieldNativeRegression

open FieldRankOne FieldContextual FieldNativeMoves FieldNativePath
open FieldContextual.F3Profile221

/-- The absorbed first basis factor in the profile-221 regression. -/
def u0 : Factor F3 2 := ⟨e0, by decide⟩

/-- The absorbed second basis factor in the profile-221 regression. -/
def u1 : Factor F3 2 := ⟨e1, by decide⟩

/-- Twice the first basis factor. -/
def twoU0 : Factor F3 2 := ⟨2 • e0, by decide⟩

/-- Twice the second basis factor. -/
def twoU1 : Factor F3 2 := ⟨2 • e1, by decide⟩

/-- The sum of the two basis factors. -/
def u01 : Factor F3 2 := ⟨e0 + e1, by decide⟩

/-- The unique chosen nonzero third factor. -/
def w1 : Factor F3 1 := ⟨unit, by decide⟩

/-- The intermediate atom `e0 ⊗ (e0+e1) ⊗ 1`. -/
def atomF : Atom F3 2 2 1 := atom u0 u01 w1

/-- The intermediate atom is distinct from every endpoint atom used alongside it. -/
theorem atomF_distinct : atomF ≠ atomA ∧ atomF ≠ atomB ∧ atomF ≠ atom2C ∧
    atomF ≠ atom2D ∧ atomF ≠ atomJ := by
  constructor
  · apply Atom.ne_of_val_ne
    decide
  constructor
  · apply Atom.ne_of_val_ne
    decide
  constructor
  · apply Atom.ne_of_val_ne
    decide
  constructor <;> apply Atom.ne_of_val_ne <;> decide

/-- The borrowed atom `e1 ⊗ (e0+e1) ⊗ 1` used by the all-context diamond. -/
def atomQ : Atom F3 2 2 1 := atom u1 u01 w1

/-- The borrowed atom is distinct from all five endpoint atoms. -/
theorem atomQ_distinct : atomQ ≠ atomA ∧ atomQ ≠ atomB ∧ atomQ ≠ atom2C ∧
    atomQ ≠ atom2D ∧ atomQ ≠ atomJ := by
  constructor
  · apply Atom.ne_of_val_ne
    decide
  constructor
  · apply Atom.ne_of_val_ne
    decide
  constructor
  · apply Atom.ne_of_val_ne
    decide
  constructor <;> apply Atom.ne_of_val_ne <;> decide

/-- The Split template `b ↦ d+q` for the all-context diamond. -/
theorem splitB : SplitFormula atomB atom2D atomQ := by
  apply SplitFormula.second u1 w1
  refine {
    x := twoU0
    y := u01
    sum_ne := by decide
    source_eq := ?_
    left_eq := ?_
    right_eq := rfl }
  all_goals
    apply Atom.ext
    funext i j l
    fin_cases i <;> fin_cases j <;> fin_cases l <;> decide

/-- The Flip template `(q,a) ↦ (j,c)` for the all-context diamond. -/
theorem flipQA : FlipFormula atomQ atomA atomJ atom2C := by
  apply FlipFormula.firstSecond w1
  refine {
    x₁ := u1
    x₂ := u0
    y₁ := u01
    y₂ := u0
    sum_ne := by decide
    diff_ne := by decide
    source₁_eq := rfl
    source₂_eq := ?_
    target₁_eq := ?_
    target₂_eq := ?_ }
  all_goals
    apply Atom.ext
    funext i j l
    fin_cases i <;> fin_cases j <;> fin_cases l <;> decide

/-- The native local replacement underlying the `b ↦ d+q` Split. -/
theorem splitBReplacement : NativeReplacement (singletonState atomB)
    (pairState atom2D atomQ) := by
  apply NativeReplacement.split splitB
  exact atomQ_distinct.2.2.2.1.symm

/-- The native local replacement underlying the `(q,a) ↦ (j,c)` Flip. -/
theorem flipQAReplacement : NativeReplacement (pairState atomQ atomA)
    (pairState atomJ atom2C) := by
  apply NativeReplacement.flip flipQA
  · exact atomQ_distinct.1
  · apply Atom.ne_of_val_ne
    decide

/-- The concrete Split relation with executable finite-set endpoints. -/
theorem splitBReplacementLiteral : NativeReplacement ({atomB} : State F3 2 2 1)
    {atom2D, atomQ} := by
  have hsource : ({atomB} : State F3 2 2 1) = singletonState atomB := by
    ext x
    simp [singletonState]
  have htarget : ({atom2D, atomQ} : State F3 2 2 1) = pairState atom2D atomQ := by
    ext x
    simp [pairState]
  rw [hsource, htarget]
  exact splitBReplacement

/-- The concrete Flip relation with executable finite-set endpoints. -/
theorem flipQAReplacementLiteral : NativeReplacement ({atomQ, atomA} : State F3 2 2 1)
    {atomJ, atom2C} := by
  have hsource : ({atomQ, atomA} : State F3 2 2 1) = pairState atomQ atomA := by
    ext x
    simp [pairState]
  have htarget : ({atomJ, atom2C} : State F3 2 2 1) = pairState atomJ atom2C := by
    ext x
    simp [pairState]
  rw [hsource, htarget]
  exact flipQAReplacement

/-- The actual three-atom intermediate state for the empty-context replay. -/
def middle : State F3 2 2 1 := {atom2C, atomF, atomB}

#eval middle.card

/-- The first native move splits `A` into `2C` and `F`. -/
theorem splitA : SplitFormula atomA atom2C atomF := by
  apply SplitFormula.second u0 w1
  refine {
    x := twoU1
    y := u01
    sum_ne := by decide
    source_eq := ?_
    left_eq := ?_
    right_eq := rfl }
  all_goals
    apply Atom.ext
    funext i j l
    fin_cases i <;> fin_cases j <;> fin_cases l <;> decide

/-- The second native move flips `(F,B)` to `(J,2D)`. -/
theorem flipFB : FlipFormula atomF atomB atomJ atom2D := by
  apply FlipFormula.firstSecond w1
  refine {
    x₁ := u0
    x₂ := u1
    y₁ := u01
    y₂ := u1
    sum_ne := by decide
    diff_ne := by decide
    source₁_eq := rfl
    source₂_eq := ?_
    target₁_eq := ?_
    target₂_eq := ?_ }
  all_goals
    apply Atom.ext
    funext i j l
    fin_cases i <;> fin_cases j <;> fin_cases l <;> decide

/-- The local Split replacement used by the first regression edge. -/
theorem splitReplacement : NativeReplacement (singletonState atomA)
    (pairState atom2C atomF) := by
  apply NativeReplacement.split splitA
  apply Atom.ne_of_val_ne
  decide

/-- The local Flip replacement used by the second regression edge. -/
theorem flipReplacement : NativeReplacement (pairState atomF atomB)
    (pairState atomJ atom2D) := by
  apply NativeReplacement.flip flipFB
  · apply Atom.ne_of_val_ne
    decide
  · apply Atom.ne_of_val_ne
    decide

/-- The exact first field-native edge from the two-atom source to the intermediate state. -/
noncomputable def stepA_middle : NativeStep A2 middle := by
  refine {
    source := singletonState atomA
    target := pairState atom2C atomF
    native := splitReplacement
    source_subset := ?_
    target_fresh := ?_
    result_eq := ?_ }
  · intro x hx
    simp only [singletonState, Finset.mem_singleton] at hx
    subst x
    simp [A2]
  · classical
    have hCA : atom2C ≠ atomA := Atom.ne_of_val_ne (by decide)
    have hCB : atom2C ≠ atomB := Atom.ne_of_val_ne (by decide)
    have hFA : atomF ≠ atomA := atomF_distinct.1
    have hFB : atomF ≠ atomB := atomF_distinct.2.1
    simp [Finset.disjoint_left, stateDifference, singletonState, pairState, A2,
      hCA, hCB, hFA, hFB]
  · classical
    have hAB : atomA ≠ atomB := Atom.ne_of_val_ne (by decide)
    have hCA : atom2C ≠ atomA := Atom.ne_of_val_ne (by decide)
    have hCB : atom2C ≠ atomB := Atom.ne_of_val_ne (by decide)
    have hFA : atomF ≠ atomA := atomF_distinct.1
    have hFB : atomF ≠ atomB := atomF_distinct.2.1
    ext x
    simp [middle, A2, stateUnion, stateDifference, singletonState, pairState,
      hCA, hCB, hFA, hFB]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨Or.inr rfl, hAB.symm⟩)
    · rintro (rfl | rfl | ⟨hx, hnot⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · rcases hx with rfl | rfl
        · exact False.elim (hnot rfl)
        · exact Or.inr (Or.inr rfl)

/-- The exact second field-native edge from the intermediate state to the three-atom target. -/
noncomputable def stepMiddle_B : NativeStep middle B3 := by
  refine {
    source := pairState atomF atomB
    target := pairState atomJ atom2D
    native := flipReplacement
    source_subset := ?_
    target_fresh := ?_
    result_eq := ?_ }
  · intro x hx
    simp only [pairState, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [middle]
  · classical
    have hJF : atomJ ≠ atomF := atomF_distinct.2.2.2.2.symm
    have hJB : atomJ ≠ atomB := Atom.ne_of_val_ne (by decide)
    have hDF : atom2D ≠ atomF := atomF_distinct.2.2.2.1.symm
    have hDB : atom2D ≠ atomB := Atom.ne_of_val_ne (by decide)
    have hCF : atom2C ≠ atomF := atomF_distinct.2.2.1.symm
    have hCB : atom2C ≠ atomB := Atom.ne_of_val_ne (by decide)
    have hJC : atomJ ≠ atom2C := Atom.ne_of_val_ne (by decide)
    have hDC : atom2D ≠ atom2C := Atom.ne_of_val_ne (by decide)
    simp [Finset.disjoint_left, stateDifference, pairState, middle,
      hJF, hJB, hDF, hDB, hCF, hCB, hJC, hDC]
  · classical
    have hFB : atomF ≠ atomB := atomF_distinct.2.1
    have hJF : atomJ ≠ atomF := atomF_distinct.2.2.2.2.symm
    have hJB : atomJ ≠ atomB := Atom.ne_of_val_ne (by decide)
    have hDF : atom2D ≠ atomF := atomF_distinct.2.2.2.1.symm
    have hDB : atom2D ≠ atomB := Atom.ne_of_val_ne (by decide)
    have hCF : atom2C ≠ atomF := atomF_distinct.2.2.1.symm
    have hCB : atom2C ≠ atomB := Atom.ne_of_val_ne (by decide)
    have hJC : atomJ ≠ atom2C := Atom.ne_of_val_ne (by decide)
    have hDC : atom2D ≠ atom2C := Atom.ne_of_val_ne (by decide)
    ext x
    simp [middle, B3, stateUnion, stateDifference, pairState,
      hJF, hJB, hDF, hDB, hJC, hDC]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact Or.inr (Or.inr ⟨Or.inl rfl, hCF, hCB⟩)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
    · rintro (rfl | rfl | ⟨hx, hnotF, hnotB⟩)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl rfl)
      · rcases hx with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact False.elim (hnotF rfl)
        · exact False.elim (hnotB rfl)


/-- The first regression edge is strict: its Split removes and inserts disjoint atoms. -/
noncomputable def strictStepA_middle : StrictNativeStep A2 middle := by
  refine {
    step := stepA_middle
    endpoints_disjoint := ?_
    ne := ?_ }
  · classical
    have hAC : atomA ≠ atom2C := Atom.ne_of_val_ne (by decide)
    have hAF : atomA ≠ atomF := atomF_distinct.1.symm
    simp [stepA_middle, Finset.disjoint_left, singletonState, pairState, hAC, hAF]
  · intro h
    have hx : atom2C ∈ A2 := h ▸ (by simp [middle])
    have hCA : atom2C ≠ atomA := Atom.ne_of_val_ne (by decide)
    have hCB : atom2C ≠ atomB := Atom.ne_of_val_ne (by decide)
    simpa [A2, hCA, hCB] using hx

/-- The second regression edge is strict: its Flip removes and inserts disjoint atoms. -/
noncomputable def strictStepMiddle_B : StrictNativeStep middle B3 := by
  refine {
    step := stepMiddle_B
    endpoints_disjoint := ?_
    ne := ?_ }
  · classical
    have hFJ : atomF ≠ atomJ := atomF_distinct.2.2.2.2
    have hFD : atomF ≠ atom2D := atomF_distinct.2.2.2.1
    have hBJ : atomB ≠ atomJ := Atom.ne_of_val_ne (by decide)
    have hBD : atomB ≠ atom2D := Atom.ne_of_val_ne (by decide)
    simp [stepMiddle_B, Finset.disjoint_left, pairState, hFJ, hFD, hBJ, hBD]
  · intro h
    have hx : atomF ∈ B3 := h ▸ (by simp [middle])
    have hFC : atomF ≠ atom2C := atomF_distinct.2.2.1
    have hFD : atomF ≠ atom2D := atomF_distinct.2.2.2.1
    have hFJ : atomF ≠ atomJ := atomF_distinct.2.2.2.2
    simpa [B3, hFC, hFD, hFJ] using hx

/-- The empty-context forward replay is an actual two-edge strict native path. -/
noncomputable def emptyForward : StrictNativePath A2 B3 :=
  .cons strictStepA_middle (.cons strictStepMiddle_B (.nil B3))

/-- Coefficient-correct native inversion gives the empty-context reverse replay. -/
noncomputable def emptyReverse : StrictNativePath B3 A2 :=
  .cons strictStepMiddle_B.reverse (.cons strictStepA_middle.reverse (.nil A2))


/-- The contextual source state is the outside context together with `{a,b}`. -/
def contextSource (C : State F3 2 2 1) : State F3 2 2 1 := C ∪ A2

/-- The contextual target state is the outside context together with `{c,d,j}`. -/
def contextTarget (C : State F3 2 2 1) : State F3 2 2 1 := C ∪ B3

/-- The q-absent branch first creates `q`, while retaining `a` and inserting `d`. -/
def absentMiddle (C : State F3 2 2 1) : State F3 2 2 1 :=
  {atomA, atom2D, atomQ} ∪ C

/-- The q-present branch borrows `q`, inserts `j,c`, and retains `b`. -/
def presentMiddle (C : State F3 2 2 1) : State F3 2 2 1 :=
  {atomB, atomJ, atom2C} ∪ C.erase atomQ

/-- An exact two-step execution records its unique intermediate vertex and both strict edges. -/
structure TwoStepExecution (D E : State F3 2 2 1) where
  /-- The unique recorded intermediate vertex. -/
  middle : State F3 2 2 1
  /-- The first strict native edge. -/
  first : StrictNativeStep D middle
  /-- The second strict native edge. -/
  second : StrictNativeStep middle E

/-- Forget an exact two-step execution to the ordinary strict native path type. -/
def TwoStepExecution.path {D E : State F3 2 2 1}
    (execution : TwoStepExecution D E) : StrictNativePath D E :=
  .cons execution.first (.cons execution.second (.nil E))

/-- Reverse an exact two-step execution using coefficient-correct native inversion. -/
def TwoStepExecution.reverse {D E : State F3 2 2 1}
    (execution : TwoStepExecution D E) : TwoStepExecution E D where
  middle := execution.middle
  first := execution.second.reverse
  second := execution.first.reverse

/-- The context disjointness condition implies that none of the five endpoint atoms occurs
in the outside context. -/
theorem endpointAtoms_not_mem {C : State F3 2 2 1}
    (hC : Disjoint C (stateUnion A2 B3)) :
    atomA ∉ C ∧ atomB ∉ C ∧ atom2C ∉ C ∧ atom2D ∉ C ∧ atomJ ∉ C := by
  rw [Finset.disjoint_left] at hC
  have hA : atomA ∈ stateUnion A2 B3 := by simp [stateUnion, A2]
  have hB : atomB ∈ stateUnion A2 B3 := by simp [stateUnion, A2]
  have hC2 : atom2C ∈ stateUnion A2 B3 := by simp [stateUnion, B3]
  have hD : atom2D ∈ stateUnion A2 B3 := by simp [stateUnion, B3]
  have hJ : atomJ ∈ stateUnion A2 B3 := by simp [stateUnion, B3]
  exact ⟨fun hx => hC hx hA, fun hx => hC hx hB, fun hx => hC hx hC2,
    fun hx => hC hx hD, fun hx => hC hx hJ⟩

#eval (absentMiddle ∅).card
#eval (presentMiddle {atomQ}).card

/-- In a q-absent context, the first edge splits `b` into `d+q`. -/
def absentFirst {C : State F3 2 2 1}
    (hC : Disjoint C (stateUnion A2 B3)) (hq : atomQ ∉ C) :
    StrictNativeStep (contextSource C) (absentMiddle C) := by
  let hEnds := endpointAtoms_not_mem hC
  have hCA := hEnds.1
  have hCB := hEnds.2.1
  have hCD := hEnds.2.2.2.1
  have hBA : atomB ≠ atomA := Atom.ne_of_val_ne (by decide)
  have hDA : atom2D ≠ atomA := Atom.ne_of_val_ne (by decide)
  have hDB : atom2D ≠ atomB := Atom.ne_of_val_ne (by decide)
  have hQA : atomQ ≠ atomA := atomQ_distinct.1
  have hQB : atomQ ≠ atomB := atomQ_distinct.2.1
  have hDQ : atom2D ≠ atomQ := atomQ_distinct.2.2.2.1.symm
  refine {
    step := {
      source := {atomB}
      target := {atom2D, atomQ}
      native := splitBReplacementLiteral
      source_subset := ?_
      target_fresh := ?_
      result_eq := ?_ }
    endpoints_disjoint := ?_
    ne := ?_ }
  · intro x hx
    simp only [singletonState, Finset.mem_singleton] at hx
    subst x
    simp [contextSource, stateUnion, A2]
  · classical
    simp [Finset.disjoint_left, contextSource, stateDifference, stateUnion, A2,
      singletonState, pairState, hCD, hDA, hDB, hq, hQA, hQB]
  · classical
    ext x
    simp [absentMiddle, contextSource, stateDifference, stateUnion, A2, *] <;> aesop
  · classical
    rw [Finset.disjoint_left]
    intro x hxSource hxTarget
    simp only [singletonState, Finset.mem_singleton] at hxSource
    subst x
    simp [pairState, hDB.symm, hQB.symm] at hxTarget
  · intro heq
    have hx : atomB ∈ absentMiddle C := heq ▸ (by simp [contextSource, stateUnion, A2])
    have hBD : atomB ≠ atom2D := hDB.symm
    have hBQ : atomB ≠ atomQ := hQB.symm
    simpa [absentMiddle, hCB, hBA, hBD, hBQ] using hx


/-- In a q-absent context, the second edge flips `(q,a)` into `(j,c)`. -/
def absentSecond {C : State F3 2 2 1}
    (hC : Disjoint C (stateUnion A2 B3)) (hq : atomQ ∉ C) :
    StrictNativeStep (absentMiddle C) (contextTarget C) := by
  let hEnds := endpointAtoms_not_mem hC
  have hA_not := hEnds.1
  have hCC := hEnds.2.2.1
  have hCD := hEnds.2.2.2.1
  have hCJ := hEnds.2.2.2.2
  have hJA : atomJ ≠ atomA := Atom.ne_of_val_ne (by decide)
  have hJD : atomJ ≠ atom2D := Atom.ne_of_val_ne (by decide)
  have hCA : atom2C ≠ atomA := Atom.ne_of_val_ne (by decide)
  have hCD' : atom2C ≠ atom2D := Atom.ne_of_val_ne (by decide)
  have hDA : atom2D ≠ atomA := Atom.ne_of_val_ne (by decide)
  have hDQ : atom2D ≠ atomQ := atomQ_distinct.2.2.2.1.symm
  have hQA : atomQ ≠ atomA := atomQ_distinct.1
  have hQJ : atomQ ≠ atomJ := atomQ_distinct.2.2.2.2
  have hQC : atomQ ≠ atom2C := atomQ_distinct.2.2.1
  refine {
    step := {
      source := {atomQ, atomA}
      target := {atomJ, atom2C}
      native := flipQAReplacementLiteral
      source_subset := ?_
      target_fresh := ?_
      result_eq := ?_ }
    endpoints_disjoint := ?_
    ne := ?_ }
  · intro x hx
    simp only [pairState, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [absentMiddle]
  · classical
    simp [Finset.disjoint_left, absentMiddle, stateDifference, pairState,
      hCJ, hCC, hJA, hJD, hCA, hCD']
  · classical
    ext x
    simp [contextTarget, absentMiddle, stateDifference, stateUnion, B3, *] <;> aesop
  · classical
    rw [Finset.disjoint_left]
    intro x hxSource hxTarget
    simp only [pairState, Finset.mem_insert, Finset.mem_singleton] at hxSource hxTarget
    rcases hxSource with rfl | rfl
    · rcases hxTarget with h | h
      · exact hQJ h
      · exact hQC h
    · rcases hxTarget with h | h
      · exact hJA h.symm
      · exact hCA h.symm
  · intro heq
    have hx : atomQ ∈ contextTarget C := heq ▸ (by simp [absentMiddle])
    have hQD : atomQ ≠ atom2D := atomQ_distinct.2.2.2.1
    simpa [contextTarget, stateUnion, B3, hq, hQC, hQD, hQJ] using hx

/-- Every q-absent endpoint-disjoint context has the direct Split-then-Flip execution. -/
def absentExecution {C : State F3 2 2 1}
    (hC : Disjoint C (stateUnion A2 B3)) (hq : atomQ ∉ C) :
    TwoStepExecution (contextSource C) (contextTarget C) where
  middle := absentMiddle C
  first := absentFirst hC hq
  second := absentSecond hC hq


/-- In a q-present context, the first edge borrows `q` and flips `(q,a)` into `(j,c)`. -/
def presentFirst {C : State F3 2 2 1}
    (hC : Disjoint C (stateUnion A2 B3)) (hq : atomQ ∈ C) :
    StrictNativeStep (contextSource C) (presentMiddle C) := by
  let hEnds := endpointAtoms_not_mem hC
  have hCA := hEnds.1
  have hCB := hEnds.2.1
  have hCC := hEnds.2.2.1
  have hCJ := hEnds.2.2.2.2
  have hAB : atomA ≠ atomB := Atom.ne_of_val_ne (by decide)
  have hJB : atomJ ≠ atomB := Atom.ne_of_val_ne (by decide)
  have hCB' : atom2C ≠ atomB := Atom.ne_of_val_ne (by decide)
  have hQJ := atomQ_distinct.2.2.2.2
  have hQC := atomQ_distinct.2.2.1
  have hQA := atomQ_distinct.1
  have hAJ : atomA ≠ atomJ := Atom.ne_of_val_ne (by decide)
  have hAC : atomA ≠ atom2C := Atom.ne_of_val_ne (by decide)
  refine {
    step := {
      source := {atomQ, atomA}
      target := {atomJ, atom2C}
      native := flipQAReplacementLiteral
      source_subset := ?_
      target_fresh := ?_
      result_eq := ?_ }
    endpoints_disjoint := ?_
    ne := ?_ }
  · intro x hx
    simp only [pairState, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp [contextSource, stateUnion, hq]
    · simp [contextSource, stateUnion, A2]
  · classical
    simp [Finset.disjoint_left, contextSource, stateDifference, stateUnion, A2,
      pairState, hCJ, hCC, hJB, hCB'] <;> aesop
  · classical
    ext x
    simp [presentMiddle, contextSource, stateDifference, stateUnion, A2, pairState,
      hCA, hAB] <;> aesop (config := { maxRuleApplications := 1000 })
  · classical
    rw [Finset.disjoint_left]
    intro x hxSource hxTarget
    simp only [pairState, Finset.mem_insert, Finset.mem_singleton] at hxSource hxTarget
    rcases hxSource with rfl | rfl
    · rcases hxTarget with h | h
      · exact hQJ h
      · exact hQC h
    · rcases hxTarget with h | h
      · exact hAJ h
      · exact hAC h
  · intro heq
    have hx : atomA ∈ presentMiddle C := heq ▸ (by simp [contextSource, stateUnion, A2])
    simpa [presentMiddle, hCA, hAB, hAJ, hAC] using hx


/-- In a q-present context, the second edge restores `q` by splitting `b` into `d+q`. -/
def presentSecond {C : State F3 2 2 1}
    (hC : Disjoint C (stateUnion A2 B3)) (hq : atomQ ∈ C) :
    StrictNativeStep (presentMiddle C) (contextTarget C) := by
  let hEnds := endpointAtoms_not_mem hC
  have hCB := hEnds.2.1
  have hCD := hEnds.2.2.2.1
  have hBD : atomB ≠ atom2D := Atom.ne_of_val_ne (by decide)
  have hBQ : atomB ≠ atomQ := atomQ_distinct.2.1.symm
  have hDJ : atom2D ≠ atomJ := Atom.ne_of_val_ne (by decide)
  have hDC : atom2D ≠ atom2C := Atom.ne_of_val_ne (by decide)
  have hCB' : atom2C ≠ atomB := Atom.ne_of_val_ne (by decide)
  have hJB : atomJ ≠ atomB := Atom.ne_of_val_ne (by decide)
  have hQJ := atomQ_distinct.2.2.2.2
  have hQC := atomQ_distinct.2.2.1
  refine {
    step := {
      source := {atomB}
      target := {atom2D, atomQ}
      native := splitBReplacementLiteral
      source_subset := ?_
      target_fresh := ?_
      result_eq := ?_ }
    endpoints_disjoint := ?_
    ne := ?_ }
  · intro x hx
    simp only [singletonState, Finset.mem_singleton] at hx
    subst x
    simp [presentMiddle]
  · classical
    simp [Finset.disjoint_left, presentMiddle, stateDifference, singletonState,
      pairState, hCD, hDJ, hDC, hQJ, hQC]
  · classical
    ext x
    simp [contextTarget, presentMiddle, stateDifference, stateUnion, B3, *]
    constructor
    · rintro (rfl | rfl | rfl | hxC)
      · exact Or.inl ⟨Or.inr (Or.inr (Or.inl rfl)), hCB'⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl ⟨Or.inr (Or.inl rfl), hJB⟩
      · by_cases hxQ : x = atomQ
        · exact Or.inr (Or.inr hxQ)
        · exact Or.inl ⟨Or.inr (Or.inr (Or.inr ⟨hxQ, hxC⟩)),
            fun hxB => hCB (hxB ▸ hxC)⟩
    · rintro (⟨hx, hnotB⟩ | rfl | rfl)
      · rcases hx with rfl | rfl | rfl | ⟨hnotQ, hxC⟩
        · exact False.elim (hnotB rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inr hxC))
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr hq))
  · classical
    rw [Finset.disjoint_left]
    intro x hxSource hxTarget
    simp only [singletonState, Finset.mem_singleton] at hxSource
    subst x
    simp [pairState, hBD, hBQ] at hxTarget
  · intro heq
    have hx : atomB ∈ contextTarget C := heq ▸ (by simp [presentMiddle])
    have hBC : atomB ≠ atom2C := Atom.ne_of_val_ne (by decide)
    have hBJ : atomB ≠ atomJ := Atom.ne_of_val_ne (by decide)
    simpa [contextTarget, stateUnion, B3, hCB, hBD, hBC, hBJ] using hx

/-- Every q-present endpoint-disjoint context has the direct Flip-then-Split execution. -/
def presentExecution {C : State F3 2 2 1}
    (hC : Disjoint C (stateUnion A2 B3)) (hq : atomQ ∈ C) :
    TwoStepExecution (contextSource C) (contextTarget C) where
  middle := presentMiddle C
  first := presentFirst hC hq
  second := presentSecond hC hq

/-- Every endpoint-disjoint context has an explicit two-step native execution, selected only
by whether the borrowed atom `q` is already present. -/
def allContextForward (C : State F3 2 2 1)
    (hC : Disjoint C (stateUnion A2 B3)) :
    TwoStepExecution (contextSource C) (contextTarget C) := by
  by_cases hq : atomQ ∈ C
  · exact presentExecution hC hq
  · exact absentExecution hC hq

/-- Every endpoint-disjoint context also has the reverse two-step execution, obtained through
the proved coefficient-correct inversion of both native primitives. -/
def allContextReverse (C : State F3 2 2 1)
    (hC : Disjoint C (stateUnion A2 B3)) :
    TwoStepExecution (contextTarget C) (contextSource C) :=
  (allContextForward C hC).reverse

/-- Executable vertex-cardinality and local-edge-arity data projected directly from a certified
execution. The first component inspects the actual start, middle, and end vertices; the second
inspects the stored local source and target of each native edge. -/
def TwoStepExecution.actualProjection {D E : State F3 2 2 1}
    (execution : TwoStepExecution D E) : List Nat × List (Nat × Nat) :=
  ([D.card, execution.middle.card, E.card],
    [(execution.first.step.source.card, execution.first.step.target.card),
      (execution.second.step.source.card, execution.second.step.target.card)])

#eval (allContextForward (∅ : State F3 2 2 1) (by
  classical
  simp [stateUnion])).actualProjection

#eval (allContextForward ({atomQ} : State F3 2 2 1) (by
  classical
  simp [stateUnion, A2, B3, atomQ_distinct])).actualProjection
#eval (allContextReverse (∅ : State F3 2 2 1) (by
  classical
  simp [stateUnion])).actualProjection

#eval (allContextReverse ({atomQ} : State F3 2 2 1) (by
  classical
  simp [stateUnion, A2, B3, atomQ_distinct])).actualProjection

/-- The contextual source has exactly two atoms more than its disjoint context. -/
theorem contextSource_card {C : State F3 2 2 1}
    (hC : Disjoint C (stateUnion A2 B3)) :
    (contextSource C).card = C.card + 2 := by
  let hEnds := endpointAtoms_not_mem hC
  have hCA := hEnds.1
  have hCB := hEnds.2.1
  have hAB : atomA ≠ atomB := Atom.ne_of_val_ne (by decide)
  classical
  simp [contextSource, stateUnion, A2, hCA, hCB, hAB, Nat.add_comm]
  omega

/-- The contextual target has exactly three atoms more than its disjoint context. -/
theorem contextTarget_card {C : State F3 2 2 1}
    (hC : Disjoint C (stateUnion A2 B3)) :
    (contextTarget C).card = C.card + 3 := by
  let hEnds := endpointAtoms_not_mem hC
  have hCC := hEnds.2.2.1
  have hCD := hEnds.2.2.2.1
  have hCJ := hEnds.2.2.2.2
  have hCD' : atom2C ≠ atom2D := Atom.ne_of_val_ne (by decide)
  have hCJ' : atom2C ≠ atomJ := Atom.ne_of_val_ne (by decide)
  have hDJ : atom2D ≠ atomJ := Atom.ne_of_val_ne (by decide)
  classical
  simp [contextTarget, stateUnion, B3, hCC, hCD, hCJ, hCD', hCJ', hDJ,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  omega

/-- The q-absent intermediate has exactly three atoms more than its context. -/
theorem absentMiddle_card {C : State F3 2 2 1}
    (hC : Disjoint C (stateUnion A2 B3)) (hq : atomQ ∉ C) :
    (absentMiddle C).card = C.card + 3 := by
  let hEnds := endpointAtoms_not_mem hC
  have hCA := hEnds.1
  have hCD := hEnds.2.2.2.1
  have hAD : atomA ≠ atom2D := Atom.ne_of_val_ne (by decide)
  have hAQ := atomQ_distinct.1.symm
  have hDQ := atomQ_distinct.2.2.2.1.symm
  classical
  simp [absentMiddle, hCA, hCD, hq, hAD, hAQ, hDQ,
    Nat.add_comm]
  omega

/-- The q-present intermediate has exactly two atoms more than its context. -/
theorem presentMiddle_card {C : State F3 2 2 1}
    (hC : Disjoint C (stateUnion A2 B3)) (hq : atomQ ∈ C) :
    (presentMiddle C).card = C.card + 2 := by
  let hEnds := endpointAtoms_not_mem hC
  have hCB := hEnds.2.1
  have hCC := hEnds.2.2.1
  have hCJ := hEnds.2.2.2.2
  have hBJ : atomB ≠ atomJ := Atom.ne_of_val_ne (by decide)
  have hBC : atomB ≠ atom2C := Atom.ne_of_val_ne (by decide)
  have hJC : atomJ ≠ atom2C := Atom.ne_of_val_ne (by decide)
  have hCardPos : 0 < C.card := Finset.card_pos.mpr ⟨atomQ, hq⟩
  classical
  rw [presentMiddle]
  simp [hCB, hCC, hCJ, hBJ, hBC, hJC, hq, Nat.add_comm]
  omega

/-- Every all-context execution has altitude at most `C.card + 3`; the three conjuncts
bound its source, recorded intermediate, and target respectively. -/
theorem allContextForward_altitude (C : State F3 2 2 1)
    (hC : Disjoint C (stateUnion A2 B3)) :
    (contextSource C).card ≤ C.card + 3 ∧
      (allContextForward C hC).middle.card ≤ C.card + 3 ∧
      (contextTarget C).card ≤ C.card + 3 := by
  have hSource := contextSource_card hC
  have hTarget := contextTarget_card hC
  classical
  by_cases hq : atomQ ∈ C
  · rw [show (allContextForward C hC).middle = presentMiddle C by
      simp [allContextForward, hq, presentExecution]]
    rw [presentMiddle_card hC hq, hSource, hTarget]
    omega
  · rw [show (allContextForward C hC).middle = absentMiddle C by
      simp [allContextForward, hq, absentExecution]]
    rw [absentMiddle_card hC hq, hSource, hTarget]
    omega

/-- Reversal preserves the same `C.card + 3` altitude bound. -/
theorem allContextReverse_altitude (C : State F3 2 2 1)
    (hC : Disjoint C (stateUnion A2 B3)) :
    (contextTarget C).card ≤ C.card + 3 ∧
      (allContextReverse C hC).middle.card ≤ C.card + 3 ∧
      (contextSource C).card ≤ C.card + 3 := by
  let hForward := allContextForward_altitude C hC
  simpa only [allContextReverse, TwoStepExecution.reverse] using
    And.intro hForward.2.2 (And.intro hForward.2.1 hForward.1)


/-- Effective labels for the four concrete F3 primitive directions used by the proof objects. -/
inductive RuntimePrimitive where
  | splitBQ
  | flipQA
  | inverseFlipQA
  | reduceBQ
  deriving DecidableEq, Repr

/-- A computable summary of the actual native two-step branch. It is intentionally separate from
the generic proof-side reversal, whose implementation uses classical finite-set reasoning. -/
def runtimePlan (C : State F3 2 2 1) (reverse : Bool) : List RuntimePrimitive :=
  if atomQ ∈ C then
    if reverse then [.reduceBQ, .inverseFlipQA] else [.flipQA, .splitBQ]
  else
    if reverse then [.inverseFlipQA, .reduceBQ] else [.splitBQ, .flipQA]

example : runtimePlan ∅ false = [.splitBQ, .flipQA] := by decide
example : runtimePlan {atomQ} false = [.flipQA, .splitBQ] := by decide
example : runtimePlan ∅ true = [.inverseFlipQA, .reduceBQ] := by decide
example : runtimePlan {atomQ} true = [.reduceBQ, .inverseFlipQA] := by decide

/-- Every effective branch summary records exactly two primitive directions. -/
theorem runtimePlan_length (C : State F3 2 2 1) (reverse : Bool) :
    (runtimePlan C reverse).length = 2 := by
  classical
  by_cases hq : atomQ ∈ C <;> cases reverse <;> simp [runtimePlan, hq]

/-- A computable cardinality trace through the same concrete semantic F3 states selected by
`runtimePlan`; the Boolean chooses endpoint order for forward or reverse inspection. -/
def runtimeCardTrace (C : State F3 2 2 1) (reverse : Bool) : List Nat :=
  let source := C ∪ A2
  let target := C ∪ B3
  let middle := if atomQ ∈ C then presentMiddle C else absentMiddle C
  if reverse then [target.card, middle.card, source.card]
  else [source.card, middle.card, target.card]

example : runtimeCardTrace ∅ false = [2, 3, 3] := by decide
example : runtimeCardTrace {atomQ} false = [3, 3, 4] := by decide
example : runtimeCardTrace ∅ true = [3, 3, 2] := by decide
example : runtimeCardTrace {atomQ} true = [4, 3, 3] := by decide

#eval runtimePlan ∅ false
#eval runtimePlan {atomQ} false
#eval runtimePlan ∅ true
#eval runtimePlan {atomQ} true
#eval runtimeCardTrace ∅ false
#eval runtimeCardTrace {atomQ} false
#eval runtimeCardTrace ∅ true
#eval runtimeCardTrace {atomQ} true

#check @allContextForward
#check @allContextReverse
#print axioms allContextForward
#print axioms allContextReverse
#print axioms allContextForward_altitude
#print axioms runtimePlan_length

end FieldNativeRegression
end BilinearComplexity
