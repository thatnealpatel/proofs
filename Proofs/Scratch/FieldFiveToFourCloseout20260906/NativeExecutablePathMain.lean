import BilinearComplexity.FieldNativePairBridge

set_option autoImplicit false

namespace BilinearComplexity
namespace FieldNativeExecutablePath

open FieldRankOne FieldContextual FieldNativeMoves FieldNativePath

variable {k : Type*} {a b c : ℕ} [Field k]

namespace ComputedState

/-- The empty semantic state, constructed without classical equality. -/
def empty : State k a b c := ∅

/-- A semantic singleton constructed with the scalar-induced atom equality decision. -/
def singleton [DecidableEq k] (x : Atom k a b c) : State k a b c := {x}

/-- A semantic pair constructed with the scalar-induced atom equality decision. -/
def pair [DecidableEq k] (x y : Atom k a b c) : State k a b c := {x, y}

/-- Computable union of semantic states over a scalar type with decidable equality. -/
def union [DecidableEq k] (S T : State k a b c) : State k a b c := S ∪ T

/-- Computable difference of semantic states over a scalar type with decidable equality. -/
def difference [DecidableEq k] (S T : State k a b c) : State k a b c := S \ T

/-- The computable empty state is the ordinary empty finite set. -/
example : (empty : State k a b c) = ∅ := rfl

/-- The computable singleton agrees with the proof-side singleton specification. -/
theorem singleton_eq_spec [DecidableEq k] (x : Atom k a b c) :
    singleton x = singletonState x := by
  classical
  ext z
  simp only [singleton, singletonState, Finset.mem_singleton]

/-- The computable pair agrees with the proof-side pair specification. -/
theorem pair_eq_spec [DecidableEq k] (x y : Atom k a b c) :
    pair x y = pairState x y := by
  classical
  ext z
  simp only [pair, pairState, Finset.mem_insert, Finset.mem_singleton]

/-- Computable union agrees with the proof-side union specification. -/
theorem union_eq_spec [DecidableEq k] (S T : State k a b c) :
    union S T = stateUnion S T := by
  classical
  ext z
  simp only [union, stateUnion, Finset.mem_union]

/-- Computable difference agrees with the proof-side difference specification. -/
theorem difference_eq_spec [DecidableEq k] (S T : State k a b c) :
    difference S T = stateDifference S T := by
  classical
  ext z
  simp only [difference, stateDifference, Finset.mem_sdiff]

end ComputedState

/-- Computably reverse a strict native step by reversing its ordinary `NativeStep` data.
Only proof fields establish disjointness and inequality; the runtime local endpoints come
straight from `NativeStep.reverse`. -/
def reverseStep {D E : State k a b c} (h : StrictNativeStep D E) :
    StrictNativeStep E D :=
  { step := h.step.reverse
    endpoints_disjoint := by
      rw [NativeStep.reverse_source h.step, NativeStep.reverse_target h.step]
      exact h.endpoints_disjoint.symm
    ne := h.ne.symm }

/-- Computable step reversal agrees with the existing proof-side reversal. -/
theorem reverseStep_eq_spec {D E : State k a b c} (h : StrictNativeStep D E) :
    reverseStep h = h.reverse := by
  rfl

/-- Computably concatenate strict native paths with an exactly matching middle state. -/
def append {D E F : State k a b c} : StrictNativePath D E →
    StrictNativePath E F → StrictNativePath D F
  | .nil _, second => second
  | .cons first tail, second => .cons first (append tail second)

/-- Computable concatenation agrees with the existing proof-side path operation. -/
theorem append_eq_spec {D E F : State k a b c} (first : StrictNativePath D E)
    (second : StrictNativePath E F) :
    append first second = FieldNativePairBridge.Path.append first second := by
  induction first with
  | nil _ => rfl
  | cons step tail ih =>
      simp only [append, FieldNativePairBridge.Path.append, ih]

/-- Computably append one strict native edge to a path. -/
def snoc {D E F : State k a b c} (path : StrictNativePath D E)
    (last : StrictNativeStep E F) : StrictNativePath D F :=
  append path (.cons last (.nil F))

/-- Computable one-edge append agrees with the existing proof-side operation. -/
theorem snoc_eq_spec {D E F : State k a b c} (path : StrictNativePath D E)
    (last : StrictNativeStep E F) :
    snoc path last = FieldNativePairBridge.Path.snoc path last := by
  simp only [snoc, FieldNativePairBridge.Path.snoc, append_eq_spec]

/-- Computably reverse a strict path, using `reverseStep` for each actual edge. -/
def reverse {D E : State k a b c} : StrictNativePath D E → StrictNativePath E D
  | .nil D => .nil D
  | .cons first tail => snoc (reverse tail) (reverseStep first)

/-- Computable reversal agrees with the existing proof-side path reversal. -/
theorem reverse_eq_spec {D E : State k a b c} (path : StrictNativePath D E) :
    reverse path = FieldNativePairBridge.Path.reverse path := by
  induction path with
  | nil D => rfl
  | cons first tail ih =>
      simp only [reverse, FieldNativePairBridge.Path.reverse, ih, snoc_eq_spec,
        reverseStep_eq_spec]

/-- The actual full-state vertex trace. The initial state is an explicit runtime argument;
callers seeking executable traces must instantiate every indexed state by computed state data,
not by a noncomputable proof-side specification. -/
def stateTrace (D : State k a b c) {E : State k a b c} :
    StrictNativePath D E → List (State k a b c)
  | .nil _ => [D]
  | @StrictNativePath.cons _ _ _ _ _ _ M F _first tail =>
      D :: stateTrace M tail

/-- The actual consecutive full-state endpoints of every edge. As for `stateTrace`, callers
must supply paths indexed by computed states when evaluating this function. -/
def edgeTrace (D : State k a b c) {E : State k a b c} :
    StrictNativePath D E → List (State k a b c × State k a b c)
  | .nil _ => []
  | @StrictNativePath.cons _ _ _ _ _ _ M F _first tail =>
      (D, M) :: edgeTrace M tail

/-- The computable local source and target state stored in every native edge. -/
def localEndpointTrace {D E : State k a b c} :
    StrictNativePath D E → List (State k a b c × State k a b c)
  | .nil _ => []
  | .cons first tail =>
      (first.step.source, first.step.target) :: localEndpointTrace tail

/-- A stationary path traces its one actual vertex. -/
example (D : State k a b c) : stateTrace D (.nil D) = [D] := rfl

/-- A stationary path has no full-state edges. -/
example (D : State k a b c) : edgeTrace D (.nil D) = [] := rfl

/-- A stationary path has no local endpoint records. -/
example (D : State k a b c) : localEndpointTrace (.nil D) = [] := rfl

/-- The vertex trace contains one more state than the primitive path length. -/
theorem stateTrace_length {D E : State k a b c} (path : StrictNativePath D E) :
    (stateTrace D path).length = FieldNativePairBridge.Path.length path + 1 := by
  induction path with
  | nil D => rfl
  | cons first tail ih =>
      simp only [stateTrace, List.length_cons, FieldNativePairBridge.Path.length, ih]

/-- The edge trace has exactly the primitive path length. -/
theorem edgeTrace_length {D E : State k a b c} (path : StrictNativePath D E) :
    (edgeTrace D path).length = FieldNativePairBridge.Path.length path := by
  induction path with
  | nil D => rfl
  | cons first tail ih =>
      simp only [edgeTrace, List.length_cons, FieldNativePairBridge.Path.length, ih]

/-- The local endpoint trace has exactly the primitive path length. -/
theorem localEndpointTrace_length {D E : State k a b c} (path : StrictNativePath D E) :
    (localEndpointTrace path).length = FieldNativePairBridge.Path.length path := by
  induction path with
  | nil D => rfl
  | cons first tail ih =>
      simp only [localEndpointTrace, List.length_cons, FieldNativePairBridge.Path.length, ih]

/-- Computable concatenation inherits the existing primitive-length formula. -/
theorem length_append {D E F : State k a b c} (first : StrictNativePath D E)
    (second : StrictNativePath E F) :
    FieldNativePairBridge.Path.length (append first second) =
      FieldNativePairBridge.Path.length first + FieldNativePairBridge.Path.length second := by
  rw [append_eq_spec]
  exact FieldNativePairBridge.Path.length_append first second

/-- Computable one-edge append inherits the existing primitive-length formula. -/
theorem length_snoc {D E F : State k a b c} (path : StrictNativePath D E)
    (last : StrictNativeStep E F) :
    FieldNativePairBridge.Path.length (snoc path last) =
      FieldNativePairBridge.Path.length path + 1 := by
  rw [snoc_eq_spec]
  exact FieldNativePairBridge.Path.length_snoc path last

/-- Computable reversal inherits preservation of primitive length. -/
theorem length_reverse {D E : State k a b c} (path : StrictNativePath D E) :
    FieldNativePairBridge.Path.length (reverse path) =
      FieldNativePairBridge.Path.length path := by
  rw [reverse_eq_spec]
  exact FieldNativePairBridge.Path.length_reverse path

/-- Computable concatenation inherits every proof-side vertex-height bound. -/
theorem heightBound_append {H : ℕ} {D E F : State k a b c}
    {first : StrictNativePath D E} {second : StrictNativePath E F}
    (hfirst : FieldNativePairBridge.Path.HeightBound H first)
    (hsecond : FieldNativePairBridge.Path.HeightBound H second) :
    FieldNativePairBridge.Path.HeightBound H (append first second) := by
  rw [append_eq_spec]
  exact hfirst.append hsecond

/-- Computable one-edge append inherits a height bound when its endpoint does. -/
theorem heightBound_snoc {H : ℕ} {D E F : State k a b c}
    {path : StrictNativePath D E} (hpath : FieldNativePairBridge.Path.HeightBound H path)
    (last : StrictNativeStep E F) (hF : F.card ≤ H) :
    FieldNativePairBridge.Path.HeightBound H (snoc path last) := by
  rw [snoc_eq_spec]
  exact hpath.snoc last hF

/-- Computable reversal inherits exactly the same vertex-height bound. -/
theorem heightBound_reverse {H : ℕ} {D E : State k a b c}
    {path : StrictNativePath D E} (hpath : FieldNativePairBridge.Path.HeightBound H path) :
    FieldNativePairBridge.Path.HeightBound H (reverse path) := by
  rw [reverse_eq_spec]
  exact hpath.reverse

/-- A thin executable packet stores computed endpoint values together with the same semantic
indexed strict path; it introduces no alternative path or graph representation. -/
structure Packet (k : Type*) [Field k] (a b c : ℕ) where
  /-- Actual computed initial state. -/
  start : State k a b c
  /-- Actual computed terminal state. -/
  finish : State k a b c
  /-- The same repository strict native path indexed by those stored states. -/
  path : StrictNativePath start finish

namespace Packet

/-- Return every actual full-state vertex of an executable packet. -/
def stateTrace (packet : Packet k a b c) : List (State k a b c) :=
  FieldNativeExecutablePath.stateTrace packet.start packet.path

/-- Return every actual full-state edge of an executable packet. -/
def edgeTrace (packet : Packet k a b c) :
    List (State k a b c × State k a b c) :=
  FieldNativeExecutablePath.edgeTrace packet.start packet.path

/-- Return local source and target states carried by every edge of an executable packet. -/
def localEndpointTrace (packet : Packet k a b c) :
    List (State k a b c × State k a b c) :=
  FieldNativeExecutablePath.localEndpointTrace packet.path

/-- A packet's vertex trace obeys the primitive-length formula. -/
theorem stateTrace_length (packet : Packet k a b c) :
    packet.stateTrace.length = FieldNativePairBridge.Path.length packet.path + 1 :=
  FieldNativeExecutablePath.stateTrace_length packet.path

/-- A packet's edge trace obeys the primitive-length formula. -/
theorem edgeTrace_length (packet : Packet k a b c) :
    packet.edgeTrace.length = FieldNativePairBridge.Path.length packet.path :=
  FieldNativeExecutablePath.edgeTrace_length packet.path

end Packet

namespace Execution

/-- Scalar field for the concrete executable split path. -/
abbrev F3 := ZMod 3

/-- First independent varying factor. -/
def e0 : Factor F3 2 := ⟨![1, 0], by decide⟩

/-- Second independent varying factor. -/
def e1 : Factor F3 2 := ⟨![0, 1], by decide⟩

/-- Common nonzero one-dimensional factor. -/
def unit : Factor F3 1 := ⟨![1], by decide⟩

/-- Certified sum of the two varying factors. -/
def e01 : Factor F3 2 := Factor.add e0 e1 (by decide)

/-- Source atom of the executable split. -/
def sourceAtom : Atom F3 2 1 1 := FieldNativeMoves.atom e01 unit unit

/-- First target atom of the executable split. -/
def leftAtom : Atom F3 2 1 1 := FieldNativeMoves.atom e0 unit unit

/-- Second target atom of the executable split. -/
def rightAtom : Atom F3 2 1 1 := FieldNativeMoves.atom e1 unit unit

/-- Exact first-factor split formula used by the executable edge. -/
theorem splitFormula : SplitFormula sourceAtom leftAtom rightAtom :=
  .first unit unit {
    x := e0
    y := e1
    sum_ne := by decide
    source_eq := rfl
    left_eq := rfl
    right_eq := rfl }

/-- Computed singleton source state. -/
def sourceState : State F3 2 1 1 := ComputedState.singleton sourceAtom

/-- Computed two-atom target state. -/
def targetState : State F3 2 1 1 := ComputedState.pair leftAtom rightAtom

/-- The computed local states support the exact split relation. -/
theorem nativeReplacement : NativeReplacement sourceState targetState := by
  simpa only [sourceState, targetState, ComputedState.singleton_eq_spec,
    ComputedState.pair_eq_spec] using
    NativeReplacement.split splitFormula (Atom.ne_of_val_ne (by decide))


/-- Actual native step whose runtime local and whole endpoints are computed F3 states. -/
def nativeStep : NativeStep sourceState targetState where
  source := sourceState
  target := targetState
  native := nativeReplacement
  source_subset := fun _ hx => hx
  target_fresh := by
    classical
    rw [Finset.disjoint_left]
    intro x hxTarget hxDifference
    simp only [stateDifference, Finset.mem_sdiff] at hxDifference
    exact hxDifference.2 hxDifference.1
  result_eq := by
    classical
    ext x
    simp only [stateUnion, stateDifference, Finset.mem_union, Finset.mem_sdiff]
    tauto

/-- The actual computed split changes state and has disjoint local endpoints. -/
def strictStep : StrictNativeStep sourceState targetState where
  step := nativeStep
  endpoints_disjoint := by decide
  ne := by decide

/-- One-edge actual strict native path over computed states. -/
def path : StrictNativePath sourceState targetState :=
  .cons strictStep (.nil targetState)

/-- Actual executable path packet for the split. -/
def packet : Packet F3 2 1 1 := ⟨sourceState, targetState, path⟩

/-- The fixture factors have their intended boundary coordinates. -/
example : (e0.1 0, e0.1 1, e1.1 0, e1.1 1, e01.1 0, e01.1 1) =
    (1, 0, 0, 1, 1, 1) := by decide

/-- The computed source and target states contain exactly the intended fixture atoms. -/
example : sourceAtom ∈ sourceState ∧ leftAtom ∉ sourceState ∧ rightAtom ∉ sourceState ∧
    sourceAtom ∉ targetState ∧ leftAtom ∈ targetState ∧ rightAtom ∈ targetState := by decide

#eval packet.stateTrace.map fun S =>
  (decide (sourceAtom ∈ S), decide (leftAtom ∈ S), decide (rightAtom ∈ S))

#eval packet.edgeTrace.map fun edge =>
  ((decide (sourceAtom ∈ edge.1), decide (leftAtom ∈ edge.1), decide (rightAtom ∈ edge.1)),
   (decide (sourceAtom ∈ edge.2), decide (leftAtom ∈ edge.2), decide (rightAtom ∈ edge.2)))

#eval packet.localEndpointTrace.map fun edge =>
  ((decide (sourceAtom ∈ edge.1), decide (leftAtom ∈ edge.1), decide (rightAtom ∈ edge.1)),
   (decide (sourceAtom ∈ edge.2), decide (leftAtom ∈ edge.2), decide (rightAtom ∈ edge.2)))

#eval stateTrace targetState (reverse path) |>.map fun S =>
  (decide (sourceAtom ∈ S), decide (leftAtom ∈ S), decide (rightAtom ∈ S))

end Execution

#check @ComputedState.singleton
#check @ComputedState.union
#check @reverseStep
#check @append
#check @snoc
#check @reverse
#check @stateTrace
#check @edgeTrace
#check @localEndpointTrace
#check @Packet
#check @heightBound_reverse
#print axioms reverseStep
#print axioms append
#print axioms reverse
#print axioms stateTrace
#print axioms Execution.packet
#print axioms heightBound_reverse

end FieldNativeExecutablePath
end BilinearComplexity
