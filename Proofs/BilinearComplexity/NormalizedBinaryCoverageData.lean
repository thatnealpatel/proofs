import BilinearComplexity.NormalizedBinaryFiniteAction
import BilinearComplexity.NormalizedBinaryFiveCircuitRows

set_option autoImplicit false

/-!
# Checked coverage-table data for normalized binary relations

This module supplies the proof-bearing data boundary for a generated coverage
table. Serialized target terms remain triples of natural-number bit masks until
a small decoder checks positivity and profile bounds. A raw coverage row then
contains only a selected-row index, the existing `RawProfileAction`, and those
literal endpoint masks. Its checker delegates matrix validity, orientation
validity, and exact ordered endpoint equality to the existing finite action
checker and returns an actual `ActionWitness` in `Type`.

The thirteen replay rows are exposed through homogeneous, profile-indexed
families. No coverage table, semantic enumeration, external count, or hash is
trusted or asserted here.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.NormalizedBinaryCoverageData

open NormalizedBinaryCarrier
open NormalizedBinaryFiniteAction
open NormalizedBinaryFiveCircuitRows
open NormalizedBinaryFiveCircuitCertificate
open Scheme.Action

/-- A profile-homogeneous selected replay row and its existing checked
five-circuit certificate. -/
structure RowSource (p : Profile) where
  /-- The ordered two-side and three-side endpoints of the selected row. -/
  endpoints : RelationEndpoints p
  /-- The already kernel-replayed certificate for those exact endpoints. -/
  certificate : FiveCircuitCertificate p endpoints.left endpoints.right

/-- The selected profile-`221` replay rows, in external row-index order. -/
def selectedRowSources221 : Fin 3 → RowSource profile221 := ![
  ⟨⟨row22101Start, row22101Finish⟩, certified22101.certificate⟩,
  ⟨⟨row22102Start, row22102Finish⟩, certified22102.certificate⟩,
  ⟨⟨row22103Start, row22103Finish⟩, certified22103.certificate⟩]

/-- The selected profile-`411` replay row, in external row-index order. -/
def selectedRowSources411 : Fin 1 → RowSource profile411 := ![
  ⟨⟨row41101Start, row41101Finish⟩, certified41101.certificate⟩]

/-- The selected profile-`321` replay rows, in external row-index order. -/
def selectedRowSources321 : Fin 6 → RowSource profile321 := ![
  ⟨⟨row32101Start, row32101Finish⟩, certified32101.certificate⟩,
  ⟨⟨row32102Start, row32102Finish⟩, certified32102.certificate⟩,
  ⟨⟨row32103Start, row32103Finish⟩, certified32103.certificate⟩,
  ⟨⟨row32104Start, row32104Finish⟩, certified32104.certificate⟩,
  ⟨⟨row32105Start, row32105Finish⟩, certified32105.certificate⟩,
  ⟨⟨row32106Start, row32106Finish⟩, certified32106.certificate⟩]

/-- The selected profile-`222` replay rows, in external row-index order. -/
def selectedRowSources222 : Fin 3 → RowSource profile222 := ![
  ⟨⟨row22201Start, row22201Finish⟩, certified22201.certificate⟩,
  ⟨⟨row22202Start, row22202Finish⟩, certified22202.certificate⟩,
  ⟨⟨row22203Start, row22203Finish⟩, certified22203.certificate⟩]

example : (selectedRowSources221 0).endpoints.left = row22101Start := rfl
example : (selectedRowSources411 0).endpoints.right = row41101Finish := rfl
example : (selectedRowSources321 5).endpoints.left = row32106Start := rfl
example : (selectedRowSources222 2).endpoints.right = row22203Finish := rfl

/-- Three externally serialized positive coordinate-vector masks for one
normalized carrier term. -/
structure SerializedTermMasks where
  /-- The first-factor bit mask. -/
  first : ℕ
  /-- The second-factor bit mask. -/
  second : ℕ
  /-- The third-factor bit mask. -/
  third : ℕ
  deriving DecidableEq, Repr

namespace SerializedTermMasks

/-- The six elementary checks saying that the three masks encode nonzero
vectors within the dimensions of `p`. -/
def Valid (p : Profile) (m : SerializedTermMasks) : Prop :=
  0 < m.first ∧ m.first < 2 ^ p.first ∧
    0 < m.second ∧ m.second < 2 ^ p.second ∧
    0 < m.third ∧ m.third < 2 ^ p.third

/-- Serialized-term validity is constructively decidable. -/
instance (p : Profile) (m : SerializedTermMasks) : Decidable (m.Valid p) := by
  unfold Valid
  infer_instance

/-- Decode one mask triple only after checking all positivity and profile-bound
conditions. -/
def decode? (p : Profile) (m : SerializedTermMasks) : Option (Carrier p) :=
  if h : m.Valid p then
    some (carrierOfMasks p m.first m.second m.third
      h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
  else
    none

/-- A successful term decode records exactly the existing mask-based carrier
term, with the checked inequalities as its proof arguments. -/
theorem decode?_eq_some_of_valid (p : Profile) (m : SerializedTermMasks)
    (h : m.Valid p) :
    m.decode? p = some (carrierOfMasks p m.first m.second m.third
      h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2) := by
  simp only [decode?, h, dite_true]

end SerializedTermMasks

example :
    (⟨3, 2, 1⟩ : SerializedTermMasks).decode? profile221 =
      some (carrierOfMasks profile221 3 2 1
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)) := by
  decide

example :
    (⟨0, 1, 1⟩ : SerializedTermMasks).decode? profile221 = none := by
  decide

/-- Literal serialized left and right endpoint lists. List order is irrelevant
after successful decoding because normalized states are finite sets. -/
structure SerializedEndpoints where
  /-- Serialized masks for the ordered left endpoint. -/
  left : List SerializedTermMasks
  /-- Serialized masks for the ordered right endpoint. -/
  right : List SerializedTermMasks
  deriving DecidableEq, Repr

namespace SerializedEndpoints

/-- Decode a list of mask triples to the normalized finite-set state it
literally denotes. -/
def decodeState? (p : Profile) (terms : List SerializedTermMasks) :
    Option (State p) :=
  (terms.mapM (SerializedTermMasks.decode? p)).map List.toFinset

/-- Decode both serialized endpoint lists without exchanging their ordered
left and right slots. -/
def decode? (p : Profile) (endpoints : SerializedEndpoints) :
    Option (RelationEndpoints p) := do
  let left ← decodeState? p endpoints.left
  let right ← decodeState? p endpoints.right
  pure ⟨left, right⟩

end SerializedEndpoints

example :
    ({ left := [⟨1, 1, 1⟩], right := [⟨2, 2, 1⟩] } :
      SerializedEndpoints).decode? profile221 =
        some ⟨{carrierOfMasks profile221 1 1 1
          (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)},
          {carrierOfMasks profile221 2 2 1
          (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)}⟩ := by
  decide

/-- A profile-independent, decidable list representation of the three factor
vectors of a normalized term. -/
structure TermEntries where
  /-- Entries of the first factor, in increasing coordinate order. -/
  first : List F2
  /-- Entries of the second factor, in increasing coordinate order. -/
  second : List F2
  /-- Entries of the third factor, in increasing coordinate order. -/
  third : List F2
  deriving DecidableEq

/-- List the coordinates of a binary coordinate vector in increasing index
order. -/
def vectorEntries {d : ℕ} (x : CoordinateVector d) : List F2 := List.ofFn x

/-- Forget a typed normalized term to its three coordinate-entry lists. -/
def termEntries {p : Profile} (t : Carrier p) : TermEntries :=
  ⟨vectorEntries t.1.1, vectorEntries t.2.1.1, vectorEntries t.2.2.1⟩

/-- Compute the coordinate-entry lists produced by the three raw forward
matrices and then reorder those lists by the raw orientation. This is a
reflection of matrix evaluation, not a second profile-action semantics. -/
def rawMappedTermEntries {p : Profile}
    (raw : RawProfileAction p) (t : Carrier p) : TermEntries :=
  let a := vectorEntries (raw.first.mulVec t.1.1)
  let b := vectorEntries (raw.second.mulVec t.2.1.1)
  let c := vectorEntries (raw.third.mulVec t.2.2.1)
  match raw.orientation with
  | .abc => ⟨a, b, c⟩
  | .bca => ⟨b, c, a⟩
  | .cab => ⟨c, a, b⟩
  | .acb => ⟨a, c, b⟩
  | .cba => ⟨c, b, a⟩
  | .bac => ⟨b, a, c⟩

/-- Encode a normalized state as the finite set of its term-entry triples. -/
def stateEntries {p : Profile} (D : State p) : Finset TermEntries :=
  D.image termEntries

/-- Compute the finite set of raw matrix-and-orientation entry triples for a
source state. -/
def rawMappedStateEntries {p : Profile}
    (raw : RawProfileAction p) (D : State p) : Finset TermEntries :=
  D.image (rawMappedTermEntries raw)

example : vectorEntries (coordinateVectorOfMask 2 2 (by decide)) = [0, 1] := by
  decide

example : termEntries
    (carrierOfMasks profile221 3 2 1 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)) = ⟨[1, 1], [0, 1], [1]⟩ := by
  decide

/-- Forgetting a carrier cast along a profile equality does not change its
profile-independent coordinate-entry lists. -/
@[simp] theorem termEntries_castCarrier {p q : Profile} (h : p = q)
    (t : Carrier p) :
    termEntries (Equiv.cast (congrArg Carrier h) t) = termEntries t := by
  subst q
  rfl

/-- Coordinate-entry lists determine a coordinate vector exactly. -/
theorem vectorEntries_injective {d : ℕ} :
    Function.Injective (@vectorEntries d) := by
  exact List.ofFn_injective

/-- The three coordinate-entry lists determine a normalized carrier term
exactly. -/
theorem termEntries_injective {p : Profile} :
    Function.Injective (@termEntries p) := by
  intro s t hst
  apply Prod.ext
  · apply Subtype.ext
    exact vectorEntries_injective (congrArg TermEntries.first hst)
  · apply Prod.ext
    · apply Subtype.ext
      exact vectorEntries_injective (congrArg TermEntries.second hst)
    · apply Subtype.ext
      exact vectorEntries_injective (congrArg TermEntries.third hst)

/-- The entry-set encoding determines a normalized finite-set state exactly. -/
theorem stateEntries_injective {p : Profile} :
    Function.Injective (@stateEntries p) := by
  exact Finset.image_injective termEntries_injective

/-- Raw matrix-and-orientation entry evaluation agrees termwise with the
existing checked `ProfileAction` semantics. In particular this theorem removes
the opaque dependent profile cast before any concrete table computation. -/
theorem termEntries_toProfileAction {p : Profile}
    (raw : RawProfileAction p) (h : raw.Valid) (t : Carrier p) :
    termEntries ((raw.toProfileAction h).actTerm t) =
      rawMappedTermEntries raw t := by
  unfold ProfileAction.actTerm
  rw [termEntries_castCarrier (raw.toProfileAction h).profile_eq]
  rcases p with ⟨d₁, d₂, d₃⟩
  rcases raw with ⟨first, second, third, orientation⟩
  cases orientation <;> rfl

/-- Equality of reflected raw state images implies exact equality under the
existing checked state action. -/
theorem actState_eq_of_mappedStateEntries_eq {p : Profile}
    (raw : RawProfileAction p) (h : raw.Valid) (source target : State p)
    (heq : rawMappedStateEntries raw source = stateEntries target) :
    (raw.toProfileAction h).actState source = target := by
  apply stateEntries_injective
  rw [ProfileAction.actState_eq_image, stateEntries, Finset.image_image]
  calc
    source.image (termEntries ∘ (raw.toProfileAction h).actTerm) =
        source.image (rawMappedTermEntries raw) := by
      apply Finset.image_congr
      intro t _ht
      exact termEntries_toProfileAction raw h t
    _ = stateEntries target := heq

/-- Two reflected finite-set equalities check an exact ordered endpoint image
without reducing intrinsic GL values or dependent profile casts. -/
def EndpointImageEquations {p : Profile}
    (raw : RawProfileAction p) (source target : RelationEndpoints p) : Prop :=
  rawMappedStateEntries raw source.left = stateEntries target.left ∧
    rawMappedStateEntries raw source.right = stateEntries target.right

/-- Reflected endpoint-image equations are constructively decidable. -/
instance {p : Profile} (raw : RawProfileAction p)
    (source target : RelationEndpoints p) :
    Decidable (EndpointImageEquations raw source target) := by
  unfold EndpointImageEquations
  infer_instance

/-- Valid reflected endpoint equations produce the exact existing semantic
endpoint image equality. -/
theorem actEndpoints_eq_of_endpointImageEquations
    {p : Profile} (raw : RawProfileAction p) (h : raw.Valid)
    (source target : RelationEndpoints p)
    (heq : EndpointImageEquations raw source target) :
    (raw.toProfileAction h).actEndpoints source = target := by
  exact congrArg₂ RelationEndpoints.mk
    (actState_eq_of_mappedStateEntries_eq raw h source.left target.left heq.1)
    (actState_eq_of_mappedStateEntries_eq raw h source.right target.right heq.2)

/-- An unchecked serialized coverage candidate. It selects a homogeneous row,
supplies the existing raw matrix-and-orientation action, and gives independent
literal masks for the intended target endpoints. -/
structure RawCoverageAction (p : Profile) (ι : Type*) where
  /-- The source replay-row index. -/
  sourceRowIndex : ι
  /-- The three forward matrices followed by the mode orientation. -/
  profileAction : RawProfileAction p
  /-- The literal ordered target endpoint masks. -/
  target : SerializedEndpoints

namespace RawCoverageAction

/-- Decode only a raw candidate's literal target masks, without evaluating its
matrices, orientation, selected row, or action checker. Coverage-set equality
should compute through this projection rather than through `Entry.checked`. -/
def decodedTarget? {p : Profile} {ι : Type*} (raw : RawCoverageAction p ι) :
    Option (RelationEndpoints p) := raw.target.decode? p

/-- Decode the literal targets of a raw candidate list, dropping only malformed
mask endpoints. This computation is independent of all GL and action casts. -/
def decodedTargets {p : Profile} {ι : Type*} :
    List (RawCoverageAction p ι) → List (RelationEndpoints p)
  | [] => []
  | raw :: raws =>
      match raw.decodedTarget? with
      | none => decodedTargets raws
      | some target => target :: decodedTargets raws

/-- The finite set of literal typed targets of a raw candidate list, computed
without reducing any action witness. -/
def decodedTargetSet {p : Profile} {ι : Type*}
    (raws : List (RawCoverageAction p ι)) : Finset (RelationEndpoints p) :=
  (decodedTargets raws).toFinset

example : decodedTargets ([] : List (RawCoverageAction profile221 (Fin 3))) =
    [] := rfl

/-- The checked payload returned for a particular raw coverage candidate. It
retains the exact successful target decoding and an actual endpoint action
witness from the selected source row. -/
structure Checked {p : Profile} {ι : Type*} (rows : ι → RowSource p)
    (raw : RawCoverageAction p ι) where
  /-- The typed normalized target decoded from the literal masks. -/
  target : RelationEndpoints p
  /-- The target is exactly the decoding of the candidate's literal masks. -/
  target_decodes : raw.target.decode? p = some target
  /-- The existing checked action maps the selected row to that exact target. -/
  witness : ActionWitness (rows raw.sourceRowIndex).endpoints target

/-- Check target-mask validity, then delegate raw action validity and exact
ordered endpoint equality to `checkActionWitness`. On success the result
contains the actual `ActionWitness` rather than a Boolean or count. -/
def check {p : Profile} {ι : Type*} (rows : ι → RowSource p)
    (raw : RawCoverageAction p ι) : Option (Checked rows raw) :=
  match htarget : raw.target.decode? p with
  | none => none
  | some target =>
      (checkActionWitness raw.profileAction
        (rows raw.sourceRowIndex).endpoints target).map fun witness =>
          ⟨target, htarget, witness⟩

/-- A successful coverage check exposes the exact literal target decode and
the actual action witness used by downstream certificate transport. -/
theorem check_sound {p : Profile} {ι : Type*} (rows : ι → RowSource p)
    (raw : RawCoverageAction p ι) (checked : Checked rows raw)
    (_hcheck : raw.check rows = some checked) :
    raw.target.decode? p = some checked.target ∧
      checked.witness.action.actEndpoints
        (rows raw.sourceRowIndex).endpoints = checked.target := by
  exact ⟨checked.target_decodes, checked.witness.maps_endpoints⟩

/-- Valid reflected equations for an exactly decoded literal target prove
that the full existing coverage checker succeeds. -/
theorem check_isSome_of_endpointImageEquations {p : Profile} {ι : Type*}
    (rows : ι → RowSource p) (raw : RawCoverageAction p ι)
    (target : RelationEndpoints p) (hdecode : raw.decodedTarget? = some target)
    (hvalid : raw.profileAction.Valid)
    (heq : EndpointImageEquations raw.profileAction
      (rows raw.sourceRowIndex).endpoints target) :
    (raw.check rows).isSome = true := by
  change raw.target.decode? p = some target at hdecode
  unfold check
  split
  · rename_i hnone
    rw [hdecode] at hnone
    contradiction
  · rename_i decoded hsome
    have htarget : decoded = target :=
      Option.some.inj (hsome.symm.trans hdecode)
    subst decoded
    simp only [Option.isSome_map]
    apply (checkActionWitness_isSome_iff raw.profileAction
      (rows raw.sourceRowIndex).endpoints target).2
    let action := raw.profileAction.toProfileAction hvalid
    refine ⟨action, ?_, ?_⟩
    · exact RawProfileAction.check_eq_some_of_valid raw.profileAction hvalid
    · exact actEndpoints_eq_of_endpointImageEquations raw.profileAction hvalid
        (rows raw.sourceRowIndex).endpoints target heq

/-- Proof-bearing coverage-table storage. Its success proof makes `checked`
return the checker-produced target and `ActionWitness` in `Type`. -/
structure Entry {p : Profile} {ι : Type*} (rows : ι → RowSource p) where
  /-- The raw serialized candidate retained for auditing. -/
  raw : RawCoverageAction p ι
  /-- Kernel-checked evidence that all decoding, validity, and endpoint checks
  succeeded. -/
  check_succeeds : (raw.check rows).isSome = true

namespace Entry

/-- Build a proof-bearing table entry from the economical obligations used by
production literals: target-mask decoding, raw validity, and two reflected
finite-set equations. -/
def ofEndpointImageEquations {p : Profile} {ι : Type*}
    (rows : ι → RowSource p) (raw : RawCoverageAction p ι)
    (target : RelationEndpoints p) (hdecode : raw.decodedTarget? = some target)
    (hvalid : raw.profileAction.Valid)
    (heq : EndpointImageEquations raw.profileAction
      (rows raw.sourceRowIndex).endpoints target) : Entry rows where
  raw := raw
  check_succeeds :=
    check_isSome_of_endpointImageEquations rows raw target hdecode hvalid heq

/-- Economically check one raw table row by decoding its target and deciding
raw validity and the reflected endpoint equations. A successful result is an
`Entry`, hence still contains an actual witness for the existing semantics. -/
def reflectedCheck {p : Profile} {ι : Type*} (rows : ι → RowSource p)
    (raw : RawCoverageAction p ι) : Option (Entry rows) :=
  match htarget : raw.decodedTarget? with
  | none => none
  | some target =>
      if hvalid : raw.profileAction.Valid then
        if heq : EndpointImageEquations raw.profileAction
            (rows raw.sourceRowIndex).endpoints target then
          some (ofEndpointImageEquations rows raw target htarget hvalid heq)
        else none
      else none

/-- Economically check every raw candidate in a list, preserving order. -/
def reflectedCheckAll {p : Profile} {ι : Type*} (rows : ι → RowSource p) :
    List (RawCoverageAction p ι) → Option (List (Entry rows))
  | [] => some []
  | raw :: raws => do
      let entry ← reflectedCheck rows raw
      let entries ← reflectedCheckAll rows raws
      pure (entry :: entries)

example : reflectedCheckAll selectedRowSources221 [] = some [] := rfl

/-- A successful reflected single-row check retains exactly its input raw
candidate. -/
theorem reflectedCheck_raw {p : Profile} {ι : Type*} (rows : ι → RowSource p)
    (raw : RawCoverageAction p ι) (entry : Entry rows)
    (hcheck : reflectedCheck rows raw = some entry) : entry.raw = raw := by
  unfold reflectedCheck at hcheck
  split at hcheck <;> try contradiction
  split at hcheck <;> try contradiction
  split at hcheck <;> try contradiction
  exact Option.some.inj hcheck ▸ rfl

/-- A successful reflected list check retains exactly the input raw candidates
when the resulting entries are projected back to their serialized rows. -/
theorem reflectedCheckAll_raws {p : Profile} {ι : Type*}
    (rows : ι → RowSource p) (raws : List (RawCoverageAction p ι))
    (entries : List (Entry rows))
    (hcheck : reflectedCheckAll rows raws = some entries) :
    entries.map Entry.raw = raws := by
  induction raws generalizing entries with
  | nil =>
      simp only [reflectedCheckAll, Option.some.injEq] at hcheck
      subst entries
      rfl
  | cons raw raws ih =>
      simp only [reflectedCheckAll] at hcheck
      cases hfirst : reflectedCheck rows raw with
      | none =>
          rw [hfirst] at hcheck
          contradiction
      | some entry =>
          rw [hfirst] at hcheck
          cases htail : reflectedCheckAll rows raws with
          | none =>
              rw [htail] at hcheck
              contradiction
          | some tail =>
              rw [htail] at hcheck
              have hentries : entries = entry :: tail := Option.some.inj hcheck.symm
              subst entries
              rw [List.map_cons, reflectedCheck_raw rows raw entry hfirst,
                ih tail htail]

/-- Extracting a successfully reflected-checked list and projecting its raw
candidates returns the original list exactly. -/
theorem reflectedCheckAll_get_raws {p : Profile} {ι : Type*}
    (rows : ι → RowSource p) (raws : List (RawCoverageAction p ι))
    (hcheck : (reflectedCheckAll rows raws).isSome = true) :
    ((reflectedCheckAll rows raws).get hcheck).map Entry.raw = raws := by
  apply reflectedCheckAll_raws rows raws
  exact (Option.some_get hcheck).symm

/-- Extract the actual checked payload certified by a coverage-table entry. -/
def checked {p : Profile} {ι : Type*} {rows : ι → RowSource p}
    (entry : Entry rows) : entry.raw.Checked rows :=
  (entry.raw.check rows).get entry.check_succeeds

/-- Extract the exact typed target relation of a checked coverage-table entry. -/
def target {p : Profile} {ι : Type*} {rows : ι → RowSource p}
    (entry : Entry rows) : RelationEndpoints p := entry.checked.target

/-- Extract the actual `ActionWitness` mapping the indexed selected row to the
entry's exact typed target. -/
def witness {p : Profile} {ι : Type*} {rows : ι → RowSource p}
    (entry : Entry rows) :
    ActionWitness (rows entry.raw.sourceRowIndex).endpoints entry.target :=
  entry.checked.witness

/-- The extracted typed target still has the exact serialized-mask decode
recorded by the checker. -/
theorem target_decodes {p : Profile} {ι : Type*} {rows : ι → RowSource p}
    (entry : Entry rows) :
    entry.raw.target.decode? p = some entry.target :=
  entry.checked.target_decodes

end Entry

end RawCoverageAction

#check @RowSource
#check @selectedRowSources221
#check @SerializedTermMasks.decode?
#check @SerializedEndpoints.decode?
#check @RawCoverageAction
#check @RawCoverageAction.check
#check @RawCoverageAction.Entry
#check @RawCoverageAction.Entry.witness

#print axioms SerializedTermMasks.decode?_eq_some_of_valid
#print axioms RawCoverageAction.check_sound
#print axioms RawCoverageAction.Entry.target_decodes

end BilinearComplexity.NormalizedBinaryCoverageData
