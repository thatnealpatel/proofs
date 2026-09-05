import BilinearComplexity.NormalizedBinaryAllModePermutation
import BilinearComplexity.NormalizedBinaryCoverageData
import BilinearComplexity.NormalizedBinaryProfileOrientation
import BilinearComplexity.NormalizedBinaryRelationEnumeration

set_option autoImplicit false

/-!
# Generic proof-producing compiler for normalized binary coverage

This module integrates profile orientation, finite exact-relation enumeration,
checked coverage entries, action witnesses, and certificate transport. Its
extraction contract is table-generic: completeness is stated only as equality
between independently decoded literal targets and the semantic exact-relation
enumeration. Concrete generated tables and their completeness proofs belong in
a downstream module.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.NormalizedBinaryCoverage

open NormalizedBinaryCarrier
open NormalizedBinaryAllModePermutation
open NormalizedBinaryCoverageData
open NormalizedBinaryFiniteAction
open NormalizedBinaryFiveCircuitCertificate
open NormalizedBinaryProfileOrientation
open NormalizedBinaryModePermutation
open NormalizedBinaryRelationEnumeration
open RawCoverageAction
open Scheme.Action

/-- The finite set of exact typed targets extracted from proof-bearing checked
coverage entries. -/
def entryTargetSet {p : Profile} {ι : Type} {rows : ι → RowSource p}
    (entries : List (Entry rows)) : Finset (RelationEndpoints p) :=
  (entries.map Entry.target).toFinset

example {p : Profile} {ι : Type} (rows : ι → RowSource p) :
    entryTargetSet ([] : List (Entry rows)) = ∅ := rfl

/-- Projecting checked entries to their raw rows and independently decoding
those literal targets gives exactly the entries' checker-produced targets. -/
theorem decodedTargets_entry_raws {p : Profile} {ι : Type}
    {rows : ι → RowSource p} (entries : List (Entry rows)) :
    decodedTargets (entries.map Entry.raw) = entries.map Entry.target := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      simp only [List.map_cons, decodedTargets, decodedTarget?,
        Entry.target_decodes, ih]

/-- The target set of checked entries is definitionally tied to the
check-independent decoded target set of their raw serialized rows. -/
theorem entryTargetSet_eq_decodedTargetSet {p : Profile} {ι : Type}
    {rows : ι → RowSource p} (entries : List (Entry rows)) :
    entryTargetSet entries = decodedTargetSet (entries.map Entry.raw) := by
  rw [entryTargetSet, decodedTargetSet, decodedTargets_entry_raws]

/-- A checked entry together with proof that its exact target is a requested
ordered relation. -/
structure LocatedEntry {p : Profile} {ι : Type} (rows : ι → RowSource p)
    (target : RelationEndpoints p) : Type where
  /-- The selected proof-bearing table entry. -/
  entry : Entry rows
  /-- Its checker-produced target is literally the requested relation. -/
  target_eq : entry.target = target

/-- Constructively locate the first checked table entry with a requested exact
target.  The membership proof only rules out the empty branch; selection is
performed by decidable equality on the finite list. -/
def locateEntry {p : Profile} {ι : Type} {rows : ι → RowSource p}
    (target : RelationEndpoints p) :
    (entries : List (Entry rows)) → target ∈ entryTargetSet entries →
      LocatedEntry rows target
  | [], hmem => by
      have hnot : target ∉ (∅ : Finset (RelationEndpoints p)) := by simp
      exact (hnot hmem).elim
  | entry :: entries, hmem => by
      by_cases heq : entry.target = target
      · exact ⟨entry, heq⟩
      · apply locateEntry target entries
        have hne : target ≠ entry.target := Ne.symm heq
        simpa only [entryTargetSet, List.map_cons, List.toFinset_cons,
          Finset.mem_insert, hne, false_or] using hmem

/-- Looking up the head target selects that head, independently of later
duplicate targets. -/
theorem locateEntry_head {p : Profile} {ι : Type} {rows : ι → RowSource p}
    (entry : Entry rows) (entries : List (Entry rows))
    (hmem : entry.target ∈ entryTargetSet (entry :: entries)) :
    (locateEntry entry.target (entry :: entries) hmem).entry = entry := by
  unfold locateEntry
  split
  · rfl
  · rename_i hne
    exact (hne rfl).elim

/-- A proof-bearing checked coverage table.  Completeness mentions only the
literal target decoder, not action evaluation, matrix casts, counts, or hashes. -/
structure CoverageTable {p : Profile} {ι : Type}
    (rows : ι → RowSource p) : Type where
  /-- The checked entries retained for witness and certificate extraction. -/
  entries : List (Entry rows)
  /-- Their independently decoded literal targets are all semantic exact
  ordered relations at this profile. -/
  decoded_complete :
    decodedTargetSet (entries.map Entry.raw) = allExactRelations p

/-- The proof-producing output of compiling one exact relation against one
profile-homogeneous checked table. The action witness and transported
certificate are derived from these two fields below, rather than stored as
unconstrained additional data. -/
structure CanonicalCompilation {p : Profile} {ι : Type}
    (rows : ι → RowSource p) (target : ExactRelation p) : Type where
  /-- The selected checked entry; its raw payload exposes the replay-row index. -/
  entry : Entry rows
  /-- The entry's checked target is the requested semantic relation. -/
  target_eq : entry.target = target.1

/-- Reindex the target endpoint of an action witness along literal endpoint
equality. -/
def castActionWitnessTarget {p : Profile}
    {source target target' : RelationEndpoints p}
    (witness : ActionWitness source target) (h : target = target') :
    ActionWitness source target' := by
  subst target'
  exact witness

/-- Extract the actual checked action witness selected by a canonical
compilation. -/
def CanonicalCompilation.witness {p : Profile} {ι : Type}
    {rows : ι → RowSource p} {target : ExactRelation p}
    (compiled : CanonicalCompilation rows target) :
    ActionWitness (rows compiled.entry.raw.sourceRowIndex).endpoints target.1 :=
  castActionWitnessTarget compiled.entry.witness compiled.target_eq

/-- Transport the selected replay-row certificate through the selected checked
action witness. -/
def CanonicalCompilation.certificate {p : Profile} {ι : Type}
    {rows : ι → RowSource p} {target : ExactRelation p}
    (compiled : CanonicalCompilation rows target) :
    FiveCircuitCertificate p target.1.left target.1.right :=
  compiled.witness.transportCertificate
    (rows compiled.entry.raw.sourceRowIndex).certificate

/-- Extract the selected homogeneous replay-row index from a compilation. -/
def CanonicalCompilation.selectedRowIndex {p : Profile} {ι : Type}
    {rows : ι → RowSource p} {target : ExactRelation p}
    (compiled : CanonicalCompilation rows target) : ι :=
  compiled.entry.raw.sourceRowIndex

example {p : Profile} {ι : Type} {rows : ι → RowSource p}
    {target : ExactRelation p} (compiled : CanonicalCompilation rows target) :
    compiled.selectedRowIndex = compiled.entry.raw.sourceRowIndex := rfl

example {p : Profile} {ι : Type} {rows : ι → RowSource p}
    {target : ExactRelation p} (compiled : CanonicalCompilation rows target) :
    compiled.witness.action.actEndpoints
        (rows compiled.selectedRowIndex).endpoints = target.1 :=
  compiled.witness.maps_endpoints

/-- Compile any semantic exact relation from a checked table whose literal
serialized targets are complete. -/
def compileCanonical {p : Profile} {ι : Type} {rows : ι → RowSource p}
    (table : CoverageTable rows) (target : ExactRelation p) :
    CanonicalCompilation rows target := by
  have hmem : target.1 ∈ entryTargetSet table.entries := by
    rw [entryTargetSet_eq_decodedTargetSet, table.decoded_complete,
      mem_allExactRelations_iff]
    exact target.2
  let located := locateEntry target.1 table.entries hmem
  exact {
    entry := located.entry
    target_eq := located.target_eq
  }

/-- The row-index type for each of the four canonical profile families. -/
def FamilyRowIndex : CanonicalProfileFamily → Type
  | .family221 => Fin 3
  | .family411 => Fin 1
  | .family321 => Fin 6
  | .family222 => Fin 3

/-- The existing replay-row source family indexed uniformly by canonical
profile family. -/
def familyRowSources : (family : CanonicalProfileFamily) →
    FamilyRowIndex family → RowSource family.profile
  | .family221 => selectedRowSources221
  | .family411 => selectedRowSources411
  | .family321 => selectedRowSources321
  | .family222 => selectedRowSources222

example : (familyRowSources .family221 (by
      change Fin 3
      exact ⟨0, by omega⟩)).endpoints.left =
    NormalizedBinaryFiveCircuitRows.row22101Start := rfl

/-- A complete checked table at one canonical profile family. -/
abbrev FamilyCoverageTable (family : CanonicalProfileFamily) : Type :=
  CoverageTable (familyRowSources family)

/-- Complete checked coverage data for all four canonical profile families. -/
def FamilyCoverageTables : Type :=
  (family : CanonicalProfileFamily) → FamilyCoverageTable family

private theorem unorientState {p q : Profile}
    (o : Scheme.Action.Orientation)
    (h : permProfile o p = q) (D : State p) :
    cast (congrArg State (by
      calc
        permProfile (orientationInverse o) q =
            permProfile (orientationInverse o) (permProfile o p) := by rw [← h]
        _ = p := permProfile_inverse_left o p))
      (permuteState (orientationInverse o)
        (cast (congrArg State h) (permuteState o D))) = D := by
  cases h
  simp

/-- Transport a certificate on the concretely oriented endpoints back through
the inverse mode orientation to the original ordered endpoints. -/
def unorientCertificate {p : Profile}
    (choice : ProfileOrientation p) {A B : State p}
    (certificate : FiveCircuitCertificate choice.family.profile
      (choice.orientState A) (choice.orientState B)) :
    FiveCircuitCertificate p A B := by
  have hInverse : permProfile (orientationInverse choice.orientation)
      choice.family.profile = p := by
    calc
      permProfile (orientationInverse choice.orientation) choice.family.profile =
          permProfile (orientationInverse choice.orientation)
            (permProfile choice.orientation p) := by rw [← choice.profile_eq]
      _ = p := permProfile_inverse_left choice.orientation p
  let transported :=
    (certificate.permute (orientationInverse choice.orientation)).castProfile hInverse
  have hA : cast (congrArg State hInverse)
      (permuteState (orientationInverse choice.orientation)
        (choice.orientState A)) = A := by
    exact unorientState choice.orientation choice.profile_eq A
  have hB : cast (congrArg State hInverse)
      (permuteState (orientationInverse choice.orientation)
        (choice.orientState B)) = B := by
    exact unorientState choice.orientation choice.profile_eq B
  rw [hA, hB] at transported
  exact transported

/-- Full proof-producing output for one arbitrary exact normalized relation.
It records the explicit family/orientation, the canonical exact relation, and
the selected table entry. Its witness and both certificates are derived below
from this data, so the structure cannot contain an unrelated certificate. -/
structure CompilationResult {p : Profile} (target : ExactRelation p) : Type where
  /-- Explicit canonical family and mode orientation. -/
  choice : ProfileOrientation p
  /-- The exact relation obtained by applying that orientation to both ordered
  endpoint slots. -/
  oriented : ExactRelation choice.family.profile
  /-- The oriented left endpoint is the computed orientation of the input left. -/
  oriented_left : oriented.1.left = choice.orientState target.1.left
  /-- The oriented right endpoint is the computed orientation of the input right. -/
  oriented_right : oriented.1.right = choice.orientState target.1.right
  /-- The selected checked table entry at the oriented canonical profile. -/
  canonical : CanonicalCompilation (familyRowSources choice.family) oriented

/-- The selected checked action witness at the oriented canonical profile. -/
def CompilationResult.witness {p : Profile} {target : ExactRelation p}
    (compiled : CompilationResult target) :
    ActionWitness
      ((familyRowSources compiled.choice.family)
        compiled.canonical.selectedRowIndex).endpoints
      compiled.oriented.1 :=
  compiled.canonical.witness

/-- The selected replay-row certificate after checked action transport, before
undoing the profile orientation. -/
def CompilationResult.orientedCertificate {p : Profile}
    {target : ExactRelation p} (compiled : CompilationResult target) :
    FiveCircuitCertificate compiled.choice.family.profile
      compiled.oriented.1.left compiled.oriented.1.right :=
  compiled.canonical.certificate

/-- Derive the final certificate by rewriting the oriented endpoints to the
computed orientation and transporting through its inverse. -/
def CompilationResult.certificate {p : Profile} {target : ExactRelation p}
    (compiled : CompilationResult target) :
    FiveCircuitCertificate p target.1.left target.1.right :=
  unorientCertificate compiled.choice (by
    rw [← compiled.oriented_left, ← compiled.oriented_right]
    exact compiled.orientedCertificate)

/-- Extract the selected replay-row index from a full compilation. -/
def CompilationResult.selectedRowIndex {p : Profile} {target : ExactRelation p}
    (compiled : CompilationResult target) : FamilyRowIndex compiled.choice.family :=
  compiled.canonical.selectedRowIndex

/-- Compile an arbitrary exact normalized relation from parameterized complete
checked tables for all four canonical families.  The final concrete compiler
specializes this helper to generated kernel-checked coverage tables. -/
def compileWithCoverage (tables : FamilyCoverageTables) {p : Profile}
    (target : ExactRelation p) : CompilationResult target := by
  let orientedData := orientExactPair target.1.left target.1.right
    target.2.1 target.2.2.1 target.2.2.2.1 target.2.2.2.2.1
    target.2.2.2.2.2
  let orientedRelation : ExactRelation orientedData.choice.family.profile :=
    ⟨{
      left := orientedData.choice.orientState target.1.left
      right := orientedData.choice.orientState target.1.right
    }, orientedData.card_left, orientedData.card_right, orientedData.disjoint,
      orientedData.evaluation, orientedData.exact_profile⟩
  let canonical := compileCanonical (tables orientedData.choice.family)
    orientedRelation
  exact {
    choice := orientedData.choice
    oriented := orientedRelation
    oriented_left := rfl
    oriented_right := rfl
    canonical := canonical
  }

example (tables : FamilyCoverageTables) :
    let target : ExactRelation profile221 :=
      ⟨{ left := NormalizedBinaryReplay221.S0,
          right := NormalizedBinaryReplay221.S2 },
        NormalizedBinaryReplay221.state_cardinalities.1,
        NormalizedBinaryReplay221.state_cardinalities.2.2,
        NormalizedBinaryReplay221.designated_endpoint_exact_profile_221.1,
        NormalizedBinaryReplay221.endpoint_evaluations.2,
        NormalizedBinaryFiveCircuitCertificate.designated_endpoint_hasExactFactorProfile⟩
    (compileWithCoverage tables target).choice.family = .family221 ∧
      (compileWithCoverage tables target).choice.orientation = .abc ∧
      Nonempty (FiveCircuitCertificate profile221
        target.1.left target.1.right) := by
  dsimp only
  let target : ExactRelation profile221 :=
    ⟨{ left := NormalizedBinaryReplay221.S0,
        right := NormalizedBinaryReplay221.S2 },
      NormalizedBinaryReplay221.state_cardinalities.1,
      NormalizedBinaryReplay221.state_cardinalities.2.2,
      NormalizedBinaryReplay221.designated_endpoint_exact_profile_221.1,
      NormalizedBinaryReplay221.endpoint_evaluations.2,
      NormalizedBinaryFiveCircuitCertificate.designated_endpoint_hasExactFactorProfile⟩
  exact ⟨rfl, rfl, ⟨(compileWithCoverage tables target).certificate⟩⟩

#check @entryTargetSet_eq_decodedTargetSet
#check @locateEntry
#check @locateEntry_head
#check @castActionWitnessTarget
#check @CanonicalCompilation.witness
#check @CanonicalCompilation.certificate
#check @compileCanonical
#check @unorientCertificate
#check @CompilationResult.witness
#check @CompilationResult.orientedCertificate
#check @CompilationResult.certificate
#check @compileWithCoverage

#print axioms entryTargetSet_eq_decodedTargetSet
#print axioms compileCanonical
#print axioms unorientCertificate
#print axioms CompilationResult.certificate
#print axioms compileWithCoverage

end BilinearComplexity.NormalizedBinaryCoverage
