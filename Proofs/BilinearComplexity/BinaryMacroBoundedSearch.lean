import BilinearComplexity.BinaryContextualMacroRecognition
import BilinearComplexity.FiniteWeightedBoundedSearch
import BilinearComplexity.BinaryAmbientBoundedSearch
import Mathlib.Data.List.Sublists

set_option autoImplicit false

/-!
# Automatic provenance-preserving binary macro bounded search

Full ambient coordinate frames are the only geometric input. Ordered endpoint
loops implement exactly the public recognizer, and all native primitive
successors remain available. The weighted search retains an executable dependent
trace: each macro step contains its actual recognized compiler object, not an
unlinked label. Expansion charges its full native length and every internal
vertex. No deduplication, state quotient, or heuristic pruning is performed.
-/

namespace BilinearComplexity.BinaryMacroBoundedSearch

open BinaryCircuit BinaryAmbientCarrier BinaryAmbientMoves
open BinaryAmbientTensorCoordinates BinaryAmbientFullFrame
open BinaryContextualMacroRecognition
open NormalizedBinaryCarrier (F2)

universe u v w

variable {U : Type u} {V : Type v} {W : Type w}
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [Module F2 U] [Module F2 V] [Module F2 W]
variable [DecidableEq U] [DecidableEq V] [DecidableEq W]
variable {a b c : ℕ}

private theorem f2_cases (x : F2) : x = 0 ∨ x = 1 := by
  have hx : x.val < 2 := ZMod.val_lt x
  have hv : x.val = 0 ∨ x.val = 1 := by omega
  rcases hv with hv | hv
  · left
    apply ZMod.val_injective
    simpa using hv
  · right
    apply ZMod.val_injective
    exact hv

local instance : FinEnum F2 :=
  FinEnum.ofList [0, 1] (by
    intro x
    rcases f2_cases x with h | h <;> simp [h])

/-- Fixed-cardinality subsets in the order induced by a duplicate-free list. -/
def endpointSets {α : Type*} [DecidableEq α] (terms : List α) (n : ℕ) :
    List (Finset α) :=
  (terms.sublistsLen n).map List.toFinset

/-- Ordered endpoint enumeration agrees exactly with the standard subset and
cardinality conditions, including cardinality zero. -/
theorem mem_endpointSets_iff {α : Type*} [DecidableEq α]
    (terms : List α) (hn : terms.Nodup) (n : ℕ) (s : Finset α) :
    s ∈ endpointSets terms n ↔ s ⊆ terms.toFinset ∧ s.card = n := by
  constructor
  · intro hs
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hs
    obtain ⟨hsub, hlen⟩ := List.mem_sublistsLen.mp hl
    refine ⟨?_, (List.toFinset_card_of_nodup (hn.sublist hsub)).trans hlen⟩
    intro x hx
    exact List.mem_toFinset.mpr (hsub.subset (List.mem_toFinset.mp hx))
  · rintro ⟨hsub, hcard⟩
    let l := terms.filter fun x => decide (x ∈ s)
    have heq : l.toFinset = s := by
      ext x
      simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (hsub h), h⟩⟩
    refine List.mem_map.mpr ⟨l, ?_, heq⟩
    apply List.mem_sublistsLen.mpr
    refine ⟨List.filter_sublist, ?_⟩
    rw [← List.toFinset_card_of_nodup (hn.filter _), heq, hcard]

example : endpointSets ([0, 1, 2] : List ℕ) 2 = [{1, 2}, {0, 2}, {0, 1}] := by
  decide

/-- Constructively ordered full ambient carrier obtained from finite coordinates. -/
def ambientTermList (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) : List (Carrier U V W) :=
  (FinEnum.toList (NormalizedBinaryCarrier.Carrier (coordinateProfile a b c))).map
    (denormalizeTerm eU eV eW)

/-- The ordered ambient carrier contains every term exactly once. -/
theorem ambientTermList_nodup (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W) :
    (ambientTermList eU eV eW).Nodup := by
  exact FinEnum.nodup_toList.map (carrierEquiv eU eV eW).injective

/-- The constructive list represents the recognizer's full ambient finite set. -/
theorem ambientTermList_toFinset (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W) :
    (ambientTermList eU eV eW).toFinset = ambientTerms eU eV eW := by
  ext t
  constructor
  · intro _
    exact mem_ambientTerms eU eV eW t
  · intro _
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨normalizeTerm eU eV eW t,
      FinEnum.mem_toList _, denormalizeTerm_normalizeTerm eU eV eW t⟩

private theorem currentList_toFinset (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W) (D : State U V W) :
    ((ambientTermList eU eV eW).filter fun t => decide (t ∈ D)).toFinset = D := by
  rw [List.toFinset_filter, ambientTermList_toFinset]
  ext t
  simp [mem_ambientTerms]

/-- Ordered two-source/three-target and three-source/two-target loops. Neither
loop enumerates the power set of the whole state space. -/
def rawKeyList (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) (D : State U V W) :
    List (MacroKey (U := U) (V := V) (W := W)) :=
  let all := ambientTermList eU eV eW
  let current := all.filter fun t => decide (t ∈ D)
  ((endpointSets current 2).flatMap fun A =>
    (endpointSets all 3).map fun B => ⟨.forward, A, B⟩) ++
  ((endpointSets all 2).flatMap fun A =>
    (endpointSets current 3).map fun B => ⟨.reverse, A, B⟩)

/-- The ordered raw-key bridge is exact in both directions. -/
theorem mem_rawKeyList_iff (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W)
    (D : State U V W) (key : MacroKey (U := U) (V := V) (W := W)) :
    key ∈ rawKeyList eU eV eW D ↔ key ∈ rawKeys eU eV eW D := by
  have hall := ambientTermList_nodup eU eV eW
  simp only [rawKeyList, List.mem_append, List.mem_flatMap, List.mem_map,
    mem_endpointSets_iff _ hall, mem_endpointSets_iff _ (hall.filter _),
    ambientTermList_toFinset, currentList_toFinset,
    rawKeys_eq_union, Finset.mem_union]
  constructor
  · rintro (⟨A, hA, B, hB, heq⟩ | ⟨A, hA, B, hB, heq⟩)
    · apply Or.inl
      rw [forwardKeys_eq_image]
      apply Finset.mem_image.mpr
      exact ⟨(A, B), Finset.mem_product.mpr
        ⟨Finset.mem_powersetCard.mpr hA, Finset.mem_powersetCard.mpr hB⟩, heq⟩
    · apply Or.inr
      rw [reverseKeys_eq_image]
      apply Finset.mem_image.mpr
      exact ⟨(A, B), Finset.mem_product.mpr
        ⟨Finset.mem_powersetCard.mpr hA, Finset.mem_powersetCard.mpr hB⟩, heq⟩
  · intro h
    rcases h with h | h
    · rw [forwardKeys_eq_image] at h
      obtain ⟨⟨A, B⟩, hp, heq⟩ := Finset.mem_image.mp h
      obtain ⟨hA, hB⟩ := Finset.mem_product.mp hp
      exact Or.inl ⟨A, Finset.mem_powersetCard.mp hA,
        B, Finset.mem_powersetCard.mp hB, heq⟩
    · rw [reverseKeys_eq_image] at h
      obtain ⟨⟨A, B⟩, hp, heq⟩ := Finset.mem_image.mp h
      obtain ⟨hA, hB⟩ := Finset.mem_product.mp hp
      exact Or.inr ⟨A, Finset.mem_powersetCard.mp hA,
        B, Finset.mem_powersetCard.mp hB, heq⟩

/-- Automatically admitted keys in deterministic raw-loop order. The sole
shortcut skips recognition below its proved minimum cost of two. -/
def recognizedKeyList (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) (D : State U V W) (k H : ℕ) :
    List (MacroKey (U := U) (V := V) (W := W)) :=
  if k < 2 then [] else
    (rawKeyList eU eV eW D).filter fun key =>
      decide (PassesBounds eU eV eW D k H key)

/-- Ordered admission is exactly the public recognizer, including the
minimum-cost shortcut. No admitted key is discarded. -/
theorem mem_recognizedKeyList_iff (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W)
    (D : State U V W) (k H : ℕ) (key : MacroKey (U := U) (V := V) (W := W)) :
    key ∈ recognizedKeyList eU eV eW D k H ↔
      key ∈ recognizeMacroKeys eU eV eW D k H := by
  by_cases hk : k < 2
  · rw [recognizedKeyList, if_pos hk,
      recognizeMacroKeys_eq_empty_of_lt_two eU eV eW D k H hk]
    simp
  · simp only [recognizedKeyList, if_neg hk, List.mem_filter,
      decide_eq_true_eq, mem_rawKeyList_iff, recognizeMacroKeys, Finset.mem_filter]

/-- Full ambient primitive successor adapter. Its runtime computation uses the
existing complete normalized native enumerator. -/
def primitiveSuccessors (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
    (eW : Coord c ≃ₗ[F2] W) (D : State U V W) :
    List (FiniteBoundedSearch.Successor (AllModeMove (U := U) (V := V) (W := W)) D) :=
  (NormalizedBinaryNativeSuccessors.certifiedSuccessors
    (normalizeState eU eV eW D)).map fun edge =>
    { finish := denormalizeState eU eV eW edge.finish
      edge := (allModeMove_iff_normalized eU eV eW _ _).mpr (by
        simpa only [normalizeState_denormalizeState] using edge.edge) }

/-- All intrinsic ambient primitive edges, not merely edges in endpoint spans,
are covered by the automatic primitive adapter. -/
theorem primitiveSuccessors_complete (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W)
    {D E : State U V W} (h : AllModeMove D E) :
    ∃ edge ∈ primitiveSuccessors eU eV eW D, edge.finish = E := by
  obtain ⟨edge, hm, he⟩ :=
    NormalizedBinaryNativeSuccessors.exists_mem_certifiedSuccessors_iff.mpr
      ((allModeMove_iff_normalized eU eV eW D E).mp h)
  refine ⟨_, List.mem_map.mpr ⟨edge, hm, rfl⟩, ?_⟩
  change denormalizeState eU eV eW edge.finish = E
  rw [he, denormalizeState_normalizeState]

/-- Membership in the ambient primitive adapter is exactly intrinsic legality. -/
theorem exists_mem_primitiveSuccessors_iff (eU : Coord a ≃ₗ[F2] U)
    (eV : Coord b ≃ₗ[F2] V) (eW : Coord c ≃ₗ[F2] W) {D E : State U V W} :
    (∃ edge ∈ primitiveSuccessors eU eV eW D, edge.finish = E) ↔ AllModeMove D E := by
  constructor
  · rintro ⟨edge, _, he⟩
    simpa only [he] using edge.edge
  · exact primitiveSuccessors_complete eU eV eW

variable (eU : Coord a ≃ₗ[F2] U) (eV : Coord b ≃ₗ[F2] V)
  (eW : Coord c ≃ₗ[F2] W)

private theorem compileRecognized_key (D : State U V W) (k H : ℕ)
    (key : MacroKey (U := U) (V := V) (W := W))
    (h : key ∈ recognizeMacroKeys eU eV eW D k H) :
    (compileRecognized eU eV eW D k H key h).key = key := by
  unfold compileRecognized
  split
  · rfl
  · next hn =>
      obtain ⟨ha, _⟩ := (mem_recognizeMacroKeys_iff eU eV eW D k H key).mp h
      exact (hn ha).elim

/-- A recognized macro together with its already materialized native path.
The equality keeps the cache tied to the public semantic compiler object. -/
structure CachedMacro (D : State U V W) where
  result : RecognizedMacro eU eV eW D
  path : MovePath (AllModeMove (U := U) (V := V) (W := W)) D result.finish
  path_eq : path = result.path

/-- Materialize exactly the directed path of a recognized macro. -/
def CachedMacro.ofRecognized {D : State U V W} (result : RecognizedMacro eU eV eW D) :
    CachedMacro eU eV eW D :=
  { result := result, path := result.path, path_eq := rfl }

example {D : State U V W} (result : RecognizedMacro eU eV eW D) :
    (CachedMacro.ofRecognized eU eV eW result).path = result.path := rfl

private theorem recognized_eq_of_key_eq {D : State U V W}
    (left right : RecognizedMacro eU eV eW D) (h : left.key = right.key) : left = right := by
  cases left
  cases right
  cases h
  rfl

private theorem CachedMacro.eq_of_result_eq {D : State U V W}
    (left right : CachedMacro eU eV eW D) (h : left.result = right.result) : left = right := by
  cases left with
  | mk leftResult leftPath leftEq =>
      cases right with
      | mk rightResult rightPath rightEq =>
          cases h
          cases leftEq
          cases rightEq
          rfl

/-- The cached path retains the recognized macro's semantic orbit, exact
positive cost, and shortestness against every ambient native competitor. -/
theorem CachedMacro.certified {D : State U V W} (cached : CachedMacro eU eV eW D) :
    BinaryFiveCircuitCompiler.AmbientInOrbit
        cached.result.compilation.label cached.result.left cached.result.right ∧
      (cached.path.length = 2 ∨ cached.path.length = 3) ∧
      0 < cached.path.length ∧
      ∀ competitor : MovePath (AllModeMove (U := U) (V := V) (W := W))
        D cached.result.finish, cached.path.length ≤ competitor.length := by
  simpa only [cached.path_eq] using cached.result.certified

/-- An admitted record retains the exact path used by its complete bounds test. -/
structure AdmittedMacro (k H : ℕ) (D : State U V W) extends CachedMacro eU eV eW D where
  admitted : result.key ∈ recognizeMacroKeys eU eV eW D k H
  length_le : path.length ≤ k
  altitude_le : path.altitude ≤ H

private def admitMacroKey (D : State U V W) (k H : ℕ)
    (key : MacroKey (U := U) (V := V) (W := W)) : Option (AdmittedMacro eU eV eW k H D) :=
  if ha : Applicable eU eV eW D key then
    let result := compileApplicable eU eV eW D key ha
    let path := result.path
    if hb : path.length ≤ k ∧ path.altitude ≤ H then
      some { result := result, path := path, path_eq := rfl
             admitted := (mem_recognizeMacroKeys_iff eU eV eW D k H key).mpr ⟨ha, hb⟩
             length_le := hb.1, altitude_le := hb.2 }
    else none
  else none

private theorem admitMacroKey_key (D : State U V W) (k H : ℕ)
    (key : MacroKey (U := U) (V := V) (W := W)) :
    (admitMacroKey eU eV eW D k H key).map (fun entry => entry.result.key) =
      if PassesBounds eU eV eW D k H key then some key else none := by
  by_cases ha : Applicable eU eV eW D key
  · simp only [admitMacroKey, dif_pos ha, PassesBounds]
    by_cases hb : (compileApplicable eU eV eW D key ha).path.length ≤ k ∧
        (compileApplicable eU eV eW D key ha).path.altitude ≤ H
    · simp only [dif_pos hb, if_pos hb, Option.map_some]
      rfl
    · simp only [dif_neg hb, if_neg hb, Option.map_none]
  · simp [admitMacroKey, PassesBounds, ha]

/-- Scan the unchanged raw-key order and retain the directed native path that
passed applicability and the exact full length/altitude bounds. -/
def admittedMacros (D : State U V W) (k H : ℕ) : List (AdmittedMacro eU eV eW k H D) :=
  if k < 2 then [] else (rawKeyList eU eV eW D).filterMap (admitMacroKey eU eV eW D k H)

/-- Projecting admitted records gives literally the previous ordered key-list
expression, including its order and duplicate multiplicities. -/
theorem admittedMacros_keys (D : State U V W) (k H : ℕ) :
    (admittedMacros eU eV eW D k H).map (fun entry => entry.result.key) =
      recognizedKeyList eU eV eW D k H := by
  by_cases hk : k < 2
  · simp only [admittedMacros, recognizedKeyList, if_pos hk, List.map_nil]
  · rw [admittedMacros, recognizedKeyList, if_neg hk, if_neg hk, List.map_filterMap,
      ← List.filterMap_eq_filter]
    apply congrArg (fun f => (rawKeyList eU eV eW D).filterMap f)
    funext key
    rw [admitMacroKey_key]
    by_cases hb : PassesBounds eU eV eW D k H key <;> simp [Option.guard, hb]

/-- Cached admission covers exactly the public recognizer, without reconstructing
paths from an erased key list at runtime. -/
theorem exists_mem_admittedMacros_iff (D : State U V W) (k H : ℕ)
    (key : MacroKey (U := U) (V := V) (W := W)) :
    (∃ entry ∈ admittedMacros eU eV eW D k H, entry.result.key = key) ↔
      key ∈ recognizeMacroKeys eU eV eW D k H := by
  rw [← List.mem_map, admittedMacros_keys, mem_recognizedKeyList_iff]

/-- A typed search step retains either the actual primitive edge or a recognized
macro together with the native path retained by automatic admission. -/
inductive Step (k H : ℕ) (D : State U V W)
  | primitive (edge : FiniteBoundedSearch.Successor
      (AllModeMove (U := U) (V := V) (W := W)) D)
  | macroStep (cached : CachedMacro eU eV eW D)
      (admitted : cached.result.key ∈ recognizeMacroKeys eU eV eW D k H)

/-- The actual native endpoint of an annotated step. -/
abbrev Step.finish {k H : ℕ} {D : State U V W} : Step eU eV eW k H D → State U V W
  | .primitive edge => edge.finish
  | .macroStep cached _ => cached.result.finish

/-- Expand an annotated step to its complete primitive native path. -/
def Step.path {k H : ℕ} {D : State U V W} (step : Step eU eV eW k H D) :
    MovePath (AllModeMove (U := U) (V := V) (W := W)) D (step.finish eU eV eW) :=
  match step with
  | .primitive edge => MovePath.one edge.edge
  | .macroStep cached _ => cached.path

private theorem one_length {α : Type*} {R : Finset α → Finset α → Prop}
    {D E : Finset α} (edge : R D E) : (MovePath.one edge).length = 1 := by
  simp only [MovePath.one, MovePath.length]

private theorem trans_one_altitude {α : Type*} {R : Finset α → Finset α → Prop}
    {D E F : Finset α} (path : MovePath R D E) (edge : R E F) :
    (path.trans (MovePath.one edge)).altitude = max path.altitude F.card := by
  simp only [MovePath.one, MovePath.trans, MovePath.altitude]

/-- All annotated steps have positive actual primitive cost. -/
theorem Step.positive {k H : ℕ} {D : State U V W} (step : Step eU eV eW k H D) :
    0 < (step.path eU eV eW).length := by
  cases step with
  | primitive edge =>
      rw [Step.path, one_length]
      exact Nat.zero_lt_succ 0
  | macroStep cached _ =>
      rw [Step.path, cached.path_eq]
      exact cached.result.length_pos

/-- Convert ordered admitted records to typed steps without recomputing the
native paths that already passed the admission bounds. -/
def macroSteps (D : State U V W) (k H : ℕ) : List (Step eU eV eW k H D) :=
  (admittedMacros eU eV eW D k H).map fun entry =>
    .macroStep entry.toCachedMacro entry.admitted

/-- Every publicly recognized macro is present in the automatic step provider. -/
theorem macroSteps_complete (D : State U V W) (k H : ℕ)
    (key : MacroKey (U := U) (V := V) (W := W))
    (h : key ∈ recognizeMacroKeys eU eV eW D k H) :
    Step.macroStep (CachedMacro.ofRecognized eU eV eW
      (compileRecognized eU eV eW D k H key h))
      (by rw [CachedMacro.ofRecognized, compileRecognized_key]; exact h) ∈
      macroSteps eU eV eW D k H := by
  obtain ⟨entry, hm, he⟩ := (exists_mem_admittedMacros_iff eU eV eW D k H key).mpr h
  have hresult : entry.result = compileRecognized eU eV eW D k H key h := by
    apply recognized_eq_of_key_eq eU eV eW
    rw [compileRecognized_key]
    exact he
  have hcached : entry.toCachedMacro = CachedMacro.ofRecognized eU eV eW
      (compileRecognized eU eV eW D k H key h) :=
    CachedMacro.eq_of_result_eq eU eV eW _ _ hresult
  apply List.mem_map.mpr
  refine ⟨entry, hm, ?_⟩
  congr 1

/-- The proof-bearing provider is exactly the ordered recognition list mapped
through the public compiler; it adds no supplied or invented macros. -/
theorem mem_macroSteps_iff (D : State U V W) (k H : ℕ) (step : Step eU eV eW k H D) :
    step ∈ macroSteps eU eV eW D k H ↔
      ∃ key, ∃ h : key ∈ recognizeMacroKeys eU eV eW D k H,
        Step.macroStep (CachedMacro.ofRecognized eU eV eW
          (compileRecognized eU eV eW D k H key h))
          (by rw [CachedMacro.ofRecognized, compileRecognized_key]; exact h) = step := by
  constructor
  · intro hm
    obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hm
    refine ⟨entry.result.key, entry.admitted, ?_⟩
    have hcached : CachedMacro.ofRecognized eU eV eW
        (compileRecognized eU eV eW D k H entry.result.key entry.admitted) = entry.toCachedMacro := by
      apply CachedMacro.eq_of_result_eq eU eV eW
      apply recognized_eq_of_key_eq eU eV eW
      exact compileRecognized_key eU eV eW D k H entry.result.key entry.admitted
    congr 1
  · rintro ⟨key, h, rfl⟩
    exact macroSteps_complete eU eV eW D k H key h

/-- Primitive expansion is always retained alongside automatic macro steps. -/
def availableSteps (D : State U V W) (k H : ℕ) : List (Step eU eV eW k H D) :=
  (primitiveSuccessors eU eV eW D).map Step.primitive ++ macroSteps eU eV eW D k H

/-- A dependent executable trace whose macro nodes retain their actual
recognized objects at the exact intermediate source state. -/
inductive Trace (k H : ℕ) (D : State U V W) : State U V W → Type (max u v w)
  | root : Trace k H D D
  | snoc {E : State U V W} (prior : Trace k H D E) (step : Step eU eV eW k H E) :
      Trace k H D (step.finish eU eV eW)

/-- Expand the selected trace, without changing or reconstructing any macro. -/
def Trace.path {k H : ℕ} {D E : State U V W} (trace : Trace eU eV eW k H D E) :
    MovePath (AllModeMove (U := U) (V := V) (W := W)) D E :=
  match trace with
  | .root => .singleton D
  | .snoc prior step => (prior.path).trans (step.path eU eV eW)

/-- The ordered recognized macros actually occurring in an executable trace,
paired with their intermediate source states. -/
def Trace.macros {k H : ℕ} {D E : State U V W} (trace : Trace eU eV eW k H D E) :
    List (Σ X, RecognizedMacro eU eV eW X) :=
  match trace with
  | .root => []
  | .snoc prior (.primitive _) => prior.macros
  | .snoc prior (.macroStep cached _) => prior.macros ++ [⟨_, cached.result⟩]

/-- Every retained trace macro is admitted and still carries its semantic orbit,
exact cost two or three, positive cost, and universal ambient shortestness. -/
theorem Trace.macro_certificates {k H : ℕ} {D E : State U V W}
    (trace : Trace eU eV eW k H D E)
    (entry : Σ X, RecognizedMacro eU eV eW X) (hm : entry ∈ trace.macros eU eV eW) :
    entry.2.key ∈ recognizeMacroKeys eU eV eW entry.1 k H ∧
      BinaryFiveCircuitCompiler.AmbientInOrbit
        entry.2.compilation.label entry.2.left entry.2.right ∧
      (entry.2.path.length = 2 ∨ entry.2.path.length = 3) ∧
      0 < entry.2.path.length ∧
      ∀ competitor : MovePath (AllModeMove (U := U) (V := V) (W := W))
        entry.1 entry.2.finish, entry.2.path.length ≤ competitor.length := by
  suffices ha : entry.2.key ∈ recognizeMacroKeys eU eV eW entry.1 k H from
    ⟨ha, entry.2.certified⟩
  induction trace with
  | root => simp [Trace.macros] at hm
  | snoc prior step ih =>
      cases step with
      | primitive edge => exact ih hm
      | macroStep result admitted =>
          simp only [Trace.macros, List.mem_append, List.mem_singleton] at hm
          rcases hm with hm | heq
          · exact ih hm
          · cases heq
            exact admitted

private theorem path_trans_assoc {α : Type*} {R : Finset α → Finset α → Prop}
    {D E F G : Finset α} (first : MovePath R D E) (second : MovePath R E F)
    (third : MovePath R F G) :
    (first.trans second).trans third = first.trans (second.trans third) := by
  induction third with
  | singleton => rfl
  | snoc prior edge ih => simp only [MovePath.trans, ih]

/-- Every reported macro is literally a segment of the trace's expanded native
path, with matching intermediate source and target, not merely an attached label. -/
theorem Trace.macro_factorization {k H : ℕ} {D E : State U V W}
    (trace : Trace eU eV eW k H D E)
    (entry : Σ X, RecognizedMacro eU eV eW X) (hm : entry ∈ trace.macros eU eV eW) :
    ∃ (before : MovePath (AllModeMove (U := U) (V := V) (W := W)) D entry.1)
      (suffix : MovePath (AllModeMove (U := U) (V := V) (W := W)) entry.2.finish E),
      trace.path eU eV eW = (before.trans entry.2.path).trans suffix := by
  induction trace with
  | root => simp [Trace.macros] at hm
  | snoc prior step ih =>
      cases step with
      | primitive edge =>
          obtain ⟨before, suffix, he⟩ := ih hm
          refine ⟨before, suffix.trans (MovePath.one edge.edge), ?_⟩
          simp only [Trace.path, Step.path, he, path_trans_assoc]
      | macroStep result admitted =>
          simp only [Trace.macros, List.mem_append, List.mem_singleton] at hm
          rcases hm with hm | heq
          · obtain ⟨before, suffix, he⟩ := ih hm
            refine ⟨before, suffix.trans result.path, ?_⟩
            simp only [Trace.path, Step.path, he, path_trans_assoc]
          · cases heq
            refine ⟨prior.path eU eV eW, .singleton result.result.finish, ?_⟩
            simp only [Trace.path, Step.path, MovePath.trans, result.path_eq]

/-- Ordered retained macro caches at their actual intermediate source states. -/
def Trace.cachedMacros {k H : ℕ} {D E : State U V W}
    (trace : Trace eU eV eW k H D E) : List (Σ X, CachedMacro eU eV eW X) :=
  match trace with
  | .root => []
  | .snoc prior (.primitive _) => prior.cachedMacros
  | .snoc prior (.macroStep cached _) => prior.cachedMacros ++ [⟨_, cached⟩]

/-- The cached trace accessor projects literally to the existing ordered
semantic macro trace, retaining duplicate entries and their source states. -/
theorem Trace.cachedMacros_results {k H : ℕ} {D E : State U V W}
    (trace : Trace eU eV eW k H D E) :
    (trace.cachedMacros eU eV eW).map
        (fun entry => (⟨entry.1, entry.2.result⟩ : Σ X, RecognizedMacro eU eV eW X)) =
      trace.macros eU eV eW := by
  induction trace with
  | root => rfl
  | snoc prior step ih =>
      cases step <;> simp only [Trace.cachedMacros, Trace.macros, List.map_append,
        List.map_singleton, ih]

/-- Each retained cached path literally factors the expanded native trace. -/
theorem Trace.cached_macro_factorization {k H : ℕ} {D E : State U V W}
    (trace : Trace eU eV eW k H D E) (entry : Σ X, CachedMacro eU eV eW X)
    (hm : entry ∈ trace.cachedMacros eU eV eW) :
    ∃ (before : MovePath (AllModeMove (U := U) (V := V) (W := W)) D entry.1)
      (suffix : MovePath (AllModeMove (U := U) (V := V) (W := W)) entry.2.result.finish E),
      trace.path eU eV eW = (before.trans entry.2.path).trans suffix := by
  have hsemantic : (⟨entry.1, entry.2.result⟩ : Σ X, RecognizedMacro eU eV eW X) ∈
      trace.macros eU eV eW := by
    rw [← trace.cachedMacros_results eU eV eW]
    exact List.mem_map.mpr ⟨entry, hm, rfl⟩
  obtain ⟨before, suffix, he⟩ := trace.macro_factorization eU eV eW _ hsemantic
  exact ⟨before, suffix, by simpa only [entry.2.path_eq] using he⟩

/-- A candidate retains its typed trace, rather than erasing block provenance. -/
structure Candidate (k H : ℕ) (D : State U V W) where
  finish : State U V W
  trace : Trace eU eV eW k H D finish
  nativePath : MovePath (AllModeMove (U := U) (V := V) (W := W)) D finish
  expands : nativePath = trace.path eU eV eW

/-- A candidate caches its expanded native path, with exact trace equality. -/
abbrev Candidate.path {k H : ℕ} {D : State U V W} (candidate : Candidate eU eV eW k H D) :=
  candidate.nativePath

/-- The zero-edge candidate ensures the search domain is nonempty. -/
def Candidate.root (k H : ℕ) (D : State U V W) : Candidate eU eV eW k H D :=
  { finish := D, trace := .root, nativePath := .singleton D, expands := rfl }

/-- Append one annotated step, retaining all of its provenance. -/
def Candidate.extend {k H : ℕ} {D : State U V W}
    (candidate : Candidate eU eV eW k H D)
    (step : Step eU eV eW k H candidate.finish) : Candidate eU eV eW k H D :=
  { finish := step.finish eU eV eW
    trace := .snoc candidate.trace step
    nativePath := (candidate.path eU eV eW).trans (step.path eU eV eW)
    expands := by simp only [Candidate.path, Trace.path, candidate.expands] }

/-- The zero-edge annotated path expands to the standard singleton native path. -/
theorem Candidate.root_path (K H : ℕ) (D : State U V W) :
    (Candidate.root eU eV eW K H D).path eU eV eW = .singleton D := rfl

/-- Extension charges the full primitive length of its step, not unit macro cost. -/
theorem Candidate.extend_length {k H : ℕ} {D : State U V W}
    (candidate : Candidate eU eV eW k H D)
    (step : Step eU eV eW k H candidate.finish) :
    ((candidate.extend eU eV eW step).path eU eV eW).length =
      (candidate.path eU eV eW).length + (step.path eU eV eW).length :=
  FiniteWeightedBoundedSearch.MovePath.length_trans _ _

/-- Every retained macro cache is literally a segment of the candidate's
cached full native path, not only of its annotated trace expansion. -/
theorem Candidate.cached_macro_factorization {k H : ℕ} {D : State U V W}
    (candidate : Candidate eU eV eW k H D) (entry : Σ X, CachedMacro eU eV eW X)
    (hm : entry ∈ candidate.trace.cachedMacros eU eV eW) :
    ∃ (before : MovePath (AllModeMove (U := U) (V := V) (W := W)) D entry.1)
      (suffix : MovePath (AllModeMove (U := U) (V := V) (W := W))
        entry.2.result.finish candidate.finish),
      candidate.path eU eV eW = (before.trans entry.2.path).trans suffix := by
  obtain ⟨before, suffix, he⟩ :=
    candidate.trace.cached_macro_factorization eU eV eW entry hm
  exact ⟨before, suffix, candidate.expands.trans he⟩

/-- Extend by every primitive step and every macro that can still fit its
minimum cost of two. The numerical guard avoids constructing impossible macros;
the entire expanded length and altitude filter remains unchanged. -/
def extensions {K H : ℕ} {D : State U V W} (k : ℕ)
    (candidate : Candidate eU eV eW K H D) : List (Candidate eU eV eW K H D) :=
  (((primitiveSuccessors eU eV eW candidate.finish).map Step.primitive ++
      (if (candidate.path eU eV eW).length + 2 ≤ k then
        macroSteps eU eV eW candidate.finish K H else [])).map
      (candidate.extend eU eV eW)).filter
    fun next => decide ((next.path eU eV eW).length ≤ k ∧ (next.path eU eV eW).altitude ≤ H)

/-- The minimum-cost prefilter gives exactly the original extension list,
including order, duplicate entries, full native paths, and annotated traces. It
only avoids constructing macros that the unchanged full bounds filter rejects. -/
theorem extensions_eq_unpruned {K H : ℕ} {D : State U V W} (k : ℕ)
    (candidate : Candidate eU eV eW K H D) :
    extensions eU eV eW k candidate =
      ((availableSteps eU eV eW candidate.finish K H).map
        (candidate.extend eU eV eW)).filter
          (fun next => decide ((next.path eU eV eW).length ≤ k ∧
            (next.path eU eV eW).altitude ≤ H)) := by
  by_cases hfit : (candidate.path eU eV eW).length + 2 ≤ k
  · simp only [extensions, if_pos hfit, availableSteps]
  · have hrejected :
        ((macroSteps eU eV eW candidate.finish K H).map
          (candidate.extend eU eV eW)).filter
            (fun next => decide ((next.path eU eV eW).length ≤ k ∧
              (next.path eU eV eW).altitude ≤ H)) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro next hnext
      obtain ⟨hmapped, hbounds⟩ := List.mem_filter.mp hnext
      obtain ⟨step, hstep, rfl⟩ := List.mem_map.mp hmapped
      obtain ⟨key, hkey, rfl⟩ :=
        (mem_macroSteps_iff eU eV eW candidate.finish K H step).mp hstep
      have hlength := (of_decide_eq_true hbounds).1
      rw [Candidate.extend_length, Step.path] at hlength
      simp only [CachedMacro.ofRecognized] at hlength
      have hcost :=
        (compileRecognized eU eV eW candidate.finish K H key hkey).length_two_or_three
      rcases hcost with hcost | hcost <;> omega
    simp only [extensions, if_neg hfit, List.append_nil, availableSteps,
      List.map_append, List.filter_append, hrejected, List.append_nil]

/-- Extension membership is exactly an available annotated step and the full
expanded bounds, unchanged by the exact minimum-cost prefilter. -/
theorem mem_extensions_iff {K H : ℕ} {D : State U V W} (k : ℕ)
    (candidate next : Candidate eU eV eW K H D) :
    next ∈ extensions eU eV eW k candidate ↔
      (∃ step ∈ availableSteps eU eV eW candidate.finish K H,
        candidate.extend eU eV eW step = next) ∧
      ((next.path eU eV eW).length ≤ k ∧ (next.path eU eV eW).altitude ≤ H) := by
  rw [extensions_eq_unpruned]
  simp only [List.mem_filter, List.mem_map, decide_eq_true_eq]

/-- Exact-cost-prefiltered weighted enumeration with retained annotated traces.
The generated list is unchanged from the original full expansion and filtering. -/
def boundedCandidates (K H : ℕ) (D : State U V W) : ℕ → List (Candidate eU eV eW K H D)
  | 0 => [Candidate.root eU eV eW K H D]
  | k + 1 =>
      let prior := boundedCandidates K H D k
      prior ++ prior.flatMap (extensions eU eV eW (k + 1))

/-- All generated paths respect full primitive cost and every vertex's ceiling. -/
theorem boundedCandidates_sound {K H : ℕ} {D : State U V W} (hD : D.card ≤ H) (k : ℕ) :
    ∀ candidate ∈ boundedCandidates eU eV eW K H D k,
      (candidate.path eU eV eW).length ≤ k ∧ (candidate.path eU eV eW).altitude ≤ H := by
  induction k with
  | zero =>
      intro candidate hm
      simp only [boundedCandidates, List.mem_singleton] at hm
      subst candidate
      simp only [Candidate.path, Candidate.root]
      rw [MovePath.length.eq_def, MovePath.altitude.eq_def]
      exact ⟨Nat.le_refl _, hD⟩
  | succ k ih =>
      intro candidate hm
      simp only [boundedCandidates, List.mem_append, List.mem_flatMap] at hm
      rcases hm with hm | ⟨prior, _, hext⟩
      · exact ⟨(ih candidate hm).1.trans (Nat.le_succ k), (ih candidate hm).2⟩
      · exact of_decide_eq_true (List.mem_filter.mp hext).2

/-- The zero-edge root is retained at every recursion depth. -/
theorem root_mem_boundedCandidates (K H : ℕ) (D : State U V W) (k : ℕ) :
    Candidate.root eU eV eW K H D ∈ boundedCandidates eU eV eW K H D k := by
  induction k with
  | zero => simp [boundedCandidates]
  | succ k ih => exact List.mem_append_left _ ih

/-- Every bounded intrinsic ambient primitive path has an enumerated endpoint.
The proof retains all primitive coverage independently of macro availability. -/
theorem boundedCandidates_complete {K H : ℕ} {D E : State U V W}
    (path : MovePath (AllModeMove (U := U) (V := V) (W := W)) D E) (k : ℕ)
    (hlength : path.length ≤ k) (haltitude : path.altitude ≤ H) :
    ∃ candidate ∈ boundedCandidates eU eV eW K H D k, candidate.finish = E := by
  induction path generalizing k with
  | singleton =>
      exact ⟨Candidate.root eU eV eW K H D,
        root_mem_boundedCandidates eU eV eW K H D k, rfl⟩
  | snoc priorPath edge ih =>
      cases k with
      | zero => simp only [MovePath.length] at hlength; omega
      | succ k =>
          have hpLen : priorPath.length ≤ k := by
            simp only [MovePath.length] at hlength
            omega
          have hpAlt : priorPath.altitude ≤ H := by
            simp only [MovePath.altitude, Nat.max_le] at haltitude
            exact haltitude.1
          obtain ⟨prior, hm, he⟩ := ih k hpLen hpAlt
          cases he
          obtain ⟨next, hn, he⟩ := primitiveSuccessors_complete eU eV eW edge
          cases he
          let step : Step eU eV eW K H prior.finish := .primitive next
          let extended := prior.extend eU eV eW step
          have hroot : D.card ≤ H :=
            (FiniteWeightedBoundedSearch.MovePath.start_card_le_altitude
              (priorPath.snoc edge)).trans haltitude
          have hp := boundedCandidates_sound eU eV eW hroot k prior hm
          have hnAlt : next.finish.card ≤ H := by
            simp only [MovePath.altitude, Nat.max_le] at haltitude
            exact haltitude.2
          have hlen : (extended.path eU eV eW).length ≤ k + 1 := by
            rw [Candidate.extend_length]
            simpa only [step, Step.path, one_length] using
              Nat.add_le_add_right hp.1 1
          have halt : (extended.path eU eV eW).altitude ≤ H := by
            simp only [extended, Candidate.path, Candidate.extend,
              step, Step.path, trans_one_altitude]
            exact Nat.max_le.mpr ⟨hp.2, hnAlt⟩
          refine ⟨extended, ?_, rfl⟩
          apply List.mem_append_right
          apply List.mem_flatMap.mpr
          refine ⟨prior, hm, List.mem_filter.mpr ⟨?_, decide_eq_true ⟨hlen, halt⟩⟩⟩
          apply List.mem_map.mpr
          refine ⟨step, ?_, rfl⟩
          apply List.mem_append_left
          exact List.mem_map.mpr ⟨next, hn, rfl⟩

/-- Compare endpoint cardinality first. On equal cardinalities, a trace with an
actual macro is preferred to a macro-free trace; all other ties retain the left
candidate. This secondary criterion does not change the search domain or objective;
no secondary trace-optimality theorem is asserted. -/
def prefer {K H : ℕ} {D : State U V W}
    (left right : Candidate eU eV eW K H D) : Candidate eU eV eW K H D :=
  if right.finish.card < left.finish.card ∨
      (right.finish.card = left.finish.card ∧
        (left.trace.macros eU eV eW).isEmpty = true ∧
        (right.trace.macros eU eV eW).isEmpty = false) then right else left

/-- Deterministically select an attaining candidate without erasing its trace. -/
def chooseBest {K H : ℕ} {D : State U V W}
    (fallback : Candidate eU eV eW K H D) (candidates : List (Candidate eU eV eW K H D)) :
    Candidate eU eV eW K H D := candidates.foldl (prefer eU eV eW) fallback

private theorem prefer_le_left {K H : ℕ} {D : State U V W}
    (left right : Candidate eU eV eW K H D) :
    (prefer eU eV eW left right).finish.card ≤ left.finish.card := by
  unfold prefer
  split
  · next h => exact h.elim Nat.le_of_lt (fun he => he.1.le)
  · exact Nat.le_refl _

private theorem prefer_le_right {K H : ℕ} {D : State U V W}
    (left right : Candidate eU eV eW K H D) :
    (prefer eU eV eW left right).finish.card ≤ right.finish.card := by
  unfold prefer
  split
  · exact Nat.le_refl _
  · next h => exact Nat.le_of_not_gt (fun hlt => h (Or.inl hlt))

private theorem chooseBest_le_fallback {K H : ℕ} {D : State U V W}
    (fallback : Candidate eU eV eW K H D) (xs : List (Candidate eU eV eW K H D)) :
    (chooseBest eU eV eW fallback xs).finish.card ≤ fallback.finish.card := by
  induction xs generalizing fallback with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
      exact (ih (prefer eU eV eW fallback head)).trans (prefer_le_left eU eV eW fallback head)

private theorem chooseBest_le_mem {K H : ℕ} {D : State U V W}
    (fallback candidate : Candidate eU eV eW K H D)
    {xs : List (Candidate eU eV eW K H D)} (hm : candidate ∈ xs) :
    (chooseBest eU eV eW fallback xs).finish.card ≤ candidate.finish.card := by
  induction xs generalizing fallback with
  | nil => simp at hm
  | cons head tail ih =>
      rcases List.mem_cons.mp hm with he | hm
      · subst candidate
        exact (chooseBest_le_fallback eU eV eW (prefer eU eV eW fallback head) tail).trans
          (prefer_le_right eU eV eW fallback head)
      · exact ih (prefer eU eV eW fallback head) hm

private theorem chooseBest_property {K H : ℕ} {D : State U V W}
    {P : Candidate eU eV eW K H D → Prop}
    (fallback : Candidate eU eV eW K H D) (xs : List (Candidate eU eV eW K H D))
    (hf : P fallback) (hx : ∀ candidate ∈ xs, P candidate) :
    P (chooseBest eU eV eW fallback xs) := by
  induction xs generalizing fallback with
  | nil => exact hf
  | cons head tail ih =>
      apply ih (prefer eU eV eW fallback head)
      · unfold prefer
        split
        · exact hx head List.mem_cons_self
        · exact hf
      · intro candidate hm
        exact hx candidate (List.mem_cons_of_mem head hm)

/-- Certified minimum endpoint and its provenance-preserving native trace. -/
structure Result (D : State U V W) (k H : ℕ) extends Candidate eU eV eW k H D where
  length_le : (toCandidate.path eU eV eW).length ≤ k
  altitude_le : (toCandidate.path eU eV eW).altitude ≤ H
  optimal : ∀ {E : State U V W}
    (competitor : MovePath (AllModeMove (U := U) (V := V) (W := W)) D E),
    competitor.length ≤ k → competitor.altitude ≤ H → finish.card ≤ E.card

/-- The returned path is exactly the expansion of the selected annotated trace. -/
abbrev Result.path {D : State U V W} {k H : ℕ} (result : Result eU eV eW D k H) :=
  result.toCandidate.path eU eV eW

/-- The returned cached native path is exactly the retained trace expansion. -/
theorem Result.path_eq_trace {D : State U V W} {k H : ℕ}
    (result : Result eU eV eW D k H) :
    result.path eU eV eW = result.trace.path eU eV eW := result.expands

/-- Each selected macro remains a literal segment of the returned cached
native path, with its original recognized endpoints and compiler path. -/
theorem Result.macro_factorization {D : State U V W} {k H : ℕ}
    (result : Result eU eV eW D k H)
    (entry : Σ X, RecognizedMacro eU eV eW X)
    (hm : entry ∈ result.trace.macros eU eV eW) :
    ∃ (before : MovePath (AllModeMove (U := U) (V := V) (W := W)) D entry.1)
      (suffix : MovePath (AllModeMove (U := U) (V := V) (W := W)) entry.2.finish result.finish),
      result.path eU eV eW = (before.trans entry.2.path).trans suffix := by
  obtain ⟨before, suffix, he⟩ := result.trace.macro_factorization eU eV eW entry hm
  exact ⟨before, suffix, (result.path_eq_trace eU eV eW).trans he⟩

/-- Oracle-free exhaustive macro-assisted optimization against every bounded
ambient native competitor. No provider, basis, or optimizer is supplied by callers. -/
def optimize (D : State U V W) (k H : ℕ) (hD : D.card ≤ H) : Result eU eV eW D k H := by
  let xs := boundedCandidates eU eV eW k H D k
  let fallback := Candidate.root eU eV eW k H D
  let best := chooseBest eU eV eW fallback xs
  have hb : (best.path eU eV eW).length ≤ k ∧ (best.path eU eV eW).altitude ≤ H := by
    apply chooseBest_property eU eV eW
      (P := fun candidate => (candidate.path eU eV eW).length ≤ k ∧
        (candidate.path eU eV eW).altitude ≤ H) fallback xs
    · simp only [fallback, Candidate.path, Candidate.root]
      rw [MovePath.length.eq_def, MovePath.altitude.eq_def]
      exact ⟨Nat.zero_le _, hD⟩
    · exact boundedCandidates_sound eU eV eW hD k
  refine { toCandidate := best, length_le := hb.1, altitude_le := hb.2, optimal := ?_ }
  intro E competitor hlen halt
  obtain ⟨candidate, hm, he⟩ := boundedCandidates_complete eU eV eW competitor k hlen halt
  have hbest := chooseBest_le_mem eU eV eW fallback candidate hm
  simpa only [he] using hbest

private theorem vertex_card_le_altitude {α : Type*} {R : Finset α → Finset α → Prop}
    {D E : Finset α} (path : MovePath R D E) (X : Finset α) (hm : X ∈ path.vertices) :
    X.card ≤ path.altitude := by
  induction path with
  | singleton =>
      simp only [MovePath.vertices, List.mem_singleton] at hm
      subst X
      simp only [MovePath.altitude, Nat.le_refl]
  | snoc prior edge ih =>
      simp only [MovePath.vertices, List.mem_append, List.mem_singleton] at hm
      simp only [MovePath.altitude]
      rcases hm with hm | he
      · exact (ih hm).trans (Nat.le_max_left _ _)
      · subst X
        exact Nat.le_max_right _ _

/-- Every vertex of the returned expanded native path, including all internal
macro vertices, lies below the declared ceiling. -/
theorem Result.vertex_card_le {D : State U V W} {k H : ℕ}
    (result : Result eU eV eW D k H) (X : State U V W)
    (hm : X ∈ (result.path eU eV eW).vertices) : X.card ≤ H :=
  (vertex_card_le_altitude (result.path eU eV eW) X hm).trans result.altitude_le

/-- The returned endpoint preserves the original ambient tensor evaluation. -/
theorem Result.preserves_evaluation {D : State U V W} {k H : ℕ}
    (result : Result eU eV eW D k H) : stateEvaluation result.finish = stateEvaluation D := by
  apply (normalized_stateEvaluation_eq_iff eU eV eW result.finish D).mp
  exact NormalizedBinaryAllModeMove.allModeMovePath_preserves_evaluation
    (normalizePath eU eV eW (result.path eU eV eW))

/-- The selected endpoint never has more terms than the admissible root. -/
theorem Result.card_le_original {D : State U V W} {k H : ℕ}
    (result : Result eU eV eW D k H) (hD : D.card ≤ H) : result.finish.card ≤ D.card := by
  apply result.optimal (.singleton D)
  · simp only [MovePath.length, Nat.zero_le]
  · simpa only [MovePath.altitude] using hD

/-- The optimum is a bounded-graph optimum, exactly matching the independently
proved primitive-only optimum under the same full frames and bounds. -/
theorem optimize_card_eq_primitive (D : State U V W) (k H : ℕ) (hD : D.card ≤ H) :
    (optimize eU eV eW D k H hD).finish.card =
      (BinaryAmbientBoundedSearch.optimize eU eV eW D k H hD).finish.card := by
  apply Nat.le_antisymm
  · exact (optimize eU eV eW D k H hD).optimal
      (BinaryAmbientBoundedSearch.optimize eU eV eW D k H hD).path
      (BinaryAmbientBoundedSearch.optimize eU eV eW D k H hD).length_le
      (BinaryAmbientBoundedSearch.optimize eU eV eW D k H hD).altitude_le
  · exact (BinaryAmbientBoundedSearch.optimize eU eV eW D k H hD).optimal
      ((optimize eU eV eW D k H hD).path eU eV eW)
      (optimize eU eV eW D k H hD).length_le
      (optimize eU eV eW D k H hD).altitude_le

#check @CachedMacro.certified
#check @admittedMacros_keys
#check @exists_mem_admittedMacros_iff
#check @Trace.cachedMacros_results
#check @Trace.cached_macro_factorization
#check @Candidate.cached_macro_factorization
#print axioms CachedMacro.certified
#print axioms admittedMacros_keys
#print axioms exists_mem_admittedMacros_iff
#print axioms Trace.cachedMacros_results
#print axioms Trace.cached_macro_factorization
#print axioms Candidate.cached_macro_factorization
#check @ambientTermList_nodup
#check @ambientTermList_toFinset
#check @exists_mem_primitiveSuccessors_iff
#check @Step.positive
#check @macroSteps_complete
#check @mem_macroSteps_iff
#check @Candidate.root_path
#check @Candidate.extend_length
#check @mem_extensions_iff
#check @boundedCandidates_sound
#check @root_mem_boundedCandidates
#check @Result.path_eq_trace
#check @Result.macro_factorization
#check @Result.card_le_original
#check @optimize_card_eq_primitive
#check @mem_endpointSets_iff
#check @mem_rawKeyList_iff
#check @mem_recognizedKeyList_iff
#check @primitiveSuccessors_complete
#check @Trace.macro_certificates
#check @boundedCandidates_complete
#check @Trace.macro_factorization
#check @extensions_eq_unpruned
#print axioms extensions_eq_unpruned
#check @Result.vertex_card_le
#check @Result.preserves_evaluation
#check @optimize
#print axioms Result.macro_factorization
#print axioms Trace.macro_factorization
#print axioms Result.vertex_card_le
#print axioms Result.preserves_evaluation
#print axioms optimize
#print axioms optimize_card_eq_primitive
#print axioms Trace.macro_certificates

end BilinearComplexity.BinaryMacroBoundedSearch
