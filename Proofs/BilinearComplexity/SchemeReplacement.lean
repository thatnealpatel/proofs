import BilinearComplexity.Scheme
import Mathlib.Data.Finset.Sort

set_option autoImplicit false

namespace BilinearComplexity
namespace Scheme
namespace Replacement

variable {k : Type*} {a b c r : ℕ}

/-- The tensor sum of the terms selected from an ordered scheme by a finite slot set. -/
def selectedTensor [CommSemiring k] (S : Scheme k a b c r) (I : Finset (Fin r)) :
    Tensor k a b c :=
  ∑ i ∈ I, (S.term i).eval

/-- The tensor sum of an ordered insertion list. -/
def insertedTensor [CommSemiring k] (L : List (TriadData k a b c)) : Tensor k a b c :=
  (L.map fun t => t.eval).sum

/-- A local replacement consists only of removed slots, ordered inserted terms, and the
exact local tensor equality needed to replay it. -/
structure Certificate [CommSemiring k] (S : Scheme k a b c r) where
  /-- Original slots removed by this replacement. -/
  removed : Finset (Fin r)
  /-- New terms, in their operational insertion order. -/
  inserted : List (TriadData k a b c)
  /-- Equality of the removed and inserted local tensors. -/
  local_eq : selectedTensor S removed = insertedTensor inserted

namespace Certificate

variable [CommSemiring k] {S : Scheme k a b c r}

/-- The complement of the removed slots has the expected cardinality. -/
theorem card_survivors (C : Certificate S) :
    C.removedᶜ.card = r - C.removed.card := by
  simpa only [Fintype.card_fin] using Finset.card_compl C.removed

/-- The canonical increasing enumeration of the surviving original slots. -/
def survivorOrderEquiv (C : Certificate S) :
    Fin (r - C.removed.card) ≃o {i : Fin r // i ∈ C.removedᶜ} :=
  Finset.orderIsoOfFin C.removedᶜ C.card_survivors

/-- The original slot occupying a canonical surviving output position. -/
def survivor (C : Certificate S) (i : Fin (r - C.removed.card)) : Fin r :=
  C.survivorOrderEquiv i

/-- Canonical survivor enumeration is strictly increasing in the original slot order. -/
theorem survivor_strictMono (C : Certificate S) : StrictMono C.survivor := by
  intro i j hij
  exact (C.survivorOrderEquiv.lt_iff_lt).mpr hij

/-- Canonical survivor enumeration is injective as a map back to original slots. -/
theorem survivor_injective (C : Certificate S) : Function.Injective C.survivor := by
  intro i j hij
  apply C.survivorOrderEquiv.injective
  exact Subtype.ext hij

/-- Every canonically enumerated survivor is outside the removed set. -/
theorem survivor_not_mem (C : Certificate S) (i : Fin (r - C.removed.card)) :
    C.survivor i ∉ C.removed := by
  have hcompl : C.survivor i ∈ C.removedᶜ := (C.survivorOrderEquiv i).property
  simpa only [Finset.mem_compl] using hcompl

/-- Every original slot outside the removed set occurs in the survivor enumeration. -/
theorem survivor_surjective (C : Certificate S) (s : Fin r) (hs : s ∉ C.removed) :
    ∃ i, C.survivor i = s := by
  let q : {i : Fin r // i ∈ C.removedᶜ} :=
    ⟨s, by simpa only [Finset.mem_compl] using hs⟩
  exact ⟨C.survivorOrderEquiv.symm q,
    congrArg Subtype.val (C.survivorOrderEquiv.apply_symm_apply q)⟩

/-- Certified embedding of surviving original positions into the initial output segment. -/
def survivorSlot (C : Certificate S) :
    Fin (r - C.removed.card) ↪ Fin (r - C.removed.card + C.inserted.length) :=
  Fin.castAddEmb C.inserted.length

/-- Certified embedding of insertion-list positions into the final output segment. -/
def insertedSlot (C : Certificate S) :
    Fin C.inserted.length ↪ Fin (r - C.removed.card + C.inserted.length) :=
  Fin.natAddEmb (r - C.removed.card)

/-- Survivor and insertion output segments are disjoint. -/
theorem survivorSlot_ne_insertedSlot (C : Certificate S)
    (i : Fin (r - C.removed.card)) (j : Fin C.inserted.length) :
    C.survivorSlot i ≠ C.insertedSlot j := by
  change Fin.castAdd C.inserted.length i ≠ Fin.natAdd (r - C.removed.card) j
  intro h
  have hval := congrArg Fin.val h
  change i.val = r - C.removed.card + j.val at hval
  omega

/-- Insertion and survivor output segments are disjoint in the reverse direction. -/
theorem insertedSlot_ne_survivorSlot (C : Certificate S)
    (j : Fin C.inserted.length) (i : Fin (r - C.removed.card)) :
    C.insertedSlot j ≠ C.survivorSlot i :=
  (C.survivorSlot_ne_insertedSlot i j).symm

/-- Deterministic replacement output: increasing original survivors, then list-order insertions. -/
def output (C : Certificate S) :
    Scheme k a b c (r - C.removed.card + C.inserted.length) :=
  ⟨Fin.addCases (fun i => S.term (C.survivor i)) (fun j => C.inserted.get j)⟩

/-- A survivor output slot contains exactly its canonically enumerated old term. -/
@[simp] theorem output_survivor_term (C : Certificate S)
    (i : Fin (r - C.removed.card)) :
    (C.output.term (C.survivorSlot i)) = S.term (C.survivor i) := by
  simp only [output, survivorSlot, Fin.castAddEmb_apply, Fin.addCases_left]

/-- An insertion output slot contains exactly its list-position term. -/
@[simp] theorem output_inserted_term (C : Certificate S) (j : Fin C.inserted.length) :
    (C.output.term (C.insertedSlot j)) = C.inserted.get j := by
  simp only [output, insertedSlot, Fin.natAddEmb_apply, Fin.addCases_right]

/-- A finite sum over insertion positions is the list tensor sum. -/
theorem sum_inserted_get (L : List (TriadData k a b c)) :
    (∑ j : Fin L.length, (L.get j).eval) = insertedTensor L := by
  rw [← List.sum_ofFn]
  change (List.ofFn fun j : Fin L.length => (L.get j).eval).sum =
    (L.map fun t => t.eval).sum
  rw [List.ofFn_comp', List.ofFn_get]

/-- The output tensor splits into the surviving-old and inserted-list tensor sums. -/
theorem sumTensor_output (C : Certificate S) :
    C.output.sumTensor = selectedTensor S C.removedᶜ + insertedTensor C.inserted := by
  have hsurvivors :
      (∑ i : Fin (r - C.removed.card), (S.term (C.survivor i)).eval) =
        selectedTensor S C.removedᶜ := by
    rw [selectedTensor, Finset.sum_subtype C.removedᶜ (fun _ => Iff.rfl)]
    rw [← Equiv.sum_comp C.survivorOrderEquiv.toEquiv]
    rfl
  rw [show C.output.sumTensor = ∑ q, (C.output.term q).eval by
    funext x y z
    simp only [sumTensor, Finset.sum_apply]]
  rw [Fin.sum_univ_add]
  simp only [output, Fin.addCases_left, Fin.addCases_right]
  rw [hsurvivors, sum_inserted_get C.inserted]

/-- Every certified local replacement preserves the represented tensor exactly. -/
theorem sumTensor_eq (C : Certificate S) : C.output.sumTensor = S.sumTensor := by
  rw [C.sumTensor_output, ← C.local_eq]
  calc
    selectedTensor S C.removedᶜ + selectedTensor S C.removed =
        ∑ s, (S.term s).eval := by
      simpa only [selectedTensor] using
        (Finset.sum_compl_add_sum C.removed (fun s => (S.term s).eval))
    _ = S.sumTensor := by
      funext x y z
      simp only [sumTensor, Finset.sum_apply]

/-- The deterministic output rank parameter: survivors plus ordered insertions. -/
def resultRank (C : Certificate S) : ℕ :=
  r - C.removed.card + C.inserted.length

/-- Replacement rank bookkeeping is exactly `r - |I| + length(L)`. -/
@[simp] theorem resultRank_eq (C : Certificate S) :
    C.resultRank = r - C.removed.card + C.inserted.length := rfl

/-- Every certified replacement proves a rank-at-most bound at its result rank. -/
theorem rankLE_resultRank (C : Certificate S) :
    RankLE S.sumTensor C.resultRank := by
  rw [← C.sumTensor_eq]
  exact C.output.rankLE_sumTensor

/-- Conditions under which inserted evaluated terms retain the stronger `Scheme.Valid` data. -/
structure InsertedValid (C : Certificate S) : Prop where
  /-- Every inserted rank-one tensor is nonzero. -/
  nonzero : ∀ j : Fin C.inserted.length, (C.inserted.get j).eval ≠ 0
  /-- Distinct insertion positions have distinct evaluated tensors. -/
  injective : Function.Injective (fun j : Fin C.inserted.length => (C.inserted.get j).eval)
  /-- No inserted evaluated tensor equals an unaffected old evaluated tensor. -/
  cross : ∀ s : Fin r, s ∉ C.removed → ∀ j : Fin C.inserted.length,
    (S.term s).eval ≠ (C.inserted.get j).eval

/-- A certified replacement preserving all nonzero/distinctness side conditions preserves validity. -/
theorem valid_output {T : Tensor k a b c} (C : Certificate S)
    (hS : S.Valid T) (hinserted : C.InsertedValid) : C.output.Valid T := by
  refine ⟨C.sumTensor_eq.trans hS.1, ?_, ?_⟩
  · intro q
    refine Fin.addCases (motive := fun q => C.output.TermNonzero q) ?_ ?_ q
    · intro i
      change (C.output.term (Fin.castAdd C.inserted.length i)).eval ≠ 0
      simp only [output, Fin.addCases_left]
      exact hS.2.1 (C.survivor i)
    · intro j
      change (C.output.term (Fin.natAdd (r - C.removed.card) j)).eval ≠ 0
      simp only [output, Fin.addCases_right]
      exact hinserted.nonzero j
  · intro q₁
    refine Fin.addCases (motive := fun q₁ => ∀ q₂,
      (C.output.term q₁).eval = (C.output.term q₂).eval → q₁ = q₂) ?_ ?_ q₁
    · intro i q₂
      refine Fin.addCases (motive := fun q₂ =>
        (C.output.term (Fin.castAdd C.inserted.length i)).eval =
          (C.output.term q₂).eval → Fin.castAdd C.inserted.length i = q₂) ?_ ?_ q₂
      · intro j hij
        simp only [output, Fin.addCases_left] at hij
        have hold : C.survivor i = C.survivor j := hS.2.2 hij
        have hsubtype : C.survivorOrderEquiv i = C.survivorOrderEquiv j :=
          Subtype.ext hold
        have hindex : i = j := C.survivorOrderEquiv.injective hsubtype
        subst j
        rfl
      · intro j hij
        simp only [output, Fin.addCases_left, Fin.addCases_right] at hij
        exact (hinserted.cross (C.survivor i) (C.survivor_not_mem i) j hij).elim
    · intro i q₂
      refine Fin.addCases (motive := fun q₂ =>
        (C.output.term (Fin.natAdd (r - C.removed.card) i)).eval =
          (C.output.term q₂).eval → Fin.natAdd (r - C.removed.card) i = q₂) ?_ ?_ q₂
      · intro j hij
        simp only [output, Fin.addCases_right, Fin.addCases_left] at hij
        exact (hinserted.cross (C.survivor j) (C.survivor_not_mem j) i hij.symm).elim
      · intro j hij
        simp only [output, Fin.addCases_right] at hij
        have hindex : i = j := hinserted.injective hij
        subst j
        rfl

/-- The preimage of a later removed set along the previous survivor-slot embedding. -/
def transportedSurvivors (C : Certificate S)
    (J : Finset (Fin (r - C.removed.card + C.inserted.length))) :
    Finset (Fin (r - C.removed.card)) :=
  Finset.univ.filter fun i => C.survivorSlot i ∈ J

/-- The preimage of a later removed set along the previous insertion-slot embedding. -/
def transportedInsertions (C : Certificate S)
    (J : Finset (Fin (r - C.removed.card + C.inserted.length))) :
    Finset (Fin C.inserted.length) :=
  Finset.univ.filter fun j => C.insertedSlot j ∈ J

/-- Every later removed set is exactly reconstructed from its transported survivor and insertion
preimages. -/
theorem removed_eq_image_transported (C : Certificate S)
    (J : Finset (Fin (r - C.removed.card + C.inserted.length))) :
    J = Finset.image C.survivorSlot (C.transportedSurvivors J) ∪
      Finset.image C.insertedSlot (C.transportedInsertions J) := by
  ext q
  refine Fin.addCases ?_ ?_ q
  · intro i
    constructor
    · intro hi
      apply Finset.mem_union_left
      have hi' : C.survivorSlot i ∈ J := by
        simpa only [survivorSlot, Fin.castAddEmb_apply] using hi
      exact Finset.mem_image.mpr ⟨i, by simp only [transportedSurvivors,
        Finset.mem_filter, Finset.mem_univ, true_and, hi'], rfl⟩
    · intro hi
      rcases Finset.mem_union.mp hi with hi | hi
      · rcases Finset.mem_image.mp hi with ⟨j, hj, hji⟩
        have hjJ : C.survivorSlot j ∈ J := by
          simpa only [transportedSurvivors, Finset.mem_filter, Finset.mem_univ,
            true_and] using hj
        rw [hji] at hjJ
        exact hjJ
      · rcases Finset.mem_image.mp hi with ⟨j, _hj, hji⟩
        exact (C.insertedSlot_ne_survivorSlot j i hji).elim
  · intro i
    constructor
    · intro hi
      apply Finset.mem_union_right
      have hi' : C.insertedSlot i ∈ J := by
        simpa only [insertedSlot, Fin.natAddEmb_apply] using hi
      exact Finset.mem_image.mpr ⟨i, by simp only [transportedInsertions,
        Finset.mem_filter, Finset.mem_univ, true_and, hi'], rfl⟩
    · intro hi
      rcases Finset.mem_union.mp hi with hi | hi
      · rcases Finset.mem_image.mp hi with ⟨j, _hj, hji⟩
        exact (C.survivorSlot_ne_insertedSlot j i hji).elim
      · rcases Finset.mem_image.mp hi with ⟨j, hj, hji⟩
        have hjJ : C.insertedSlot j ∈ J := by
          simpa only [transportedInsertions, Finset.mem_filter, Finset.mem_univ,
            true_and] using hj
        rw [hji] at hjJ
        exact hjJ

/-- Selected tensor sums split across disjoint slot sets. -/
theorem selectedTensor_union (R : Scheme k a b c r) (I J : Finset (Fin r))
    (hdisjoint : Disjoint I J) :
    selectedTensor R (I ∪ J) = selectedTensor R I + selectedTensor R J := by
  simp only [selectedTensor]
  rw [Finset.sum_union hdisjoint]

/-- Insertion tensor sums split according to list concatenation. -/
theorem insertedTensor_append (L M : List (TriadData k a b c)) :
    insertedTensor (L ++ M) = insertedTensor L + insertedTensor M := by
  simp only [insertedTensor, List.map_append, List.sum_append]

/-- Selecting survivor output slots recovers the corresponding original-slot tensor sum. -/
theorem selectedTensor_image_survivor (C : Certificate S)
    (I : Finset (Fin (r - C.removed.card))) :
    selectedTensor C.output (Finset.image C.survivorSlot I) =
      selectedTensor S (Finset.image C.survivor I) := by
  simp only [selectedTensor]
  rw [Finset.sum_image C.survivorSlot.injective.injOn]
  rw [Finset.sum_image C.survivor_injective.injOn]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [C.output_survivor_term]

/-- Selecting insertion output slots recovers the corresponding insertion-list tensor sum. -/
theorem selectedTensor_image_inserted (C : Certificate S)
    (I : Finset (Fin C.inserted.length)) :
    selectedTensor C.output (Finset.image C.insertedSlot I) =
      ∑ j ∈ I, (C.inserted.get j).eval := by
  simp only [selectedTensor]
  rw [Finset.sum_image C.insertedSlot.injective.injOn]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [C.output_inserted_term]

/-- Images of the survivor and insertion embeddings are disjoint for arbitrary source subsets. -/
theorem disjoint_image_slots (C : Certificate S)
    (I : Finset (Fin (r - C.removed.card))) (J : Finset (Fin C.inserted.length)) :
    Disjoint (Finset.image C.survivorSlot I) (Finset.image C.insertedSlot J) := by
  rw [Finset.disjoint_left]
  intro q hqI hqJ
  rcases Finset.mem_image.mp hqI with ⟨i, _hi, hiq⟩
  rcases Finset.mem_image.mp hqJ with ⟨j, _hj, hjq⟩
  exact C.survivorSlot_ne_insertedSlot i j (hiq.trans hjq.symm)

/-- Explicit lineage data for a later removed-slot set through both canonical output
embeddings of the preceding replacement. -/
structure RemovalTransport (C : Certificate S)
    (J : Finset (Fin (r - C.removed.card + C.inserted.length))) where
  /-- Later-removed slots that came from surviving original terms. -/
  survivorPreimage : Finset (Fin (r - C.removed.card))
  /-- Later-removed slots that came from the preceding insertion list. -/
  insertionPreimage : Finset (Fin C.inserted.length)
  /-- The supplied lineage sets reconstruct the later removed slots exactly. -/
  reconstruct : J = Finset.image C.survivorSlot survivorPreimage ∪
    Finset.image C.insertedSlot insertionPreimage

/-- The canonical explicit lineage witness obtained by taking both embedding preimages. -/
def canonicalRemovalTransport (C : Certificate S)
    (J : Finset (Fin (r - C.removed.card + C.inserted.length))) :
    C.RemovalTransport J where
  survivorPreimage := C.transportedSurvivors J
  insertionPreimage := C.transportedInsertions J
  reconstruct := C.removed_eq_image_transported J

/-- The canonical transport witness, retained as a short replay-facing name. -/
def removalTransport (C : Certificate S)
    (J : Finset (Fin (r - C.removed.card + C.inserted.length))) :
    C.RemovalTransport J :=
  C.canonicalRemovalTransport J

/-- Original slots removed by the direct operational composite. -/
def compositeRemoved (C₁ : Certificate S) (C₂ : Certificate C₁.output)
    (transport : C₁.RemovalTransport C₂.removed) : Finset (Fin r) :=
  C₁.removed ∪ Finset.image C₁.survivor transport.survivorPreimage

/-- The original and later-removed survivor parts of a composite are disjoint. -/
theorem disjoint_removed_image_survivor (C₁ : Certificate S)
    (C₂ : Certificate C₁.output) (transport : C₁.RemovalTransport C₂.removed) :
    Disjoint C₁.removed (Finset.image C₁.survivor transport.survivorPreimage) := by
  rw [Finset.disjoint_left]
  intro s hs himage
  rcases Finset.mem_image.mp himage with ⟨i, _hi, his⟩
  rw [← his] at hs
  exact C₁.survivor_not_mem i hs

/-- The surviving preceding insertion positions have the expected cardinality. -/
theorem card_surviving_prior_insertions (C₁ : Certificate S)
    (C₂ : Certificate C₁.output) (transport : C₁.RemovalTransport C₂.removed) :
    transport.insertionPreimageᶜ.card =
      C₁.inserted.length - transport.insertionPreimage.card := by
  simpa only [Fintype.card_fin] using Finset.card_compl transport.insertionPreimage

/-- Increasing enumeration of preceding insertion positions not removed by the later replacement. -/
def priorInsertionSurvivorOrderEquiv (C₁ : Certificate S)
    (C₂ : Certificate C₁.output) (transport : C₁.RemovalTransport C₂.removed) :
    Fin (C₁.inserted.length - transport.insertionPreimage.card) ≃o
      {j : Fin C₁.inserted.length // j ∈ transport.insertionPreimageᶜ} :=
  Finset.orderIsoOfFin transport.insertionPreimageᶜ
    (C₁.card_surviving_prior_insertions C₂ transport)

/-- The surviving preceding insertions, retained in their original list order. -/
def survivingPriorInsertions (C₁ : Certificate S) (C₂ : Certificate C₁.output)
    (transport : C₁.RemovalTransport C₂.removed) : List (TriadData k a b c) :=
  List.ofFn fun i : Fin (C₁.inserted.length - transport.insertionPreimage.card) =>
    C₁.inserted.get (C₁.priorInsertionSurvivorOrderEquiv C₂ transport i)

/-- Direct-composite insertion order: surviving preceding insertions, then later insertions. -/
def compositeInserted (C₁ : Certificate S) (C₂ : Certificate C₁.output)
    (transport : C₁.RemovalTransport C₂.removed) : List (TriadData k a b c) :=
  C₁.survivingPriorInsertions C₂ transport ++ C₂.inserted

/-- The direct composite removes exactly the first removals plus transported later survivor
removals. -/
theorem card_compositeRemoved (C₁ : Certificate S) (C₂ : Certificate C₁.output)
    (transport : C₁.RemovalTransport C₂.removed) :
    (C₁.compositeRemoved C₂ transport).card =
      C₁.removed.card + transport.survivorPreimage.card := by
  rw [compositeRemoved]
  rw [Finset.card_union_of_disjoint (C₁.disjoint_removed_image_survivor C₂ transport)]
  rw [Finset.card_image_of_injective _ C₁.survivor_injective]

/-- The direct-composite insertion length records both ordered insertion blocks. -/
@[simp] theorem length_compositeInserted (C₁ : Certificate S)
    (C₂ : Certificate C₁.output) (transport : C₁.RemovalTransport C₂.removed) :
    (C₁.compositeInserted C₂ transport).length =
      C₁.inserted.length - transport.insertionPreimage.card + C₂.inserted.length := by
  simp only [compositeInserted, survivingPriorInsertions, List.length_append,
    List.length_ofFn]

/-- The preceding insertion tensor splits into list-order survivors and later-removed
insertion positions. -/
theorem insertedTensor_eq_surviving_add_removed (C₁ : Certificate S)
    (C₂ : Certificate C₁.output) (transport : C₁.RemovalTransport C₂.removed) :
    insertedTensor C₁.inserted = insertedTensor (C₁.survivingPriorInsertions C₂ transport) +
      ∑ j ∈ transport.insertionPreimage, (C₁.inserted.get j).eval := by
  have hsurviving :
      insertedTensor (C₁.survivingPriorInsertions C₂ transport) =
        ∑ j ∈ transport.insertionPreimageᶜ, (C₁.inserted.get j).eval := by
    simp only [insertedTensor, survivingPriorInsertions]
    rw [← List.ofFn_comp']
    rw [List.sum_ofFn]
    rw [Finset.sum_subtype transport.insertionPreimageᶜ (fun _ => Iff.rfl)]
    rw [← Equiv.sum_comp (C₁.priorInsertionSurvivorOrderEquiv C₂ transport).toEquiv]
    rfl
  rw [hsurviving]
  calc
    insertedTensor C₁.inserted = ∑ j, (C₁.inserted.get j).eval :=
      (sum_inserted_get C₁.inserted).symm
    _ = (∑ j ∈ transport.insertionPreimageᶜ, (C₁.inserted.get j).eval) +
        ∑ j ∈ transport.insertionPreimage, (C₁.inserted.get j).eval :=
      (Finset.sum_compl_add_sum transport.insertionPreimage
        (fun j => (C₁.inserted.get j).eval)).symm

/-- The supplied later-removal lineage decomposes its local tensor into original-survivor and
preceding-insertion parts. -/
theorem selectedTensor_later_eq_parts (C₁ : Certificate S)
    (C₂ : Certificate C₁.output) (transport : C₁.RemovalTransport C₂.removed) :
    selectedTensor C₁.output C₂.removed =
      selectedTensor S (Finset.image C₁.survivor transport.survivorPreimage) +
        ∑ j ∈ transport.insertionPreimage, (C₁.inserted.get j).eval := by
  calc
    selectedTensor C₁.output C₂.removed =
        selectedTensor C₁.output
          (Finset.image C₁.survivorSlot transport.survivorPreimage ∪
            Finset.image C₁.insertedSlot transport.insertionPreimage) :=
      congrArg (selectedTensor C₁.output) transport.reconstruct
    _ = selectedTensor C₁.output
          (Finset.image C₁.survivorSlot transport.survivorPreimage) +
        selectedTensor C₁.output
          (Finset.image C₁.insertedSlot transport.insertionPreimage) :=
      selectedTensor_union C₁.output _ _
        (C₁.disjoint_image_slots transport.survivorPreimage transport.insertionPreimage)
    _ = selectedTensor S (Finset.image C₁.survivor transport.survivorPreimage) +
        ∑ j ∈ transport.insertionPreimage, (C₁.inserted.get j).eval := by
      rw [C₁.selectedTensor_image_survivor, C₁.selectedTensor_image_inserted]

/-- The exact direct composite certificate, with operational order consisting of unaffected
original slots, surviving preceding insertions, and then later insertions. -/
def composite (C₁ : Certificate S) (C₂ : Certificate C₁.output)
    (transport : C₁.RemovalTransport C₂.removed) : Certificate S where
  removed := C₁.compositeRemoved C₂ transport
  inserted := C₁.compositeInserted C₂ transport
  local_eq := by
    rw [compositeRemoved]
    rw [selectedTensor_union S _ _ (C₁.disjoint_removed_image_survivor C₂ transport)]
    rw [C₁.local_eq]
    rw [C₁.insertedTensor_eq_surviving_add_removed C₂ transport]
    rw [compositeInserted, insertedTensor_append]
    have hlater : insertedTensor C₂.inserted =
        selectedTensor S (Finset.image C₁.survivor transport.survivorPreimage) +
          ∑ j ∈ transport.insertionPreimage, (C₁.inserted.get j).eval :=
      C₂.local_eq.symm.trans (C₁.selectedTensor_later_eq_parts C₂ transport)
    rw [hlater]
    ac_rfl

/-- The supplied lineage decomposes the cardinality of the later removed-slot set. -/
theorem card_later_removed_eq_parts (C₁ : Certificate S)
    (C₂ : Certificate C₁.output) (transport : C₁.RemovalTransport C₂.removed) :
    C₂.removed.card = transport.survivorPreimage.card +
      transport.insertionPreimage.card := by
  calc
    C₂.removed.card =
        (Finset.image C₁.survivorSlot transport.survivorPreimage ∪
          Finset.image C₁.insertedSlot transport.insertionPreimage).card :=
      congrArg Finset.card transport.reconstruct
    _ = (Finset.image C₁.survivorSlot transport.survivorPreimage).card +
        (Finset.image C₁.insertedSlot transport.insertionPreimage).card :=
      Finset.card_union_of_disjoint
        (C₁.disjoint_image_slots transport.survivorPreimage transport.insertionPreimage)
    _ = transport.survivorPreimage.card + transport.insertionPreimage.card := by
      rw [Finset.card_image_of_injective _ C₁.survivorSlot.injective,
        Finset.card_image_of_injective _ C₁.insertedSlot.injective]

/-- The direct composite and the sequential endpoint have the same rank parameter. -/
theorem composite_resultRank_eq_later_resultRank (C₁ : Certificate S)
    (C₂ : Certificate C₁.output) (transport : C₁.RemovalTransport C₂.removed) :
    (C₁.composite C₂ transport).resultRank = C₂.resultRank := by
  have hremoved : C₁.removed.card ≤ r := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ C₁.removed
  have hsurvivors : transport.survivorPreimage.card ≤ r - C₁.removed.card := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ transport.survivorPreimage
  have hinsertions : transport.insertionPreimage.card ≤ C₁.inserted.length := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ transport.insertionPreimage
  rw [resultRank_eq, resultRank_eq]
  simp only [composite, card_compositeRemoved, length_compositeInserted]
  rw [C₁.card_later_removed_eq_parts C₂ transport]
  omega

/-- A concatenation of two strictly increasing finite sequences is strictly increasing when
all entries of the first sequence precede all entries of the second. -/
theorem strictMono_addCases {α : Type*} [Preorder α] {m n : ℕ}
    (f : Fin m → α) (g : Fin n → α) (hf : StrictMono f) (hg : StrictMono g)
    (hcross : ∀ i j, f i < g j) : StrictMono (Fin.addCases f g) := by
  let F : Fin (m + n) → α := Fin.addCases f g
  intro i j hij
  change F i < F j
  refine Fin.addCases (motive := fun i => ∀ j, i < j → F i < F j) ?_ ?_ i j hij
  · intro x
    refine Fin.addCases ?_ ?_
    · intro y hxy
      simp only [F, Fin.addCases_left]
      apply hf
      change x.val < y.val at hxy
      exact hxy
    · intro y _hxy
      simp only [F, Fin.addCases_left, Fin.addCases_right]
      exact hcross x y
  · intro x
    refine Fin.addCases ?_ ?_
    · intro y hxy
      change m + x.val < y.val at hxy
      omega
    · intro y hxy
      simp only [F, Fin.addCases_right]
      apply hg
      change m + x.val < m + y.val at hxy
      omega

/-- The unaffected-original block of the direct composite has the expected length. -/
theorem composite_survivor_count_eq (C₁ : Certificate S) (C₂ : Certificate C₁.output)
    (transport : C₁.RemovalTransport C₂.removed) :
    r - (C₁.composite C₂ transport).removed.card =
      r - C₁.removed.card - transport.survivorPreimage.card := by
  have hremoved : C₁.removed.card ≤ r := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ C₁.removed
  have hsurvivors : transport.survivorPreimage.card ≤ r - C₁.removed.card := by
    simpa only [Fintype.card_fin] using
      Finset.card_le_univ transport.survivorPreimage
  simp only [composite]
  rw [C₁.card_compositeRemoved C₂ transport]
  omega

/-- Direct-composite unaffected originals are the surviving first-output original positions,
in their canonical increasing order. -/
theorem composite_survivor_cast_eq (C₁ : Certificate S) (C₂ : Certificate C₁.output)
    (transport : C₁.RemovalTransport C₂.removed)
    (i : Fin (r - C₁.removed.card - transport.survivorPreimage.card)) :
    (C₁.composite C₂ transport).survivor
        (Fin.cast (C₁.composite_survivor_count_eq C₂ transport).symm i) =
      C₁.survivor
        (transport.survivorPreimageᶜ.orderEmbOfFin
          (by simpa only [Fintype.card_fin] using
            Finset.card_compl transport.survivorPreimage) i) := by
  have hcount := C₁.composite_survivor_count_eq C₂ transport
  have hpreimageCard : transport.survivorPreimageᶜ.card =
      r - C₁.removed.card - transport.survivorPreimage.card := by
    simpa only [Fintype.card_fin] using Finset.card_compl transport.survivorPreimage
  let f : Fin (r - (C₁.composite C₂ transport).removed.card) → Fin r :=
    fun q => C₁.survivor
      (transport.survivorPreimageᶜ.orderEmbOfFin hpreimageCard (Fin.cast hcount q))
  have hfmem : ∀ q, f q ∉ (C₁.composite C₂ transport).removed := by
    intro q
    simp only [composite, compositeRemoved, Finset.mem_union, Finset.mem_image, not_or]
    constructor
    · exact C₁.survivor_not_mem _
    · intro himage
      rcases himage with ⟨j, hj, heq⟩
      have hindex : j = transport.survivorPreimageᶜ.orderEmbOfFin hpreimageCard
          (Fin.cast hcount q) := C₁.survivor_injective heq
      subst j
      have hcompl := Finset.orderEmbOfFin_mem transport.survivorPreimageᶜ
        hpreimageCard (Fin.cast hcount q)
      exact (Finset.mem_compl.mp hcompl) hj
  have hfmono : StrictMono f := by
    exact C₁.survivor_strictMono.comp
      ((transport.survivorPreimageᶜ.orderEmbOfFin hpreimageCard).strictMono.comp
        (Fin.cast_strictMono hcount))
  have hfun : f = (C₁.composite C₂ transport).survivor := by
    apply Finset.orderEmbOfFin_unique (C₁.composite C₂ transport).card_survivors
    · intro q
      simpa only [Finset.mem_compl] using hfmem q
    · exact hfmono
  rw [← hfun]
  apply congrArg C₁.survivor
  apply Fin.ext
  rfl

/-- The later survivor block splits into surviving first originals followed by surviving first
insertions. -/
theorem later_survivor_count_eq (C₁ : Certificate S) (C₂ : Certificate C₁.output)
    (transport : C₁.RemovalTransport C₂.removed) :
    r - C₁.removed.card + C₁.inserted.length - C₂.removed.card =
      (r - C₁.removed.card - transport.survivorPreimage.card) +
        (C₁.inserted.length - transport.insertionPreimage.card) := by
  have hsurvivors : transport.survivorPreimage.card ≤ r - C₁.removed.card := by
    simpa only [Fintype.card_fin] using
      Finset.card_le_univ transport.survivorPreimage
  have hinsertions : transport.insertionPreimage.card ≤ C₁.inserted.length := by
    simpa only [Fintype.card_fin] using
      Finset.card_le_univ transport.insertionPreimage
  rw [C₁.card_later_removed_eq_parts C₂ transport]
  omega

/-- After the canonical count cast, later survivors enumerate surviving first originals and
then surviving first insertions. -/
theorem later_survivor_cast_eq_addCases (C₁ : Certificate S)
    (C₂ : Certificate C₁.output) (transport : C₁.RemovalTransport C₂.removed) :
    (fun q : Fin ((r - C₁.removed.card - transport.survivorPreimage.card) +
        (C₁.inserted.length - transport.insertionPreimage.card)) =>
      C₂.survivor (Fin.cast (C₁.later_survivor_count_eq C₂ transport).symm q)) =
      Fin.addCases
        (fun i => C₁.survivorSlot
          (transport.survivorPreimageᶜ.orderEmbOfFin
            (by simpa only [Fintype.card_fin] using
              Finset.card_compl transport.survivorPreimage) i))
        (fun j => C₁.insertedSlot
          (C₁.priorInsertionSurvivorOrderEquiv C₂ transport j)) := by
  have hsurvivorCard : transport.survivorPreimageᶜ.card =
      r - C₁.removed.card - transport.survivorPreimage.card := by
    simpa only [Fintype.card_fin] using
      Finset.card_compl transport.survivorPreimage
  have hcount := C₁.later_survivor_count_eq C₂ transport
  let left : Fin (r - C₁.removed.card - transport.survivorPreimage.card) →
      Fin (r - C₁.removed.card + C₁.inserted.length) :=
    fun i => C₁.survivorSlot
      (transport.survivorPreimageᶜ.orderEmbOfFin hsurvivorCard i)
  let right : Fin (C₁.inserted.length - transport.insertionPreimage.card) →
      Fin (r - C₁.removed.card + C₁.inserted.length) :=
    fun j => C₁.insertedSlot (C₁.priorInsertionSurvivorOrderEquiv C₂ transport j)
  let g : Fin ((r - C₁.removed.card - transport.survivorPreimage.card) +
      (C₁.inserted.length - transport.insertionPreimage.card)) →
      Fin (r - C₁.removed.card + C₁.inserted.length) := Fin.addCases left right
  have hgmem : ∀ q, g q ∉ C₂.removed := by
    intro q
    rw [transport.reconstruct]
    refine Fin.addCases (motive := fun q => g q ∉
      Finset.image C₁.survivorSlot transport.survivorPreimage ∪
        Finset.image C₁.insertedSlot transport.insertionPreimage) ?_ ?_ q
    · intro i
      simp only [g, Fin.addCases_left, Finset.mem_union, not_or]
      constructor
      · intro himage
        rcases Finset.mem_image.mp himage with ⟨j, hj, hji⟩
        have hindex : j = transport.survivorPreimageᶜ.orderEmbOfFin
            hsurvivorCard i := C₁.survivorSlot.injective hji
        subst j
        have hcompl := Finset.orderEmbOfFin_mem transport.survivorPreimageᶜ
          hsurvivorCard i
        exact (Finset.mem_compl.mp hcompl) hj
      · intro himage
        rcases Finset.mem_image.mp himage with ⟨j, _hj, hji⟩
        exact C₁.survivorSlot_ne_insertedSlot
          (transport.survivorPreimageᶜ.orderEmbOfFin hsurvivorCard i) j hji.symm
    · intro i
      simp only [g, Fin.addCases_right, Finset.mem_union, not_or]
      constructor
      · intro himage
        rcases Finset.mem_image.mp himage with ⟨j, _hj, hji⟩
        exact C₁.survivorSlot_ne_insertedSlot j
          (C₁.priorInsertionSurvivorOrderEquiv C₂ transport i) hji
      · intro himage
        rcases Finset.mem_image.mp himage with ⟨j, hj, hji⟩
        have hindex : j = C₁.priorInsertionSurvivorOrderEquiv C₂ transport i :=
          C₁.insertedSlot.injective hji
        subst j
        have hcompl := (C₁.priorInsertionSurvivorOrderEquiv C₂ transport i).property
        exact (Finset.mem_compl.mp hcompl) hj
  have hleftMono : StrictMono left := by
    exact (Fin.strictMono_castAdd C₁.inserted.length).comp
      ((transport.survivorPreimageᶜ.orderEmbOfFin hsurvivorCard).strictMono)
  have hrightMono : StrictMono right := by
    exact (Fin.strictMono_natAdd (r - C₁.removed.card)).comp
      (C₁.priorInsertionSurvivorOrderEquiv C₂ transport).strictMono
  have hcross : ∀ i j, left i < right j := by
    intro i j
    change (transport.survivorPreimageᶜ.orderEmbOfFin hsurvivorCard i).val <
      r - C₁.removed.card +
        (C₁.priorInsertionSurvivorOrderEquiv C₂ transport j).val
    have hi := (transport.survivorPreimageᶜ.orderEmbOfFin hsurvivorCard i).isLt
    omega
  have hgmono : StrictMono g :=
    strictMono_addCases left right hleftMono hrightMono hcross
  let f : Fin (r - C₁.removed.card + C₁.inserted.length - C₂.removed.card) →
      Fin (r - C₁.removed.card + C₁.inserted.length) :=
    fun q => g (Fin.cast hcount q)
  have hfmono : StrictMono f := hgmono.comp (Fin.cast_strictMono hcount)
  have hfmem : ∀ q, f q ∉ C₂.removed := by
    intro q
    exact hgmem (Fin.cast hcount q)
  have hfun : f = C₂.survivor := by
    apply Finset.orderEmbOfFin_unique C₂.card_survivors
    · intro q
      simpa only [Finset.mem_compl] using hfmem q
    · exact hfmono
  funext q
  change C₂.survivor (Fin.cast hcount.symm q) = g q
  rw [← hfun]
  apply congrArg g
  apply Fin.ext
  rfl

/-- A direct-composite insertion slot in the first block reads the corresponding surviving
first insertion. -/
theorem compositeInserted_get_prior (C₁ : Certificate S)
    (C₂ : Certificate C₁.output) (transport : C₁.RemovalTransport C₂.removed)
    (i : Fin (C₁.inserted.length - transport.insertionPreimage.card)) :
    (C₁.compositeInserted C₂ transport).get
        (Fin.cast (C₁.length_compositeInserted C₂ transport).symm
          (Fin.castAdd C₂.inserted.length i)) =
      C₁.inserted.get (C₁.priorInsertionSurvivorOrderEquiv C₂ transport i) := by
  rw [List.get_eq_getElem]
  simp only [compositeInserted]
  rw [List.getElem_append_left (by
    simp only [survivingPriorInsertions, List.length_ofFn]
    exact i.isLt)]
  simp only [survivingPriorInsertions]
  rw [List.getElem_ofFn]
  apply congrArg C₁.inserted.get
  apply Fin.ext
  rfl

/-- A direct-composite insertion slot in the second block reads the corresponding later
insertion. -/
theorem compositeInserted_get_later (C₁ : Certificate S)
    (C₂ : Certificate C₁.output) (transport : C₁.RemovalTransport C₂.removed)
    (j : Fin C₂.inserted.length) :
    (C₁.compositeInserted C₂ transport).get
        (Fin.cast (C₁.length_compositeInserted C₂ transport).symm
          (Fin.natAdd (C₁.inserted.length - transport.insertionPreimage.card) j)) =
      C₂.inserted.get j := by
  change (C₁.survivingPriorInsertions C₂ transport ++ C₂.inserted).get
      ⟨C₁.inserted.length - transport.insertionPreimage.card + j.val, by
        simp only [survivingPriorInsertions, List.length_append, List.length_ofFn]
        omega⟩ = C₂.inserted.get j
  rw [List.get_eq_getElem]
  rw [List.getElem_append_right (by
    simp only [survivingPriorInsertions, List.length_ofFn]
    omega)]
  rw [List.get_eq_getElem]
  simp only [survivingPriorInsertions, List.length_ofFn, Nat.add_sub_cancel_left]

/-- After the canonical rank cast, every direct-composite output slot contains exactly the
term in the corresponding slot of the sequential endpoint. -/
theorem composite_output_term_cast_eq_later_output_term (C₁ : Certificate S)
    (C₂ : Certificate C₁.output) (transport : C₁.RemovalTransport C₂.removed)
    (q : Fin C₂.resultRank) :
    (C₁.composite C₂ transport).output.term
        (Fin.cast (C₁.composite_resultRank_eq_later_resultRank C₂ transport).symm q) =
      C₂.output.term q := by
  refine Fin.addCases (motive := fun q =>
    (C₁.composite C₂ transport).output.term
        (Fin.cast (C₁.composite_resultRank_eq_later_resultRank C₂ transport).symm q) =
      C₂.output.term q) ?_ ?_ q
  · intro i
    let i' : Fin ((r - C₁.removed.card - transport.survivorPreimage.card) +
        (C₁.inserted.length - transport.insertionPreimage.card)) :=
      Fin.cast (C₁.later_survivor_count_eq C₂ transport) i
    have hi : i = Fin.cast (C₁.later_survivor_count_eq C₂ transport).symm i' := by
      apply Fin.ext
      rfl
    rw [hi]
    refine Fin.addCases (motive := fun u =>
      (C₁.composite C₂ transport).output.term
          (Fin.cast (C₁.composite_resultRank_eq_later_resultRank C₂ transport).symm
            (Fin.castAdd C₂.inserted.length
              (Fin.cast (C₁.later_survivor_count_eq C₂ transport).symm u))) =
        C₂.output.term
          (Fin.castAdd C₂.inserted.length
            (Fin.cast (C₁.later_survivor_count_eq C₂ transport).symm u))) ?_ ?_ i'
    · intro x
      let xDirect : Fin (r - (C₁.composite C₂ transport).removed.card) :=
        Fin.cast (C₁.composite_survivor_count_eq C₂ transport).symm x
      let xLater : Fin (r - C₁.removed.card + C₁.inserted.length - C₂.removed.card) :=
        Fin.cast (C₁.later_survivor_count_eq C₂ transport).symm
          (Fin.castAdd (C₁.inserted.length - transport.insertionPreimage.card) x)
      have hsurvivorCard : transport.survivorPreimageᶜ.card =
          r - C₁.removed.card - transport.survivorPreimage.card := by
        simpa only [Fintype.card_fin] using
          Finset.card_compl transport.survivorPreimage
      let old : Fin (r - C₁.removed.card) :=
        transport.survivorPreimageᶜ.orderEmbOfFin hsurvivorCard x
      have hslot :
          Fin.cast (C₁.composite_resultRank_eq_later_resultRank C₂ transport).symm
              (Fin.castAdd C₂.inserted.length xLater) =
            (C₁.composite C₂ transport).survivorSlot xDirect := by
        apply Fin.ext
        rfl
      have hdirectSurvivor :
          (C₁.composite C₂ transport).survivor xDirect = C₁.survivor old := by
        simpa only [xDirect, old, hsurvivorCard] using
          C₁.composite_survivor_cast_eq C₂ transport x
      have hlaterSurvivor : C₂.survivor xLater = C₁.survivorSlot old := by
        have hfun := congrFun
          (C₁.later_survivor_cast_eq_addCases C₂ transport)
          (Fin.castAdd (C₁.inserted.length - transport.insertionPreimage.card) x)
        simpa only [xLater, old, hsurvivorCard, Fin.addCases_left] using hfun
      have hlaterSlot : Fin.castAdd C₂.inserted.length xLater =
          C₂.survivorSlot xLater := by
        rfl
      calc
        (C₁.composite C₂ transport).output.term
            (Fin.cast (C₁.composite_resultRank_eq_later_resultRank C₂ transport).symm
              (Fin.castAdd C₂.inserted.length xLater)) =
            (C₁.composite C₂ transport).output.term
              ((C₁.composite C₂ transport).survivorSlot xDirect) :=
          congrArg (C₁.composite C₂ transport).output.term hslot
        _ = S.term ((C₁.composite C₂ transport).survivor xDirect) :=
          (C₁.composite C₂ transport).output_survivor_term xDirect
        _ = S.term (C₁.survivor old) := congrArg S.term hdirectSurvivor
        _ = C₁.output.term (C₁.survivorSlot old) :=
          (C₁.output_survivor_term old).symm
        _ = C₁.output.term (C₂.survivor xLater) :=
          congrArg C₁.output.term hlaterSurvivor.symm
        _ = C₂.output.term (C₂.survivorSlot xLater) :=
          (C₂.output_survivor_term xLater).symm
        _ = C₂.output.term (Fin.castAdd C₂.inserted.length xLater) :=
          congrArg C₂.output.term hlaterSlot.symm
    · intro y
      let yDirect : Fin (C₁.composite C₂ transport).inserted.length :=
        Fin.cast (C₁.length_compositeInserted C₂ transport).symm
          (Fin.castAdd C₂.inserted.length y)
      let yLater : Fin
          (r - C₁.removed.card + C₁.inserted.length - C₂.removed.card) :=
        Fin.cast (C₁.later_survivor_count_eq C₂ transport).symm
          (Fin.natAdd
            (r - C₁.removed.card - transport.survivorPreimage.card) y)
      let prior : Fin C₁.inserted.length :=
        C₁.priorInsertionSurvivorOrderEquiv C₂ transport y
      have hslot :
          Fin.cast (C₁.composite_resultRank_eq_later_resultRank C₂ transport).symm
              (Fin.castAdd C₂.inserted.length yLater) =
            (C₁.composite C₂ transport).insertedSlot yDirect := by
        apply Fin.ext
        change
          r - C₁.removed.card - transport.survivorPreimage.card + y.val =
            (r - (C₁.composite C₂ transport).removed.card) + y.val
        rw [C₁.composite_survivor_count_eq C₂ transport]
      have hlaterSurvivor : C₂.survivor yLater = C₁.insertedSlot prior := by
        have hfun := congrFun
          (C₁.later_survivor_cast_eq_addCases C₂ transport)
          (Fin.natAdd
            (r - C₁.removed.card - transport.survivorPreimage.card) y)
        simpa only [yLater, prior, Fin.addCases_right] using hfun
      have hlaterSlot : Fin.castAdd C₂.inserted.length yLater =
          C₂.survivorSlot yLater := by
        rfl
      calc
        (C₁.composite C₂ transport).output.term
            (Fin.cast (C₁.composite_resultRank_eq_later_resultRank C₂ transport).symm
              (Fin.castAdd C₂.inserted.length yLater)) =
            (C₁.composite C₂ transport).output.term
              ((C₁.composite C₂ transport).insertedSlot yDirect) :=
          congrArg (C₁.composite C₂ transport).output.term hslot
        _ = (C₁.composite C₂ transport).inserted.get yDirect :=
          (C₁.composite C₂ transport).output_inserted_term yDirect
        _ = C₁.inserted.get prior :=
          C₁.compositeInserted_get_prior C₂ transport y
        _ = C₁.output.term (C₁.insertedSlot prior) :=
          (C₁.output_inserted_term prior).symm
        _ = C₁.output.term (C₂.survivor yLater) :=
          congrArg C₁.output.term hlaterSurvivor.symm
        _ = C₂.output.term (C₂.survivorSlot yLater) :=
          (C₂.output_survivor_term yLater).symm
        _ = C₂.output.term (Fin.castAdd C₂.inserted.length yLater) :=
          congrArg C₂.output.term hlaterSlot.symm
  · intro j
    let j' : Fin (C₁.composite C₂ transport).inserted.length :=
      Fin.cast (C₁.length_compositeInserted C₂ transport).symm
        (Fin.natAdd (C₁.inserted.length - transport.insertionPreimage.card) j)
    have hslot :
        Fin.cast (C₁.composite_resultRank_eq_later_resultRank C₂ transport).symm
            (Fin.natAdd
              (r - C₁.removed.card + C₁.inserted.length - C₂.removed.card) j) =
          (C₁.composite C₂ transport).insertedSlot j' := by
      apply Fin.ext
      change
        r - C₁.removed.card + C₁.inserted.length - C₂.removed.card + j.val =
          (r - (C₁.composite C₂ transport).removed.card) +
            (C₁.inserted.length - transport.insertionPreimage.card + j.val)
      rw [C₁.composite_survivor_count_eq C₂ transport,
        C₁.later_survivor_count_eq C₂ transport]
      omega
    have hlaterSlot :
        Fin.natAdd
            (r - C₁.removed.card + C₁.inserted.length - C₂.removed.card) j =
          C₂.insertedSlot j := by
      rfl
    calc
      (C₁.composite C₂ transport).output.term
          (Fin.cast (C₁.composite_resultRank_eq_later_resultRank C₂ transport).symm
            (Fin.natAdd
              (r - C₁.removed.card + C₁.inserted.length - C₂.removed.card) j)) =
          (C₁.composite C₂ transport).output.term
            ((C₁.composite C₂ transport).insertedSlot j') :=
        congrArg (C₁.composite C₂ transport).output.term hslot
      _ = (C₁.composite C₂ transport).inserted.get j' :=
        (C₁.composite C₂ transport).output_inserted_term j'
      _ = C₂.inserted.get j := C₁.compositeInserted_get_later C₂ transport j
      _ = C₂.output.term (C₂.insertedSlot j) :=
        (C₂.output_inserted_term j).symm
      _ = C₂.output.term
          (Fin.natAdd
            (r - C₁.removed.card + C₁.inserted.length - C₂.removed.card) j) :=
        congrArg C₂.output.term hlaterSlot.symm

/-- Casting the direct-composite output along the canonical rank equality gives exactly the
sequential endpoint as an ordered scheme. -/
theorem composite_output_cast_eq_later_output (C₁ : Certificate S)
    (C₂ : Certificate C₁.output) (transport : C₁.RemovalTransport C₂.removed) :
    Eq.rec (motive := fun q _ => Scheme k a b c q)
      (C₁.composite C₂ transport).output
      (C₁.composite_resultRank_eq_later_resultRank C₂ transport) = C₂.output := by
  have rec_eq {m n : ℕ} (A : Scheme k a b c m) (h : m = n) :
      Eq.rec (motive := fun q _ => Scheme k a b c q) A h =
        (⟨fun q : Fin n => A.term (Fin.cast h.symm q)⟩ : Scheme k a b c n) := by
    subst n
    rfl
  have hfinCast :
      (⟨fun q : Fin C₂.resultRank =>
        (C₁.composite C₂ transport).output.term
          (Fin.cast
            (C₁.composite_resultRank_eq_later_resultRank C₂ transport).symm q)⟩ :
        Scheme k a b c C₂.resultRank) = C₂.output := by
    apply congrArg (fun f : Fin C₂.resultRank → TriadData k a b c =>
      (⟨f⟩ : Scheme k a b c C₂.resultRank))
    funext q
    exact C₁.composite_output_term_cast_eq_later_output_term C₂ transport q
  exact (rec_eq (C₁.composite C₂ transport).output
    (C₁.composite_resultRank_eq_later_resultRank C₂ transport)).trans hfinCast

/-- Two successive replayable replacements, together with the explicit transport of the later
removed slots through the first output embeddings. -/
structure Composition (C₁ : Certificate S) where
  /-- The later replacement, whose source is the first deterministic output. -/
  later : Certificate C₁.output
  /-- The required survivor/insertion transport of its removed slots. -/
  removalTransport : C₁.RemovalTransport later.removed

namespace Composition

/-- Construct the direct operational composite certificate from a sequential witness. -/
def direct (C₁ : Certificate S) (C : C₁.Composition) : Certificate S :=
  C₁.composite C.later C.removalTransport

/-- The direct composite preserves the original represented tensor by certificate replay. -/
theorem direct_sumTensor_eq (C₁ : Certificate S) (C : C₁.Composition) :
    (C.direct C₁).output.sumTensor = S.sumTensor :=
  (C.direct C₁).sumTensor_eq

/-- The direct composite and the sequential endpoint have the same rank parameter. -/
theorem direct_resultRank_eq (C₁ : Certificate S) (C : C₁.Composition) :
    (C.direct C₁).resultRank = C.later.resultRank :=
  C₁.composite_resultRank_eq_later_resultRank C.later C.removalTransport

/-- Casting a composition's direct output along its rank equality recovers the sequential
endpoint exactly as an ordered scheme. -/
theorem direct_output_cast_eq_later_output (C₁ : Certificate S) (C : C₁.Composition) :
    Eq.rec (motive := fun q _ => Scheme k a b c q)
      (C.direct C₁).output (C.direct_resultRank_eq C₁) = C.later.output :=
  C₁.composite_output_cast_eq_later_output C.later C.removalTransport

/-- Replaying a composed replacement witness preserves the original represented tensor. -/
theorem sumTensor_eq (C₁ : Certificate S) (C : C₁.Composition) :
    C.later.output.sumTensor = S.sumTensor := by
  rw [C.later.sumTensor_eq, C₁.sumTensor_eq]

end Composition

/-- A direct two-certificate composition theorem with explicit later-removal transport. -/
theorem compose_sumTensor_eq (C₁ : Certificate S) (C₂ : Certificate C₁.output)
    (transport : C₁.RemovalTransport C₂.removed) :
    (C₁.composite C₂ transport).output.sumTensor = S.sumTensor :=
  (C₁.composite C₂ transport).sumTensor_eq

end Certificate

/-- An additive triad symmetry pairs a bijection of triads with the corresponding additive
equivalence of evaluated tensors. -/
structure TriadSymmetry (k : Type*) [CommSemiring k]
    (a b c a' b' c' : ℕ) where
  /-- Bijection on stored rank-one factor triples. -/
  termEquiv : TriadData k a b c ≃ TriadData k a' b' c'
  /-- Additive equivalence on represented tensors. -/
  tensorEquiv : Tensor k a b c ≃+ Tensor k a' b' c'
  /-- Evaluation commutes with the paired term/tensor maps. -/
  eval_term : ∀ t, (termEquiv t).eval = tensorEquiv t.eval

namespace TriadSymmetry

variable [CommSemiring k] {a' b' c' : ℕ}

/-- Transport every stored term of a scheme through a triad symmetry. -/
def mapScheme (e : TriadSymmetry k a b c a' b' c') (S : Scheme k a b c r) :
    Scheme k a' b' c' r :=
  ⟨fun s => e.termEquiv (S.term s)⟩

/-- Transport an ordered insertion list through a triad symmetry. -/
def mapInserted (e : TriadSymmetry k a b c a' b' c')
    (L : List (TriadData k a b c)) : List (TriadData k a' b' c') :=
  L.map e.termEquiv

/-- A triad symmetry maps the represented scheme tensor through its additive tensor equivalence. -/
theorem sumTensor_mapScheme (e : TriadSymmetry k a b c a' b' c')
    (S : Scheme k a b c r) :
    (e.mapScheme S).sumTensor = e.tensorEquiv S.sumTensor := by
  rw [show (e.mapScheme S).sumTensor = ∑ s, ((e.mapScheme S).term s).eval by
    funext x y z
    simp only [sumTensor, Finset.sum_apply]]
  rw [show S.sumTensor = ∑ s, (S.term s).eval by
    funext x y z
    simp only [sumTensor, Finset.sum_apply]]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s _hs
  exact e.eval_term (S.term s)

/-- A triad symmetry maps a selected local tensor through its additive tensor equivalence. -/
theorem selectedTensor_mapScheme (e : TriadSymmetry k a b c a' b' c')
    (S : Scheme k a b c r) (I : Finset (Fin r)) :
    selectedTensor (e.mapScheme S) I = e.tensorEquiv (selectedTensor S I) := by
  simp only [selectedTensor, mapScheme]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s _hs
  exact e.eval_term (S.term s)

/-- A triad symmetry maps an insertion-list local tensor through its additive tensor equivalence. -/
theorem insertedTensor_mapInserted (e : TriadSymmetry k a b c a' b' c')
    (L : List (TriadData k a b c)) :
    insertedTensor (e.mapInserted L) = e.tensorEquiv (insertedTensor L) := by
  simp only [insertedTensor, mapInserted]
  rw [map_list_sum]
  apply congrArg List.sum
  simp only [List.map_map]
  apply List.map_congr_left
  intro t ht
  exact e.eval_term t

end TriadSymmetry

namespace Certificate

variable [CommSemiring k] {S : Scheme k a b c r} {a' b' c' : ℕ}

/-- A tensor symmetry transports a replayable local replacement certificate without any search
provenance. -/
def transport (C : Certificate S) (e : TriadSymmetry k a b c a' b' c') :
    Certificate (e.mapScheme S) where
  removed := C.removed
  inserted := e.mapInserted C.inserted
  local_eq := by
    calc
      selectedTensor (e.mapScheme S) C.removed =
          e.tensorEquiv (selectedTensor S C.removed) :=
        e.selectedTensor_mapScheme S C.removed
      _ = e.tensorEquiv (insertedTensor C.inserted) := congrArg e.tensorEquiv C.local_eq
      _ = insertedTensor (e.mapInserted C.inserted) :=
        (e.insertedTensor_mapInserted C.inserted).symm

end Certificate

/-- A concrete one-slot replay over `ZMod 2` certifies tensor preservation without search data. -/
example :
    let S : Scheme (ZMod 2) 1 1 1 2 :=
      ⟨fun s => (fun _ => if s = 0 then 1 else 0,
        fun _ => 1, fun _ => 1)⟩
    let C : Certificate S :=
      { removed := {0}
        inserted := [S.term 0]
        local_eq := by
          simp only [selectedTensor, insertedTensor, Finset.sum_singleton,
            List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] }
    C.output.sumTensor = S.sumTensor := by
  dsimp only
  exact Certificate.sumTensor_eq _

/-- A concrete rank-three composition has nonempty unaffected-original, prior-insertion, and
later-insertion output blocks, so the ordered-composition hypotheses are jointly satisfiable. -/
example :
    let S : Scheme (ZMod 2) 1 1 1 3 :=
      ⟨fun _ => (fun _ => 1, fun _ => 1, fun _ => 1)⟩
    let C₁ : Certificate S :=
      { removed := {2}
        inserted := [S.term 2]
        local_eq := by
          simp only [selectedTensor, insertedTensor, Finset.sum_singleton,
            List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] }
    let C₂ : Certificate C₁.output :=
      { removed := {1}
        inserted := [C₁.output.term 1]
        local_eq := by
          simp only [selectedTensor, insertedTensor, Finset.sum_singleton,
            List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] }
    let transport := C₁.removalTransport C₂.removed
    Eq.rec (motive := fun q _ => Scheme (ZMod 2) 1 1 1 q)
      (C₁.composite C₂ transport).output
      (C₁.composite_resultRank_eq_later_resultRank C₂ transport) = C₂.output := by
  dsimp only
  exact Certificate.composite_output_cast_eq_later_output _ _ _


/-- The concrete rank-three source used to test a rank-changing replacement over `ZMod 2`. -/
abbrev zmod2RankChangeSource : Scheme (ZMod 2) 4 1 1 3 :=
  ⟨![(![1, 0, 0, 0], ![1], ![1]),
      (![0, 1, 0, 0], ![1], ![1]),
      (![0, 0, 1, 0], ![1], ![1])]⟩

/-- The concrete certificate replacing one source tensor by two distinct evaluated tensors. -/
abbrev zmod2RankChangeCertificate : Certificate zmod2RankChangeSource where
  removed := {1}
  inserted := [(![0, 0, 0, 1], ![1], ![1]), (![0, 1, 0, 1], ![1], ![1])]
  local_eq := by
    funext i j l
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      decide

/-- The concrete rank-changing replacement computes rank four and exact survivor-then-insertion
slot order, while all source and inserted evaluated tensors are pairwise distinct. -/
theorem zmod2_rankChange_fixture :
    let old₀ : TriadData (ZMod 2) 4 1 1 := (![1, 0, 0, 0], ![1], ![1])
    let replaced : TriadData (ZMod 2) 4 1 1 := (![0, 1, 0, 0], ![1], ![1])
    let old₂ : TriadData (ZMod 2) 4 1 1 := (![0, 0, 1, 0], ![1], ![1])
    let inserted₀ : TriadData (ZMod 2) 4 1 1 := (![0, 0, 0, 1], ![1], ![1])
    let inserted₁ : TriadData (ZMod 2) 4 1 1 := (![0, 1, 0, 1], ![1], ![1])
    (([old₀, replaced, old₂, inserted₀, inserted₁].map TriadData.eval).Nodup ∧
      zmod2RankChangeSource.term 0 = old₀ ∧
      zmod2RankChangeSource.term 1 = replaced ∧
      zmod2RankChangeSource.term 2 = old₂ ∧
      zmod2RankChangeCertificate.resultRank = 4 ∧
      zmod2RankChangeCertificate.output.term 0 = old₀ ∧
      zmod2RankChangeCertificate.output.term 1 = old₂ ∧
      zmod2RankChangeCertificate.output.term 2 = inserted₀ ∧
      zmod2RankChangeCertificate.output.term 3 = inserted₁) := by
  dsimp only
  let q₀ : Fin (3 - zmod2RankChangeCertificate.removed.card) :=
    ⟨0, by simp⟩
  let q₁ : Fin (3 - zmod2RankChangeCertificate.removed.card) :=
    ⟨1, by simp⟩
  have hmono := zmod2RankChangeCertificate.survivor_strictMono
    (show q₀ < q₁ by change 0 < 1; omega)
  have hnot₀ := zmod2RankChangeCertificate.survivor_not_mem q₀
  have hnot₁ := zmod2RankChangeCertificate.survivor_not_mem q₁
  change zmod2RankChangeCertificate.survivor q₀ ∉ ({1} : Finset (Fin 3)) at hnot₀
  change zmod2RankChangeCertificate.survivor q₁ ∉ ({1} : Finset (Fin 3)) at hnot₁
  simp only [Finset.mem_singleton] at hnot₀ hnot₁
  have hsurvivor₀ : zmod2RankChangeCertificate.survivor q₀ = 0 := by
    apply Fin.ext
    change zmod2RankChangeCertificate.survivor q₀ <
      zmod2RankChangeCertificate.survivor q₁ at hmono
    omega
  have hsurvivor₁ : zmod2RankChangeCertificate.survivor q₁ = 2 := by
    apply Fin.ext
    change zmod2RankChangeCertificate.survivor q₀ <
      zmod2RankChangeCertificate.survivor q₁ at hmono
    omega
  refine ⟨by decide, rfl, rfl, rfl, by decide, ?_, ?_, ?_, ?_⟩
  · have hslot : zmod2RankChangeCertificate.survivorSlot q₀ = (0 : Fin 4) := by
      apply Fin.ext
      rfl
    calc
      zmod2RankChangeCertificate.output.term 0 =
          zmod2RankChangeCertificate.output.term
            (zmod2RankChangeCertificate.survivorSlot q₀) :=
        congrArg zmod2RankChangeCertificate.output.term hslot.symm
      _ = zmod2RankChangeSource.term (zmod2RankChangeCertificate.survivor q₀) :=
        zmod2RankChangeCertificate.output_survivor_term q₀
      _ = (![1, 0, 0, 0], ![1], ![1]) := by rw [hsurvivor₀]; rfl
  · have hslot : zmod2RankChangeCertificate.survivorSlot q₁ = (1 : Fin 4) := by
      apply Fin.ext
      rfl
    calc
      zmod2RankChangeCertificate.output.term 1 =
          zmod2RankChangeCertificate.output.term
            (zmod2RankChangeCertificate.survivorSlot q₁) :=
        congrArg zmod2RankChangeCertificate.output.term hslot.symm
      _ = zmod2RankChangeSource.term (zmod2RankChangeCertificate.survivor q₁) :=
        zmod2RankChangeCertificate.output_survivor_term q₁
      _ = (![0, 0, 1, 0], ![1], ![1]) := by rw [hsurvivor₁]; rfl
  · have hslot : zmod2RankChangeCertificate.insertedSlot (0 : Fin 2) =
        (2 : Fin 4) := by
      apply Fin.ext
      rfl
    calc
      zmod2RankChangeCertificate.output.term 2 =
          zmod2RankChangeCertificate.output.term
            (zmod2RankChangeCertificate.insertedSlot (0 : Fin 2)) :=
        congrArg zmod2RankChangeCertificate.output.term hslot.symm
      _ = zmod2RankChangeCertificate.inserted.get (0 : Fin 2) :=
        zmod2RankChangeCertificate.output_inserted_term (0 : Fin 2)
      _ = (![0, 0, 0, 1], ![1], ![1]) := rfl
  · have hslot : zmod2RankChangeCertificate.insertedSlot (1 : Fin 2) =
        (3 : Fin 4) := by
      apply Fin.ext
      rfl
    calc
      zmod2RankChangeCertificate.output.term 3 =
          zmod2RankChangeCertificate.output.term
            (zmod2RankChangeCertificate.insertedSlot (1 : Fin 2)) :=
        congrArg zmod2RankChangeCertificate.output.term hslot.symm
      _ = zmod2RankChangeCertificate.inserted.get (1 : Fin 2) :=
        zmod2RankChangeCertificate.output_inserted_term (1 : Fin 2)
      _ = (![0, 1, 0, 1], ![1], ![1]) := rfl

/-- The concrete rank-four source used to test the three ordered blocks of composition. -/
abbrev zmod2CompositionSource : Scheme (ZMod 2) 5 1 1 4 :=
  ⟨![(![1, 0, 0, 0, 0], ![1], ![1]),
      (![0, 0, 1, 0, 0], ![1], ![1]),
      (![0, 0, 0, 1, 0], ![1], ![1]),
      (![0, 1, 0, 0, 0], ![1], ![1])]⟩

/-- The first concrete composition certificate replaces the final original by two terms. -/
abbrev zmod2CompositionFirst : Certificate zmod2CompositionSource where
  removed := {3}
  inserted := [(![0, 0, 0, 0, 1], ![1], ![1]), (![0, 1, 0, 0, 1], ![1], ![1])]
  local_eq := by
    funext i j l
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      decide

/-- The later concrete composition certificate removes the first prior insertion and replaces
it by two later terms. -/
abbrev zmod2CompositionLater : Certificate zmod2CompositionFirst.output where
  removed := {3}
  inserted := [(![1, 0, 1, 0, 0], ![1], ![1]), (![1, 0, 1, 0, 1], ![1], ![1])]
  local_eq := by
    rw [selectedTensor, Finset.sum_singleton]
    have hslot : zmod2CompositionFirst.insertedSlot (0 : Fin 2) = (3 : Fin 5) := by
      apply Fin.ext
      rfl
    have hterm : zmod2CompositionFirst.output.term (3 : Fin 5) =
        zmod2CompositionFirst.inserted.get (0 : Fin 2) :=
      (congrArg zmod2CompositionFirst.output.term hslot.symm).trans
        (zmod2CompositionFirst.output_inserted_term (0 : Fin 2))
    calc
      (zmod2CompositionFirst.output.term (3 : Fin 5)).eval =
          (zmod2CompositionFirst.inserted.get (0 : Fin 2)).eval :=
        congrArg TriadData.eval hterm
      _ = insertedTensor
          [(![1, 0, 1, 0, 0], ![1], ![1]), (![1, 0, 1, 0, 1], ![1], ![1])] := by
        funext i j l
        fin_cases i <;> fin_cases j <;> fin_cases l <;>
          decide

/-- The canonical concrete transport of the later removed slot through the first output. -/
abbrev zmod2CompositionTransport :=
  zmod2CompositionFirst.removalTransport zmod2CompositionLater.removed

/-- The concrete direct certificate obtained from the two sequential certificates. -/
abbrev zmod2CompositionDirect :=
  zmod2CompositionFirst.composite zmod2CompositionLater zmod2CompositionTransport

/-- The concrete direct composite has result rank six. -/
theorem zmod2CompositionDirect_resultRank : zmod2CompositionDirect.resultRank = 6 :=
  (zmod2CompositionFirst.composite_resultRank_eq_later_resultRank
    zmod2CompositionLater zmod2CompositionTransport).trans (by decide)

/-- The concrete composition computes all ranks and the exact direct and sequential order
`[unaffected originals] ++ [surviving prior insertion] ++ [later insertions]`, with all ground
evaluated tensors pairwise distinct. -/
theorem zmod2_compositionBlocks_fixture :
    let oldA : TriadData (ZMod 2) 5 1 1 := (![1, 0, 0, 0, 0], ![1], ![1])
    let oldC : TriadData (ZMod 2) 5 1 1 := (![0, 0, 1, 0, 0], ![1], ![1])
    let oldD : TriadData (ZMod 2) 5 1 1 := (![0, 0, 0, 1, 0], ![1], ![1])
    let oldB : TriadData (ZMod 2) 5 1 1 := (![0, 1, 0, 0, 0], ![1], ![1])
    let priorP : TriadData (ZMod 2) 5 1 1 := (![0, 0, 0, 0, 1], ![1], ![1])
    let priorQ : TriadData (ZMod 2) 5 1 1 := (![0, 1, 0, 0, 1], ![1], ![1])
    let laterL : TriadData (ZMod 2) 5 1 1 := (![1, 0, 1, 0, 0], ![1], ![1])
    let laterM : TriadData (ZMod 2) 5 1 1 := (![1, 0, 1, 0, 1], ![1], ![1])
    (([oldA, oldB, oldC, oldD, priorP, priorQ, laterL, laterM].map
          TriadData.eval).Nodup ∧
      zmod2CompositionSource.term 0 = oldA ∧
      zmod2CompositionSource.term 1 = oldC ∧
      zmod2CompositionSource.term 2 = oldD ∧
      zmod2CompositionSource.term 3 = oldB ∧
      zmod2CompositionFirst.resultRank = 5 ∧
      zmod2CompositionLater.resultRank = 6 ∧
      zmod2CompositionDirect.resultRank = 6 ∧
      zmod2CompositionDirect.output.term
        (Fin.cast zmod2CompositionDirect_resultRank.symm 0) = oldA ∧
      zmod2CompositionDirect.output.term
        (Fin.cast zmod2CompositionDirect_resultRank.symm 1) = oldC ∧
      zmod2CompositionDirect.output.term
        (Fin.cast zmod2CompositionDirect_resultRank.symm 2) = oldD ∧
      zmod2CompositionDirect.output.term
        (Fin.cast zmod2CompositionDirect_resultRank.symm 3) = priorQ ∧
      zmod2CompositionDirect.output.term
        (Fin.cast zmod2CompositionDirect_resultRank.symm 4) = laterL ∧
      zmod2CompositionDirect.output.term
        (Fin.cast zmod2CompositionDirect_resultRank.symm 5) = laterM ∧
      zmod2CompositionLater.output.term 0 = oldA ∧
      zmod2CompositionLater.output.term 1 = oldC ∧
      zmod2CompositionLater.output.term 2 = oldD ∧
      zmod2CompositionLater.output.term 3 = priorQ ∧
      zmod2CompositionLater.output.term 4 = laterL ∧
      zmod2CompositionLater.output.term 5 = laterM) := by
  dsimp only
  have htransportSurvivors : zmod2CompositionTransport.survivorPreimage = ∅ := by
    change zmod2CompositionFirst.transportedSurvivors {3} = ∅
    ext i
    simp only [Certificate.transportedSurvivors, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.notMem_empty, iff_false]
    intro hi
    have heq : zmod2CompositionFirst.survivorSlot i = 3 :=
      Finset.mem_singleton.mp hi
    have hval := congrArg Fin.val heq
    change i.val = 3 at hval
    have hibound : i.val < 3 := by
      simpa [zmod2CompositionFirst] using i.isLt
    omega
  have hfirstSurvivorCount : 4 - zmod2CompositionFirst.removed.card = 3 := by
    decide
  have htransportInsertions : zmod2CompositionTransport.insertionPreimage = {0} := by
    change zmod2CompositionFirst.transportedInsertions {3} = {0}
    ext j
    simp only [Certificate.transportedInsertions, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_singleton]
    constructor
    · intro hj
      have hval := congrArg Fin.val hj
      change 4 - zmod2CompositionFirst.removed.card + j.val = 3 at hval
      rw [hfirstSurvivorCount] at hval
      have hjval : j.val = 0 := by omega
      exact Fin.ext hjval
    · intro hj
      have hval := congrArg Fin.val hj
      change j.val = 0 at hval
      apply Fin.ext
      change 4 - zmod2CompositionFirst.removed.card + j.val = 3
      rw [hfirstSurvivorCount]
      omega
  have hdirectRemoved : zmod2CompositionDirect.removed = {3} := by
    change zmod2CompositionFirst.compositeRemoved zmod2CompositionLater
      zmod2CompositionTransport = {3}
    simp only [Certificate.compositeRemoved, htransportSurvivors, Finset.image_empty,
      Finset.union_empty]
  let f₀ : Fin (4 - zmod2CompositionFirst.removed.card) :=
    ⟨0, by simp⟩
  let f₁ : Fin (4 - zmod2CompositionFirst.removed.card) :=
    ⟨1, by simp⟩
  let f₂ : Fin (4 - zmod2CompositionFirst.removed.card) :=
    ⟨2, by simp⟩
  have hfmono₀₁ := zmod2CompositionFirst.survivor_strictMono
    (show f₀ < f₁ by change 0 < 1; omega)
  have hfmono₁₂ := zmod2CompositionFirst.survivor_strictMono
    (show f₁ < f₂ by change 1 < 2; omega)
  have hfnot₀ := zmod2CompositionFirst.survivor_not_mem f₀
  have hfnot₁ := zmod2CompositionFirst.survivor_not_mem f₁
  have hfnot₂ := zmod2CompositionFirst.survivor_not_mem f₂
  change zmod2CompositionFirst.survivor f₀ ∉ ({3} : Finset (Fin 4)) at hfnot₀
  change zmod2CompositionFirst.survivor f₁ ∉ ({3} : Finset (Fin 4)) at hfnot₁
  change zmod2CompositionFirst.survivor f₂ ∉ ({3} : Finset (Fin 4)) at hfnot₂
  simp only [Finset.mem_singleton] at hfnot₀ hfnot₁ hfnot₂
  have hfsurvivor₀ : zmod2CompositionFirst.survivor f₀ = 0 := by
    apply Fin.ext
    omega
  have hfsurvivor₁ : zmod2CompositionFirst.survivor f₁ = 1 := by
    apply Fin.ext
    omega
  have hfsurvivor₂ : zmod2CompositionFirst.survivor f₂ = 2 := by
    apply Fin.ext
    omega
  have hfirstTerm₀ : zmod2CompositionFirst.output.term (0 : Fin 5) =
      zmod2CompositionSource.term 0 := by
    have hslot : zmod2CompositionFirst.survivorSlot f₀ = (0 : Fin 5) := by
      apply Fin.ext
      rfl
    calc
      zmod2CompositionFirst.output.term 0 =
          zmod2CompositionFirst.output.term (zmod2CompositionFirst.survivorSlot f₀) :=
        congrArg zmod2CompositionFirst.output.term hslot.symm
      _ = zmod2CompositionSource.term (zmod2CompositionFirst.survivor f₀) :=
        zmod2CompositionFirst.output_survivor_term f₀
      _ = zmod2CompositionSource.term 0 := congrArg zmod2CompositionSource.term hfsurvivor₀
  have hfirstTerm₁ : zmod2CompositionFirst.output.term (1 : Fin 5) =
      zmod2CompositionSource.term 1 := by
    have hslot : zmod2CompositionFirst.survivorSlot f₁ = (1 : Fin 5) := by
      apply Fin.ext
      rfl
    calc
      zmod2CompositionFirst.output.term 1 =
          zmod2CompositionFirst.output.term (zmod2CompositionFirst.survivorSlot f₁) :=
        congrArg zmod2CompositionFirst.output.term hslot.symm
      _ = zmod2CompositionSource.term (zmod2CompositionFirst.survivor f₁) :=
        zmod2CompositionFirst.output_survivor_term f₁
      _ = zmod2CompositionSource.term 1 := congrArg zmod2CompositionSource.term hfsurvivor₁
  have hfirstTerm₂ : zmod2CompositionFirst.output.term (2 : Fin 5) =
      zmod2CompositionSource.term 2 := by
    have hslot : zmod2CompositionFirst.survivorSlot f₂ = (2 : Fin 5) := by
      apply Fin.ext
      rfl
    calc
      zmod2CompositionFirst.output.term 2 =
          zmod2CompositionFirst.output.term (zmod2CompositionFirst.survivorSlot f₂) :=
        congrArg zmod2CompositionFirst.output.term hslot.symm
      _ = zmod2CompositionSource.term (zmod2CompositionFirst.survivor f₂) :=
        zmod2CompositionFirst.output_survivor_term f₂
      _ = zmod2CompositionSource.term 2 := congrArg zmod2CompositionSource.term hfsurvivor₂
  have hfirstTerm₄ : zmod2CompositionFirst.output.term (4 : Fin 5) =
      (![0, 1, 0, 0, 1], ![1], ![1]) := by
    have hslot : zmod2CompositionFirst.insertedSlot (1 : Fin 2) = (4 : Fin 5) := by
      apply Fin.ext
      rfl
    calc
      zmod2CompositionFirst.output.term 4 =
          zmod2CompositionFirst.output.term
            (zmod2CompositionFirst.insertedSlot (1 : Fin 2)) :=
        congrArg zmod2CompositionFirst.output.term hslot.symm
      _ = zmod2CompositionFirst.inserted.get (1 : Fin 2) :=
        zmod2CompositionFirst.output_inserted_term (1 : Fin 2)
      _ = (![0, 1, 0, 0, 1], ![1], ![1]) := rfl
  let l₀ : Fin (5 - zmod2CompositionLater.removed.card) :=
    ⟨0, by simp⟩
  let l₁ : Fin (5 - zmod2CompositionLater.removed.card) :=
    ⟨1, by simp⟩
  let l₂ : Fin (5 - zmod2CompositionLater.removed.card) :=
    ⟨2, by simp⟩
  let l₃ : Fin (5 - zmod2CompositionLater.removed.card) :=
    ⟨3, by simp⟩
  have hlmono₀₁ := zmod2CompositionLater.survivor_strictMono
    (show l₀ < l₁ by change 0 < 1; omega)
  have hlmono₁₂ := zmod2CompositionLater.survivor_strictMono
    (show l₁ < l₂ by change 1 < 2; omega)
  have hlmono₂₃ := zmod2CompositionLater.survivor_strictMono
    (show l₂ < l₃ by change 2 < 3; omega)
  have hlnot₀ := zmod2CompositionLater.survivor_not_mem l₀
  have hlnot₁ := zmod2CompositionLater.survivor_not_mem l₁
  have hlnot₂ := zmod2CompositionLater.survivor_not_mem l₂
  have hlnot₃ := zmod2CompositionLater.survivor_not_mem l₃
  change zmod2CompositionLater.survivor l₀ ∉ ({3} : Finset (Fin 5)) at hlnot₀
  change zmod2CompositionLater.survivor l₁ ∉ ({3} : Finset (Fin 5)) at hlnot₁
  change zmod2CompositionLater.survivor l₂ ∉ ({3} : Finset (Fin 5)) at hlnot₂
  change zmod2CompositionLater.survivor l₃ ∉ ({3} : Finset (Fin 5)) at hlnot₃
  have hlvalnot₀ : (zmod2CompositionLater.survivor l₀).val ≠ 3 := by
    intro heq
    apply hlnot₀
    exact Finset.mem_singleton.mpr (Fin.ext heq)
  have hlvalnot₁ : (zmod2CompositionLater.survivor l₁).val ≠ 3 := by
    intro heq
    apply hlnot₁
    exact Finset.mem_singleton.mpr (Fin.ext heq)
  have hlvalnot₂ : (zmod2CompositionLater.survivor l₂).val ≠ 3 := by
    intro heq
    apply hlnot₂
    exact Finset.mem_singleton.mpr (Fin.ext heq)
  have hlvalnot₃ : (zmod2CompositionLater.survivor l₃).val ≠ 3 := by
    intro heq
    apply hlnot₃
    exact Finset.mem_singleton.mpr (Fin.ext heq)
  change (zmod2CompositionLater.survivor l₀).val <
    (zmod2CompositionLater.survivor l₁).val at hlmono₀₁
  change (zmod2CompositionLater.survivor l₁).val <
    (zmod2CompositionLater.survivor l₂).val at hlmono₁₂
  change (zmod2CompositionLater.survivor l₂).val <
    (zmod2CompositionLater.survivor l₃).val at hlmono₂₃
  have hlbound₀ : (zmod2CompositionLater.survivor l₀).val < 5 := by
    simpa [zmod2CompositionFirst] using (zmod2CompositionLater.survivor l₀).isLt
  have hlbound₁ : (zmod2CompositionLater.survivor l₁).val < 5 := by
    simpa [zmod2CompositionFirst] using (zmod2CompositionLater.survivor l₁).isLt
  have hlbound₂ : (zmod2CompositionLater.survivor l₂).val < 5 := by
    simpa [zmod2CompositionFirst] using (zmod2CompositionLater.survivor l₂).isLt
  have hlbound₃ : (zmod2CompositionLater.survivor l₃).val < 5 := by
    simpa [zmod2CompositionFirst] using (zmod2CompositionLater.survivor l₃).isLt
  have hlsurvivor₀ : zmod2CompositionLater.survivor l₀ = 0 := by
    apply Fin.ext
    change (zmod2CompositionLater.survivor l₀).val = 0
    omega
  have hlsurvivor₁ : zmod2CompositionLater.survivor l₁ = 1 := by
    apply Fin.ext
    change (zmod2CompositionLater.survivor l₁).val = 1
    omega
  have hlsurvivor₂ : zmod2CompositionLater.survivor l₂ = 2 := by
    apply Fin.ext
    change (zmod2CompositionLater.survivor l₂).val = 2
    omega
  have hlsurvivor₃ : zmod2CompositionLater.survivor l₃ = 4 := by
    apply Fin.ext
    change (zmod2CompositionLater.survivor l₃).val = 4
    omega
  let d₀ : Fin (4 - zmod2CompositionDirect.removed.card) :=
    ⟨0, by rw [hdirectRemoved]; decide⟩
  let d₁ : Fin (4 - zmod2CompositionDirect.removed.card) :=
    ⟨1, by rw [hdirectRemoved]; decide⟩
  let d₂ : Fin (4 - zmod2CompositionDirect.removed.card) :=
    ⟨2, by rw [hdirectRemoved]; decide⟩
  have hdmono₀₁ := zmod2CompositionDirect.survivor_strictMono
    (show d₀ < d₁ by change 0 < 1; omega)
  have hdmono₁₂ := zmod2CompositionDirect.survivor_strictMono
    (show d₁ < d₂ by change 1 < 2; omega)
  have hdnot₀ := zmod2CompositionDirect.survivor_not_mem d₀
  have hdnot₁ := zmod2CompositionDirect.survivor_not_mem d₁
  have hdnot₂ := zmod2CompositionDirect.survivor_not_mem d₂
  rw [hdirectRemoved] at hdnot₀ hdnot₁ hdnot₂
  simp only [Finset.mem_singleton] at hdnot₀ hdnot₁ hdnot₂
  have hdsurvivor₀ : zmod2CompositionDirect.survivor d₀ = 0 := by
    apply Fin.ext
    omega
  have hdsurvivor₁ : zmod2CompositionDirect.survivor d₁ = 1 := by
    apply Fin.ext
    omega
  have hdsurvivor₂ : zmod2CompositionDirect.survivor d₂ = 2 := by
    apply Fin.ext
    omega
  let p₀ : Fin (zmod2CompositionFirst.inserted.length -
      zmod2CompositionTransport.insertionPreimage.card) :=
    ⟨0, by rw [htransportInsertions]; decide⟩
  let prior := zmod2CompositionFirst.priorInsertionSurvivorOrderEquiv
    zmod2CompositionLater zmod2CompositionTransport p₀
  have hpriorMem := prior.property
  have hpriorNe : (prior : Fin 2) ≠ 0 := by
    intro hzero
    have hnot := Finset.mem_compl.mp hpriorMem
    apply hnot
    rw [hzero, htransportInsertions]
    exact Finset.mem_singleton_self 0
  have hprior : (prior : Fin 2) = 1 := by
    have hpriorNeVal : (prior : Fin 2).val ≠ 0 := by
      intro heq
      apply hpriorNe
      exact Fin.ext heq
    have hpriorBound : (prior : Fin 2).val < 2 := (prior : Fin 2).isLt
    have hpriorVal : (prior : Fin 2).val = 1 := by omega
    exact Fin.ext hpriorVal
  let directPrior : Fin zmod2CompositionDirect.inserted.length :=
    Fin.cast (zmod2CompositionFirst.length_compositeInserted zmod2CompositionLater
      zmod2CompositionTransport).symm
      (Fin.castAdd zmod2CompositionLater.inserted.length p₀)
  have hdirectPriorGet : zmod2CompositionDirect.inserted.get directPrior =
      zmod2CompositionFirst.inserted.get prior := by
    exact zmod2CompositionFirst.compositeInserted_get_prior zmod2CompositionLater
      zmod2CompositionTransport p₀
  let directLater₀ : Fin zmod2CompositionDirect.inserted.length :=
    Fin.cast (zmod2CompositionFirst.length_compositeInserted zmod2CompositionLater
      zmod2CompositionTransport).symm
      (Fin.natAdd (zmod2CompositionFirst.inserted.length -
        zmod2CompositionTransport.insertionPreimage.card) (0 : Fin 2))
  let directLater₁ : Fin zmod2CompositionDirect.inserted.length :=
    Fin.cast (zmod2CompositionFirst.length_compositeInserted zmod2CompositionLater
      zmod2CompositionTransport).symm
      (Fin.natAdd (zmod2CompositionFirst.inserted.length -
        zmod2CompositionTransport.insertionPreimage.card) (1 : Fin 2))
  have hdirectLaterGet₀ : zmod2CompositionDirect.inserted.get directLater₀ =
      zmod2CompositionLater.inserted.get (0 : Fin 2) :=
    zmod2CompositionFirst.compositeInserted_get_later zmod2CompositionLater
      zmod2CompositionTransport (0 : Fin 2)
  have hdirectLaterGet₁ : zmod2CompositionDirect.inserted.get directLater₁ =
      zmod2CompositionLater.inserted.get (1 : Fin 2) :=
    zmod2CompositionFirst.compositeInserted_get_later zmod2CompositionLater
      zmod2CompositionTransport (1 : Fin 2)
  have hdirectSurvivorCount : 4 - zmod2CompositionDirect.removed.card = 3 := by
    rw [hdirectRemoved]
    decide
  have hdirectPriorVal : directPrior.val = 0 := by
    rfl
  have hdirectLaterVal₀ : directLater₀.val = 1 := by
    change zmod2CompositionFirst.inserted.length -
      zmod2CompositionTransport.insertionPreimage.card = 1
    rw [htransportInsertions]
    decide
  have hdirectLaterVal₁ : directLater₁.val = 2 := by
    change zmod2CompositionFirst.inserted.length -
      zmod2CompositionTransport.insertionPreimage.card + 1 = 2
    rw [htransportInsertions]
    decide
  refine ⟨by decide, rfl, rfl, rfl, rfl, by decide, by decide,
    zmod2CompositionDirect_resultRank, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hslot : zmod2CompositionDirect.survivorSlot d₀ =
        Fin.cast zmod2CompositionDirect_resultRank.symm (0 : Fin 6) := by
      apply Fin.ext
      rfl
    calc
      zmod2CompositionDirect.output.term (Fin.cast zmod2CompositionDirect_resultRank.symm 0) =
          zmod2CompositionDirect.output.term (zmod2CompositionDirect.survivorSlot d₀) :=
        congrArg zmod2CompositionDirect.output.term hslot.symm
      _ = zmod2CompositionSource.term (zmod2CompositionDirect.survivor d₀) :=
        zmod2CompositionDirect.output_survivor_term d₀
      _ = (![1, 0, 0, 0, 0], ![1], ![1]) := by rw [hdsurvivor₀]; rfl
  · have hslot : zmod2CompositionDirect.survivorSlot d₁ =
        Fin.cast zmod2CompositionDirect_resultRank.symm (1 : Fin 6) := by
      apply Fin.ext
      rfl
    calc
      zmod2CompositionDirect.output.term (Fin.cast zmod2CompositionDirect_resultRank.symm 1) =
          zmod2CompositionDirect.output.term (zmod2CompositionDirect.survivorSlot d₁) :=
        congrArg zmod2CompositionDirect.output.term hslot.symm
      _ = zmod2CompositionSource.term (zmod2CompositionDirect.survivor d₁) :=
        zmod2CompositionDirect.output_survivor_term d₁
      _ = (![0, 0, 1, 0, 0], ![1], ![1]) := by rw [hdsurvivor₁]; rfl
  · have hslot : zmod2CompositionDirect.survivorSlot d₂ =
        Fin.cast zmod2CompositionDirect_resultRank.symm (2 : Fin 6) := by
      apply Fin.ext
      rfl
    calc
      zmod2CompositionDirect.output.term (Fin.cast zmod2CompositionDirect_resultRank.symm 2) =
          zmod2CompositionDirect.output.term (zmod2CompositionDirect.survivorSlot d₂) :=
        congrArg zmod2CompositionDirect.output.term hslot.symm
      _ = zmod2CompositionSource.term (zmod2CompositionDirect.survivor d₂) :=
        zmod2CompositionDirect.output_survivor_term d₂
      _ = (![0, 0, 0, 1, 0], ![1], ![1]) := by rw [hdsurvivor₂]; rfl
  · have hslot : zmod2CompositionDirect.insertedSlot directPrior =
        Fin.cast zmod2CompositionDirect_resultRank.symm (3 : Fin 6) := by
      apply Fin.ext
      change 4 - zmod2CompositionDirect.removed.card + directPrior.val = 3
      rw [hdirectSurvivorCount, hdirectPriorVal]
    calc
      zmod2CompositionDirect.output.term (Fin.cast zmod2CompositionDirect_resultRank.symm 3) =
          zmod2CompositionDirect.output.term
            (zmod2CompositionDirect.insertedSlot directPrior) :=
        congrArg zmod2CompositionDirect.output.term hslot.symm
      _ = zmod2CompositionDirect.inserted.get directPrior :=
        zmod2CompositionDirect.output_inserted_term directPrior
      _ = zmod2CompositionFirst.inserted.get prior := hdirectPriorGet
      _ = (![0, 1, 0, 0, 1], ![1], ![1]) := by rw [hprior]; rfl
  · have hslot : zmod2CompositionDirect.insertedSlot directLater₀ =
        Fin.cast zmod2CompositionDirect_resultRank.symm (4 : Fin 6) := by
      apply Fin.ext
      change 4 - zmod2CompositionDirect.removed.card + directLater₀.val = 4
      rw [hdirectSurvivorCount, hdirectLaterVal₀]
    calc
      zmod2CompositionDirect.output.term (Fin.cast zmod2CompositionDirect_resultRank.symm 4) =
          zmod2CompositionDirect.output.term
            (zmod2CompositionDirect.insertedSlot directLater₀) :=
        congrArg zmod2CompositionDirect.output.term hslot.symm
      _ = zmod2CompositionDirect.inserted.get directLater₀ :=
        zmod2CompositionDirect.output_inserted_term directLater₀
      _ = zmod2CompositionLater.inserted.get (0 : Fin 2) := hdirectLaterGet₀
      _ = (![1, 0, 1, 0, 0], ![1], ![1]) := rfl
  · have hslot : zmod2CompositionDirect.insertedSlot directLater₁ =
        Fin.cast zmod2CompositionDirect_resultRank.symm (5 : Fin 6) := by
      apply Fin.ext
      change 4 - zmod2CompositionDirect.removed.card + directLater₁.val = 5
      rw [hdirectSurvivorCount, hdirectLaterVal₁]
    calc
      zmod2CompositionDirect.output.term (Fin.cast zmod2CompositionDirect_resultRank.symm 5) =
          zmod2CompositionDirect.output.term
            (zmod2CompositionDirect.insertedSlot directLater₁) :=
        congrArg zmod2CompositionDirect.output.term hslot.symm
      _ = zmod2CompositionDirect.inserted.get directLater₁ :=
        zmod2CompositionDirect.output_inserted_term directLater₁
      _ = zmod2CompositionLater.inserted.get (1 : Fin 2) := hdirectLaterGet₁
      _ = (![1, 0, 1, 0, 1], ![1], ![1]) := rfl
  · have hslot : zmod2CompositionLater.survivorSlot l₀ = (0 : Fin 6) := by
      apply Fin.ext
      rfl
    calc
      zmod2CompositionLater.output.term 0 =
          zmod2CompositionLater.output.term (zmod2CompositionLater.survivorSlot l₀) :=
        congrArg zmod2CompositionLater.output.term hslot.symm
      _ = zmod2CompositionFirst.output.term (zmod2CompositionLater.survivor l₀) :=
        zmod2CompositionLater.output_survivor_term l₀
      _ = zmod2CompositionFirst.output.term 0 :=
        congrArg zmod2CompositionFirst.output.term hlsurvivor₀
      _ = (![1, 0, 0, 0, 0], ![1], ![1]) := hfirstTerm₀
  · have hslot : zmod2CompositionLater.survivorSlot l₁ = (1 : Fin 6) := by
      apply Fin.ext
      rfl
    calc
      zmod2CompositionLater.output.term 1 =
          zmod2CompositionLater.output.term (zmod2CompositionLater.survivorSlot l₁) :=
        congrArg zmod2CompositionLater.output.term hslot.symm
      _ = zmod2CompositionFirst.output.term (zmod2CompositionLater.survivor l₁) :=
        zmod2CompositionLater.output_survivor_term l₁
      _ = zmod2CompositionFirst.output.term 1 :=
        congrArg zmod2CompositionFirst.output.term hlsurvivor₁
      _ = (![0, 0, 1, 0, 0], ![1], ![1]) := hfirstTerm₁
  · have hslot : zmod2CompositionLater.survivorSlot l₂ = (2 : Fin 6) := by
      apply Fin.ext
      rfl
    calc
      zmod2CompositionLater.output.term 2 =
          zmod2CompositionLater.output.term (zmod2CompositionLater.survivorSlot l₂) :=
        congrArg zmod2CompositionLater.output.term hslot.symm
      _ = zmod2CompositionFirst.output.term (zmod2CompositionLater.survivor l₂) :=
        zmod2CompositionLater.output_survivor_term l₂
      _ = zmod2CompositionFirst.output.term 2 :=
        congrArg zmod2CompositionFirst.output.term hlsurvivor₂
      _ = (![0, 0, 0, 1, 0], ![1], ![1]) := hfirstTerm₂
  · have hslot : zmod2CompositionLater.survivorSlot l₃ = (3 : Fin 6) := by
      apply Fin.ext
      rfl
    calc
      zmod2CompositionLater.output.term 3 =
          zmod2CompositionLater.output.term (zmod2CompositionLater.survivorSlot l₃) :=
        congrArg zmod2CompositionLater.output.term hslot.symm
      _ = zmod2CompositionFirst.output.term (zmod2CompositionLater.survivor l₃) :=
        zmod2CompositionLater.output_survivor_term l₃
      _ = zmod2CompositionFirst.output.term 4 :=
        congrArg zmod2CompositionFirst.output.term hlsurvivor₃
      _ = (![0, 1, 0, 0, 1], ![1], ![1]) := hfirstTerm₄
  · have hslot : zmod2CompositionLater.insertedSlot (0 : Fin 2) = (4 : Fin 6) := by
      apply Fin.ext
      rfl
    calc
      zmod2CompositionLater.output.term 4 =
          zmod2CompositionLater.output.term
            (zmod2CompositionLater.insertedSlot (0 : Fin 2)) :=
        congrArg zmod2CompositionLater.output.term hslot.symm
      _ = zmod2CompositionLater.inserted.get (0 : Fin 2) :=
        zmod2CompositionLater.output_inserted_term (0 : Fin 2)
      _ = (![1, 0, 1, 0, 0], ![1], ![1]) := rfl
  · have hslot : zmod2CompositionLater.insertedSlot (1 : Fin 2) = (5 : Fin 6) := by
      apply Fin.ext
      rfl
    calc
      zmod2CompositionLater.output.term 5 =
          zmod2CompositionLater.output.term
            (zmod2CompositionLater.insertedSlot (1 : Fin 2)) :=
        congrArg zmod2CompositionLater.output.term hslot.symm
      _ = zmod2CompositionLater.inserted.get (1 : Fin 2) :=
        zmod2CompositionLater.output_inserted_term (1 : Fin 2)
      _ = (![1, 0, 1, 0, 1], ![1], ![1]) := rfl


#check @zmod2_rankChange_fixture
#check @zmod2_compositionBlocks_fixture
#check @Certificate.output
#check @Certificate.sumTensor_eq
#check @Certificate.rankLE_resultRank
#check @Certificate.valid_output
#check @Certificate.removed_eq_image_transported
#check @Certificate.composite
#check @Certificate.composite_resultRank_eq_later_resultRank
#check @Certificate.composite_output_term_cast_eq_later_output_term
#check @Certificate.composite_output_cast_eq_later_output
#check @Certificate.Composition.direct_sumTensor_eq
#check @Certificate.Composition.direct_output_cast_eq_later_output
#check @Certificate.Composition.sumTensor_eq
#check @Certificate.transport

#print axioms zmod2_rankChange_fixture
#print axioms zmod2_compositionBlocks_fixture
#print axioms Certificate.sumTensor_eq
#print axioms Certificate.rankLE_resultRank
#print axioms Certificate.valid_output
#print axioms Certificate.removed_eq_image_transported
#print axioms Certificate.composite
#print axioms Certificate.composite_resultRank_eq_later_resultRank
#print axioms Certificate.composite_output_term_cast_eq_later_output_term
#print axioms Certificate.composite_output_cast_eq_later_output
#print axioms Certificate.Composition.direct_sumTensor_eq
#print axioms Certificate.Composition.direct_output_cast_eq_later_output
#print axioms Certificate.Composition.sumTensor_eq
#print axioms Certificate.transport

end Replacement
end Scheme
end BilinearComplexity
