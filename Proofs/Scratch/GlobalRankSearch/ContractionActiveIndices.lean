/-
  Scratch/GlobalRankSearch/ContractionActiveIndices — multiplicity-aware
  active-index bounds after a rectangular linear substitution in one tensor
  mode.

  A rectangular matrix need not be surjective and may kill some factors in an
  exact triad decomposition.  The surviving summand indices, rather than the
  distinct surviving vectors, index a decomposition of the contracted tensor.
  Thus repeated surviving factors retain their multiplicity in the resulting
  cardinality bound.
-/
import BilinearComplexity.RankCalculus
import Mathlib.LinearAlgebra.Matrix.Notation

set_option autoImplicit false

namespace BilinearComplexity

open scoped Matrix

/-- Indices in an exact triad family whose first factor survives mode-one
contraction by `M`.  This is a finset of original indices, so equal surviving
factors at different indices retain their multiplicity. -/
noncomputable def contractionActiveIndices {k : Type*} [CommSemiring k]
    {a a' s : ℕ} (M : Matrix (Fin a') (Fin a) k)
    (u : Fin s → Fin a → k) : Finset (Fin s) :=
  @Finset.filter (Fin s) (fun t => M.mulVec (u t) ≠ 0)
    (fun _ => Classical.propDecidable _) Finset.univ

/-- Membership in `contractionActiveIndices` is exactly nonvanishing of the
transformed factor. -/
theorem mem_contractionActiveIndices_iff {k : Type*} [CommSemiring k]
    {a a' s : ℕ} (M : Matrix (Fin a') (Fin a) k)
    (u : Fin s → Fin a → k) (t : Fin s) :
    t ∈ contractionActiveIndices M u ↔ M.mulVec (u t) ≠ 0 := by
  classical
  simp [contractionActiveIndices]

/-- Ground check: projection onto the first coordinate kills only the middle
term, while the two equal-direction survivors remain as two active indices. -/
example :
    let M : Matrix (Fin 1) (Fin 2) ℚ := !![(1 : ℚ), 0]
    let u : Fin 3 → Fin 2 → ℚ := ![![1, 0], ![0, 1], ![2, 0]]
    contractionActiveIndices M u = {0, 2} := by
  classical
  ext t
  fin_cases t <;>
    simp [contractionActiveIndices, dotProduct, Fin.sum_univ_succ]

/-- In an exact `Fin s` triad decomposition, contracting mode one yields a
triad decomposition indexed by precisely the original summands whose
transformed first factor is nonzero. -/
theorem rankLE_contract₁_card_active {k : Type*} [CommSemiring k]
    {a a' b c s : ℕ} (T : Tensor k a b c)
    (u : Fin s → Fin a → k) (v : Fin s → Fin b → k)
    (w : Fin s → Fin c → k)
    (hdecomp : T = fun i j l => ∑ t, u t i * v t j * w t l)
    (M : Matrix (Fin a') (Fin a) k) :
    RankLE (contract₁ M T) (contractionActiveIndices M u).card := by
  classical
  let active := contractionActiveIndices M u
  let e := active.equivFin.symm
  refine ⟨fun q => M.mulVec (u (e q)), fun q => v (e q), fun q => w (e q), ?_⟩
  funext i' j l
  rw [hdecomp]
  simp only [contract₁, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hrearrange :
      (∑ t, ∑ i, M i' i * (u t i * v t j * w t l)) =
        ∑ t, M.mulVec (u t) i' * v t j * w t l := by
    apply Finset.sum_congr rfl
    intro t _
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hrearrange]
  calc
    (∑ t, M.mulVec (u t) i' * v t j * w t l) =
        ∑ t ∈ active, M.mulVec (u t) i' * v t j * w t l := by
      symm
      apply Finset.sum_subset (Finset.subset_univ active)
      intro t _ ht
      have hfactor : M.mulVec (u t) = 0 := by
        apply not_ne_iff.mp
        intro hne
        exact ht ((mem_contractionActiveIndices_iff M u t).2 hne)
      simp [hfactor]
    _ = ∑ t : active, M.mulVec (u t) i' * v t j * w t l := by
      apply Finset.sum_subtype active
      intro t
      rfl
    _ = ∑ q : Fin active.card,
        M.mulVec (u (e q)) i' * v (e q) j * w (e q) l := by
      exact (Equiv.sum_comp e
        (fun t : active => M.mulVec (u t) i' * v t j * w t l)).symm

/-- Consequently, over a field the rank of a mode-one contraction is at most
the multiplicity-aware number of surviving decomposition indices. -/
theorem rank_contract₁_le_card_active {k : Type*} [Field k]
    {a a' b c s : ℕ} (T : Tensor k a b c)
    (u : Fin s → Fin a → k) (v : Fin s → Fin b → k)
    (w : Fin s → Fin c → k)
    (hdecomp : T = fun i j l => ∑ t, u t i * v t j * w t l)
    (M : Matrix (Fin a') (Fin a) k) :
    rank (contract₁ M T) ≤ (contractionActiveIndices M u).card :=
  rank_le_of_rankLE (rankLE_contract₁_card_active T u v w hdecomp M)

/-- Cyclic mode-two form of the active-index decomposition bound. -/
theorem rankLE_contract₂_card_active {k : Type*} [CommSemiring k]
    {a b b' c s : ℕ} (T : Tensor k a b c)
    (u : Fin s → Fin a → k) (v : Fin s → Fin b → k)
    (w : Fin s → Fin c → k)
    (hdecomp : T = fun i j l => ∑ t, u t i * v t j * w t l)
    (M : Matrix (Fin b') (Fin b) k) :
    RankLE (contract₂ M T) (contractionActiveIndices M v).card := by
  have hrotate : cyc T = fun j l i => ∑ t, v t j * w t l * u t i := by
    funext j l i
    simp only [cyc_apply]
    rw [hdecomp]
    exact Finset.sum_congr rfl fun t _ => by ring
  have hactive := rankLE_contract₁_card_active (cyc T) v w u hrotate M
  rw [contract₂_eq_cyc]
  exact hactive.cyc.cyc

/-- Over a field, mode-two tensor rank is bounded by the number of original
second factors that survive the rectangular substitution. -/
theorem rank_contract₂_le_card_active {k : Type*} [Field k]
    {a b b' c s : ℕ} (T : Tensor k a b c)
    (u : Fin s → Fin a → k) (v : Fin s → Fin b → k)
    (w : Fin s → Fin c → k)
    (hdecomp : T = fun i j l => ∑ t, u t i * v t j * w t l)
    (M : Matrix (Fin b') (Fin b) k) :
    rank (contract₂ M T) ≤ (contractionActiveIndices M v).card :=
  rank_le_of_rankLE (rankLE_contract₂_card_active T u v w hdecomp M)

/-- Cyclic mode-three form of the active-index decomposition bound. -/
theorem rankLE_contract₃_card_active {k : Type*} [CommSemiring k]
    {a b c c' s : ℕ} (T : Tensor k a b c)
    (u : Fin s → Fin a → k) (v : Fin s → Fin b → k)
    (w : Fin s → Fin c → k)
    (hdecomp : T = fun i j l => ∑ t, u t i * v t j * w t l)
    (M : Matrix (Fin c') (Fin c) k) :
    RankLE (contract₃ M T) (contractionActiveIndices M w).card := by
  have hrotate : cyc (cyc T) = fun l i j => ∑ t, w t l * u t i * v t j := by
    funext l i j
    simp only [cyc_apply]
    rw [hdecomp]
    exact Finset.sum_congr rfl fun t _ => by ring
  have hactive := rankLE_contract₁_card_active (cyc (cyc T)) w u v hrotate M
  rw [contract₃_eq_cyc]
  exact hactive.cyc

/-- Over a field, mode-three tensor rank is bounded by the number of original
third factors that survive the rectangular substitution. -/
theorem rank_contract₃_le_card_active {k : Type*} [Field k]
    {a b c c' s : ℕ} (T : Tensor k a b c)
    (u : Fin s → Fin a → k) (v : Fin s → Fin b → k)
    (w : Fin s → Fin c → k)
    (hdecomp : T = fun i j l => ∑ t, u t i * v t j * w t l)
    (M : Matrix (Fin c') (Fin c) k) :
    rank (contract₃ M T) ≤ (contractionActiveIndices M w).card :=
  rank_le_of_rankLE (rankLE_contract₃_card_active T u v w hdecomp M)

/-- Concrete nonvacuous projection: a `1 × 2` projection kills the middle of
three summands, keeps two proportional surviving first factors as distinct
indices, and produces the nonzero scalar tensor with entry `3`. -/
example :
    let M : Matrix (Fin 1) (Fin 2) ℚ := !![(1 : ℚ), 0]
    let u : Fin 3 → Fin 2 → ℚ := ![![1, 0], ![0, 1], ![2, 0]]
    let v : Fin 3 → Fin 1 → ℚ := fun _ _ => 1
    let w : Fin 3 → Fin 1 → ℚ := fun _ _ => 1
    let T : Tensor ℚ 2 1 1 := fun i j l => ∑ t, u t i * v t j * w t l
    contractionActiveIndices M u = {0, 2} ∧
      contract₁ M T = (fun _ _ _ => 3) ∧
      RankLE (contract₁ M T) 2 ∧ rank (contract₁ M T) ≤ 2 := by
  classical
  let M : Matrix (Fin 1) (Fin 2) ℚ := !![(1 : ℚ), 0]
  let u : Fin 3 → Fin 2 → ℚ := ![![1, 0], ![0, 1], ![2, 0]]
  let v : Fin 3 → Fin 1 → ℚ := fun _ _ => 1
  let w : Fin 3 → Fin 1 → ℚ := fun _ _ => 1
  let T : Tensor ℚ 2 1 1 := fun i j l => ∑ t, u t i * v t j * w t l
  change contractionActiveIndices M u = {0, 2} ∧
    contract₁ M T = (fun _ _ _ => 3) ∧
    RankLE (contract₁ M T) 2 ∧ rank (contract₁ M T) ≤ 2
  have hactive : contractionActiveIndices M u = {0, 2} := by
    ext t
    fin_cases t <;>
      simp [contractionActiveIndices, dotProduct, Fin.sum_univ_succ, M, u]
  have hcontract : contract₁ M T = (fun _ _ _ => 3) := by
    funext i j l
    fin_cases i
    fin_cases j
    fin_cases l
    norm_num [contract₁, T, M, u, v, w, Fin.sum_univ_succ]
  have hdecomp : T = fun i j l => ∑ t, u t i * v t j * w t l := rfl
  have hcard : (contractionActiveIndices M u).card = 2 := by
    rw [hactive]
    decide
  have hRankLE : RankLE (contract₁ M T) 2 := by
    simpa only [hcard] using rankLE_contract₁_card_active T u v w hdecomp M
  exact ⟨hactive, hcontract, hRankLE, rank_le_of_rankLE hRankLE⟩

#check @contractionActiveIndices
#check @mem_contractionActiveIndices_iff
#check @rankLE_contract₁_card_active
#check @rank_contract₁_le_card_active
#check @rankLE_contract₂_card_active
#check @rank_contract₂_le_card_active
#check @rankLE_contract₃_card_active
#check @rank_contract₃_le_card_active

#print axioms mem_contractionActiveIndices_iff
#print axioms rankLE_contract₁_card_active
#print axioms rank_contract₁_le_card_active
#print axioms rankLE_contract₂_card_active
#print axioms rank_contract₂_le_card_active
#print axioms rankLE_contract₃_card_active
#print axioms rank_contract₃_le_card_active

end BilinearComplexity
