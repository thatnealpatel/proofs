/-
  Scratch/GlobalRankSearch/SliceCover — an exact coordinate formulation of
  tensor rank through a rank-one dictionary covering one mode's slices.

  This file is exploratory. It tests the foundational equivalence needed by
  the global slice-incidence search before any API is promoted to the library.
-/
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import BilinearComplexity.Basic

set_option autoImplicit false

namespace BilinearComplexity

/-- The mode-one slice of `T` at `i`, flattened as a vector indexed by
`Fin b × Fin c`. -/
def modeOneSlice {k : Type*} {a b c : ℕ} (T : Tensor k a b c) (i : Fin a) :
    Fin b × Fin c → k :=
  fun jl => T i jl.1 jl.2

/-- The flattened rank-one matrix formed by the outer product of `v` and `w`. -/
def rankOneMatrixVector {k : Type*} [Mul k] {b c : ℕ}
    (v : Fin b → k) (w : Fin c → k) : Fin b × Fin c → k :=
  fun jl => v jl.1 * w jl.2

/-- `SliceCover T r` says that every mode-one slice of `T` lies in the span
of one shared dictionary of `r` rank-one matrices. -/
def SliceCover {k : Type*} [CommSemiring k] {a b c : ℕ}
    (T : Tensor k a b c) (r : ℕ) : Prop :=
  ∃ v : Fin r → Fin b → k, ∃ w : Fin r → Fin c → k,
    ∀ i, modeOneSlice T i ∈
      Submodule.span k (Set.range fun s => rankOneMatrixVector (v s) (w s))

/-- A tensor has rank at most `r` exactly when one complementary rank-one
matrix dictionary of size `r` spans every mode-one slice. -/
theorem rankLE_iff_sliceCover {k : Type*} [CommSemiring k] {a b c r : ℕ}
    {T : Tensor k a b c} : RankLE T r ↔ SliceCover T r := by
  classical
  constructor
  · rintro ⟨u, v, w, rfl⟩
    refine ⟨v, w, fun i => ?_⟩
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun s => u s i, ?_⟩
    funext jl
    simp [modeOneSlice, rankOneMatrixVector, mul_assoc]
  · rintro ⟨v, w, hcover⟩
    have hcoeff : ∀ i, ∃ coeff : Fin r → k,
        ∑ s, coeff s • rankOneMatrixVector (v s) (w s) = modeOneSlice T i :=
      fun i => by
        rw [← Submodule.mem_span_range_iff_exists_fun]
        exact hcover i
    choose coeff hcoeff_eq using hcoeff
    refine ⟨fun s i => coeff i s, v, w, ?_⟩
    funext i j l
    have hentry := congrFun (hcoeff_eq i) (j, l)
    simpa [modeOneSlice, rankOneMatrixVector, mul_assoc] using hentry.symm

/-- Ground check for the mode-one slice coordinate convention. -/
example : modeOneSlice (fun _ _ _ => (7 : ℚ) : Tensor ℚ 1 1 1) 0 (0, 0) = 7 :=
  rfl

/-- Ground check for the rank-one matrix coordinate convention. -/
example :
    rankOneMatrixVector (fun _ : Fin 1 => (2 : ℚ)) (fun _ : Fin 1 => 3) (0, 0) = 6 := by
  norm_num [rankOneMatrixVector]

/-- Joint non-vacuity check: the nonzero scalar multiplication tensor has both
a one-term triad decomposition and a one-point slice cover. -/
example :
    let T : Tensor ℚ 1 1 1 := fun _ _ _ => 1
    RankLE T 1 ∧ SliceCover T 1 := by
  dsimp
  have hrank : RankLE (fun _ _ _ => (1 : ℚ) : Tensor ℚ 1 1 1) 1 :=
    ⟨fun _ _ => 1, fun _ _ => 1, fun _ _ => 1, by funext; simp⟩
  exact ⟨hrank, rankLE_iff_sliceCover.mp hrank⟩

#check @modeOneSlice
#check @rankOneMatrixVector
#check @SliceCover
#check @rankLE_iff_sliceCover
#print axioms rankLE_iff_sliceCover

end BilinearComplexity
