/-
  Scratch/GlobalRankSearch/TwoModeCompletion — exact completion of two fixed
  tensor-factor families by a third family.

  The criterion is coordinate-level and explicit: mode-three slice
  coefficients transpose directly into the missing third factors.  The
  finite family of choices used for span witnesses relies on `Classical.choice`.
-/
import Scratch.GlobalRankSearch.SliceCover

set_option autoImplicit false

namespace BilinearComplexity

/-- The mode-three slice of `T` at `l`, flattened as a vector indexed by
`Fin a × Fin b`. -/
def modeThreeSlice {k : Type*} {a b c : ℕ} (T : Tensor k a b c) (l : Fin c) :
    Fin a × Fin b → k :=
  fun ij => T ij.1 ij.2 l

/-- The flattened pair vector formed by the outer product of fixed first- and
second-mode factors. -/
def fixedPairVector {k : Type*} [Mul k] {a b : ℕ}
    (u : Fin a → k) (v : Fin b → k) : Fin a × Fin b → k :=
  fun ij => u ij.1 * v ij.2

/-- Completing two fixed factor families is equivalent to choosing, separately
for every mode-three slice, coefficients for those same fixed pair vectors.
The witnesses transpose explicitly by `w s l = coeff l s`; assembling the
slice-wise witnesses may use classical choice. -/
theorem exists_third_factors_iff_exists_modeThree_coefficients
    {k : Type*} [CommSemiring k] {a b c r : ℕ} (T : Tensor k a b c)
    (u : Fin r → Fin a → k) (v : Fin r → Fin b → k) :
    (∃ w : Fin r → Fin c → k,
      ∀ i j l, T i j l = ∑ s, u s i * v s j * w s l) ↔
      ∀ l, ∃ coeff : Fin r → k,
        ∀ i j, T i j l = ∑ s, u s i * v s j * coeff s := by
  constructor
  · rintro ⟨w, hdecomp⟩ l
    exact ⟨fun s => w s l, fun i j => hdecomp i j l⟩
  · intro hcoeff
    choose coeff hcoeff_eq using hcoeff
    exact ⟨fun s l => coeff l s, fun i j l => hcoeff_eq l i j⟩

/-- Two fixed factor families can be completed by exact third factors for `T`
if and only if every mode-three slice of `T` lies in the span of their fixed
pair vectors.
In the reverse implication, chosen linear coefficients of slice `l` become the
entries `w s l` of the explicit third-factor witness. -/
theorem exists_third_factors_iff_modeThreeSlice_mem_span
    {k : Type*} [CommSemiring k] {a b c r : ℕ} (T : Tensor k a b c)
    (u : Fin r → Fin a → k) (v : Fin r → Fin b → k) :
    (∃ w : Fin r → Fin c → k,
      ∀ i j l, T i j l = ∑ s, u s i * v s j * w s l) ↔
      ∀ l, modeThreeSlice T l ∈
        Submodule.span k (Set.range fun s => fixedPairVector (u s) (v s)) := by
  classical
  constructor
  · rintro ⟨w, hdecomp⟩ l
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun s => w s l, ?_⟩
    funext ij
    simpa [modeThreeSlice, fixedPairVector, mul_comm, mul_left_comm, mul_assoc] using
      (hdecomp ij.1 ij.2 l).symm
  · intro hspan
    have hcoeff : ∀ l, ∃ coeff : Fin r → k,
        ∑ s, coeff s • fixedPairVector (u s) (v s) = modeThreeSlice T l :=
      fun l => by
        rw [← Submodule.mem_span_range_iff_exists_fun]
        exact hspan l
    choose coeff hcoeff_eq using hcoeff
    refine ⟨fun s l => coeff l s, ?_⟩
    intro i j l
    have hentry := congrFun (hcoeff_eq l) (i, j)
    simpa [modeThreeSlice, fixedPairVector, mul_comm, mul_left_comm, mul_assoc] using
      hentry.symm

/-- Ground check for the mode-three slice coordinate convention. -/
example : modeThreeSlice (fun _ _ _ => (7 : ℚ) : Tensor ℚ 1 1 1) 0 (0, 0) = 7 :=
  rfl

/-- Ground check for the fixed pair-vector coordinate convention. -/
example : fixedPairVector (fun _ : Fin 1 => (2 : ℚ))
    (fun _ : Fin 1 => 3) (0, 0) = 6 := by
  norm_num [fixedPairVector]

/-- Joint non-vacuity check: a nonzero tensor on two coordinates in every
mode has both an explicit one-term completion and the corresponding slice-span
certificate. -/
example :
    let u : Fin 1 → Fin 2 → ℚ := fun _ _ => 2
    let v : Fin 1 → Fin 2 → ℚ := fun _ _ => 3
    let T : Tensor ℚ 2 2 2 := fun _ _ _ => 30
    (∃ w : Fin 1 → Fin 2 → ℚ,
      ∀ i j l, T i j l = ∑ s, u s i * v s j * w s l) ∧
      ∀ l, modeThreeSlice T l ∈
        Submodule.span ℚ (Set.range fun s => fixedPairVector (u s) (v s)) := by
  dsimp only
  have hcomplete :
      ∃ w : Fin 1 → Fin 2 → ℚ,
        ∀ (_i _j _l : Fin 2), (30 : ℚ) = ∑ s, (2 : ℚ) * 3 * w s _l := by
    refine ⟨fun _ _ => 5, ?_⟩
    intro i j l
    rw [Fin.sum_univ_one]
    norm_num
  exact ⟨hcomplete,
    (exists_third_factors_iff_modeThreeSlice_mem_span
      (fun _ _ _ => (30 : ℚ)) (fun _ _ => 2) (fun _ _ => 3)).mp hcomplete⟩

#check @modeThreeSlice
#check @fixedPairVector
#check @exists_third_factors_iff_exists_modeThree_coefficients
#check @exists_third_factors_iff_modeThreeSlice_mem_span

#print axioms exists_third_factors_iff_exists_modeThree_coefficients
#print axioms exists_third_factors_iff_modeThreeSlice_mem_span

end BilinearComplexity
