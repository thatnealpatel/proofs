/-
  BilinearComplexity/PeelingCert333 — certified schoolbook decomposition of
  `matMulTensor (ZMod 2) 3 3 3` with peak 26. Card Nc2.

  The schoolbook decomposition consists of 27 rank-one triads
  `e_{ij} ⊗ e_{jl} ⊗ e_{li}` for `(i,j,l) ∈ {0,1,2}³`, in the canonical
  lexicographic order on `(i,j,l)`. Each triad has a single nonzero cell in
  the tensor, all 27 cells are distinct (they cover all of `matMulTensor`'s
  support), and supports are pairwise disjoint. Every ordering therefore
  yields the same trajectory `[26, 25, ..., 1, 0]` with peak exactly 26.

  We certify one ordering (canonical) by `native_decide`.

  CONVENTION: `peak` uses the j ≥ 1 convention (see Peeling.lean header).
  The initial `nnz(T) = 27` at j = 0 is excluded. Under the convention that
  includes j = 0, this decomposition instead has peak `max(27, 26) = 27`.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import BilinearComplexity.Peeling
import Mathlib.Data.ZMod.Basic

namespace BilinearComplexity

/-! ## 1. Helpers: standard basis vectors over ZMod 2 -/

/-- Standard basis indicator vector `eᵢ` in `(Fin n → ZMod 2)`. -/
abbrev basisVec (n : ℕ) (idx : Fin n) : Fin n → ZMod 2 :=
  fun i => if i = idx then 1 else 0

/-! ## 2. Schoolbook triads and decomposition -/

/-- Schoolbook triad for index triple `(i, j, l)` with `i, j, l : Fin 3`.
Produces `e_{3i+j} ⊗ e_{3j+l} ⊗ e_{3l+i}` as a `TriadData (ZMod 2) 9 9 9`,
matching the `finProdFinEquiv` packing `(a, b) ↦ b + 3 * a`. -/
abbrev schoolbookTriad (i j l : Fin 3) : TriadData (ZMod 2) 9 9 9 :=
  (basisVec 9 ⟨j + 3 * i, by omega⟩,
   basisVec 9 ⟨l + 3 * j, by omega⟩,
   basisVec 9 ⟨i + 3 * l, by omega⟩)

/-- The 27-element schoolbook decomposition of `⟨3,3,3⟩` over `ZMod 2`,
in canonical lexicographic order on `(i, j, l)`. -/
abbrev schoolbookDecomp333 : Decomp (ZMod 2) 9 9 9 :=
  (List.finRange 3).flatMap fun i =>
    (List.finRange 3).flatMap fun j =>
      (List.finRange 3).map fun l =>
        schoolbookTriad i j l

/-! ## 3. Certified properties -/

/-- The schoolbook list has exactly 27 triads. Kernel `decide` (a `List.length`
of a literal 27-element list), so this lemma adds no compiler trust. -/
theorem schoolbookDecomp333_length :
    schoolbookDecomp333.length = 27 := by decide

/-- The schoolbook decomposition is a valid decomposition of
`matMulTensor (ZMod 2) 3 3 3`. -/
theorem schoolbookDecomp333_isDecomp :
    IsDecomp (matMulTensor (ZMod 2) 3 3 3) schoolbookDecomp333 := by
  rw [← isDecompB_iff]
  native_decide

/-- The peak of the schoolbook decomposition (in canonical order) is 26. -/
theorem schoolbookDecomp333_peak :
    peak (matMulTensor (ZMod 2) 3 3 3) schoolbookDecomp333 = 26 := by
  native_decide

/-- **P(27) ≤ 26**: the schoolbook decomposition of `⟨3,3,3⟩` over `ZMod 2`
witnesses that the 27-triad decomposition can be ordered with peak at most 26.
(In fact, every ordering achieves peak exactly 26, but certifying one suffices
for the upper bound.) -/
theorem peak_matMulTensor_333_le_26 :
    peak (matMulTensor (ZMod 2) 3 3 3) schoolbookDecomp333 ≤ 26 :=
  le_of_eq schoolbookDecomp333_peak

end BilinearComplexity
