/-
  Vp2/Apolarity — the modeled (111) border-apolarity test as concrete
  linear algebra, and its soundness on the rank locus.

  This file supplies the infrastructure that discharges the two final
  `sorry`s of `Proofs.Vp2.Vp2` (`Passes111`, `passes111_of_borderRankLE`):

    · `flatteningA/B/C`, `sliceA/B/C` — the three flattening maps of a
      3-tensor (CHL §2.1: `T_A`, `T_B`, `T_C`) and the slice maps of
      `A⊗B⊗C`, as `LinearMap`s between concrete function spaces.
    · `Candidate111 T r` — the (111) candidate condition, in the DUAL
      form of CHL Prop 3.1 eq (7) [arXiv:1911.07981] with the Hilbert
      function min-truncated per BB Thm 1.2 [arXiv:1910.01944]: three
      subspaces of dimension exactly `min r n²` containing the
      flattening images `T(C*)`, `T(B*)`, `T(A*)`, whose slicewise
      triple intersection inside `A⊗B⊗C` has dimension ≥ `min r n³`.
    · `test111Locus` — the accept locus of that search, as a set of
      entry vectors (exact analogue of `rankLocus`, BorderRank.lean).
    · `candidate111_of_linearIndependent` (Lemma A-spread) — a tensor
      decomposed into `r` linearly INDEPENDENT simple tensors satisfies
      `Candidate111 · r`. Pure linear algebra, any field.
    · `candidate111_of_sq_le` — the degenerate band: for `n² ≤ r` EVERY
      tensor is a candidate (all three subspaces `= ⊤`). See the
      content-window note below.
    · `vanishingIdeal_test111Locus_le` — the soundness core, over any
      INFINITE field: every polynomial vanishing on the (111) accept
      locus vanishes on the whole rank-≤ r locus. Proof: perturb an
      arbitrary decomposition along a polynomial line towards a spread
      reference configuration; a nonzero determinant detector confines
      the bad parameters to a finite set; a univariate polynomial
      vanishing on a cofinite subset of an infinite field is zero.
      This is the flat-limit ingredient of BB's soundness direction,
      made scalar.

  MODELED SCOPE (honesty; each omission RELAXES the test, so the
  soundness statement is a fortiori sound; NONE of them is hidden):
    · the (210)/(120) (and (201)/(102)/(021)/(012)) sibling pre-tests
      (CHL §3 steps (i)–(ii), degree-3 conditions in `S²`-pieces) are
      NOT modeled — out of the degree-(1,1,1) scope of this file;
    · the degree-(100)/(010)/(001) pieces are NOT constrained (CHL set
      them to 0 "by conciseness" — for the modeled test this is a
      strict relaxation exactly when `r < n`);
    · multidegrees of total degree ≥ 4, and extendability of the
      subspace triple to an actual graded IDEAL, are NOT modeled;
    · Borel-fixedness (CHL §2.4 condition (iv)) is NOT imposed: in the
      sources it is a WLOG reduction (Lie's theorem / BB's Fixed Ideal
      Theorem) that makes CHL's SEARCH finite; it needs an algebraically
      closed field and is not needed for soundness;
    · smoothability / Slip-membership (BB §7, the cactus gap) is NOT
      modeled — it is precisely the Hilbert-scheme infrastructure absent
      from Mathlib, and it is why the converse of soundness FAILS.

  CONTENT WINDOW (from the WP-B adversarial review; documents when the
  modeled verdict is informative):
    · `Candidate111 · r` holds for ALL tensors once `r ≥ ⌈2n³/(3n−1)⌉`
      (≈ (2/3)n²): subspaces of exact dimension `min r n²` containing
      the ≤ n-dimensional flattening images exist as soon as `r ≥ n`,
      and each slicewise comap has codimension ≤ n·(n² − min r n²), so
      the triple intersection has dimension ≥ n³ − 3n(n² − r) ≥ r on
      that band. Only the cruder band `r ≥ n²` is PROVED here
      (`candidate111_of_sq_le`); the sharper threshold is recorded as a
      remark. Consequence (documented at `DecidedByVP`, Vp2.lean §4):
      for rank families that are eventually ≥ n², the ZERO polynomial
      family decides the test — a degenerate-parameter artifact.
    · for `r < n` the accept set is expected (over algebraically closed
      fields) to have codimension ≥ 2 in the tensor space, so no single
      polynomial's vanishing can coincide with it — dimension counting,
      no barrier content. Not formalized here.
    · the informative band is therefore superlinear:
      `n ≲ r < 2n³/(3n−1)` — where matrix-multiplication-type
      parameters live.

  FIELD SCOPE: definitions are stated over any `Field k` (the
  `CommSemiring`-level maps over any commutative semiring); the
  soundness core needs `[Infinite k]`. BB/CHL prove soundness of the
  FULL Slip-membership test over algebraically closed fields; this file
  proves soundness of the WEAKER modeled (111) test's polynomial
  closure over any infinite field. Those are different theorems about
  different objects; neither claim subsumes the other. Over finite `k`
  the polynomial closure degenerates (every subset of a finite affine
  space is a zero locus), the wrap adds nothing, and the sources make
  no claim; none is made here.

  Provenance: CHL = Conner–Harper–Landsberg, arXiv:1911.07981; BB =
  Buczyńska–Buczyński, arXiv:1910.01944. The source digest for both is
  `Documents/BorderApolarity.md`.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import AlgComplexity.Vp2.BorderRank
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace Vp2

/-! ## 1. Slice and flattening maps

Concrete degree-(1,1,0)/(1,0,1)/(0,1,1) ambient spaces are all
`Fin n → Fin n → k` (matrices), in the three roles `A⊗B`, `A⊗C`, `B⊗C`;
the degree-(1,1,1) ambient space is `Tensor3 k n` itself. -/

/-- The `C`-flattening of `T` (CHL §2.1 `T_C`) as a linear map
`C* → A⊗B` : `z ↦ (i j ↦ ∑ l, T i j l * z l)`. Its range is `T(C*)`. -/
def flatteningC {k : Type*} [CommSemiring k] {n : ℕ} (T : Tensor3 k n) :
    (Fin n → k) →ₗ[k] (Fin n → Fin n → k) where
  toFun z := fun i j => ∑ l, T i j l * z l
  map_add' z z' := by
    funext i j
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' t z := by
    funext i j
    simp [Finset.mul_sum, mul_left_comm]

/-- The `B`-flattening of `T` (CHL §2.1 `T_B`) as a linear map
`B* → A⊗C` : `y ↦ (i l ↦ ∑ j, T i j l * y j)`. Its range is `T(B*)`. -/
def flatteningB {k : Type*} [CommSemiring k] {n : ℕ} (T : Tensor3 k n) :
    (Fin n → k) →ₗ[k] (Fin n → Fin n → k) where
  toFun y := fun i l => ∑ j, T i j l * y j
  map_add' y y' := by
    funext i l
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' t y := by
    funext i l
    simp [Finset.mul_sum, mul_left_comm]

/-- The `A`-flattening of `T` (CHL §2.1 `T_A`) as a linear map
`A* → B⊗C` : `x ↦ (j l ↦ ∑ i, T i j l * x i)`. Its range is `T(A*)`. -/
def flatteningA {k : Type*} [CommSemiring k] {n : ℕ} (T : Tensor3 k n) :
    (Fin n → k) →ₗ[k] (Fin n → Fin n → k) where
  toFun x := fun j l => ∑ i, T i j l * x i
  map_add' x x' := by
    funext j l
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' t x := by
    funext j l
    simp [Finset.mul_sum, mul_left_comm]

@[simp] theorem flatteningC_apply {k : Type*} [CommSemiring k] {n : ℕ}
    (T : Tensor3 k n) (z : Fin n → k) (i j : Fin n) :
    flatteningC T z i j = ∑ l, T i j l * z l := rfl

@[simp] theorem flatteningB_apply {k : Type*} [CommSemiring k] {n : ℕ}
    (T : Tensor3 k n) (y : Fin n → k) (i l : Fin n) :
    flatteningB T y i l = ∑ j, T i j l * y j := rfl

@[simp] theorem flatteningA_apply {k : Type*} [CommSemiring k] {n : ℕ}
    (T : Tensor3 k n) (x : Fin n → k) (j l : Fin n) :
    flatteningA T x j l = ∑ i, T i j l * x i := rfl

/-- The `l`-th `C`-slice of a 3-tensor, `X ↦ (i j ↦ X i j l)`, as a
linear map `A⊗B⊗C → A⊗B`. A subspace `E ≤ A⊗B` induces
`E⊗C = ⨅ l, comap (sliceC l) E` inside `A⊗B⊗C`. -/
def sliceC {k : Type*} [CommSemiring k] {n : ℕ} (l : Fin n) :
    Tensor3 k n →ₗ[k] (Fin n → Fin n → k) where
  toFun X := fun i j => X i j l
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The `j`-th `B`-slice of a 3-tensor, `X ↦ (i l ↦ X i j l)`, as a
linear map `A⊗B⊗C → A⊗C`. -/
def sliceB {k : Type*} [CommSemiring k] {n : ℕ} (j : Fin n) :
    Tensor3 k n →ₗ[k] (Fin n → Fin n → k) where
  toFun X := fun i l => X i j l
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The `i`-th `A`-slice of a 3-tensor, `X ↦ (j l ↦ X i j l)`, as a
linear map `A⊗B⊗C → B⊗C`. -/
def sliceA {k : Type*} [CommSemiring k] {n : ℕ} (i : Fin n) :
    Tensor3 k n →ₗ[k] (Fin n → Fin n → k) where
  toFun X := fun j l => X i j l
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem sliceC_apply {k : Type*} [CommSemiring k] {n : ℕ}
    (l : Fin n) (X : Tensor3 k n) (i j : Fin n) : sliceC l X i j = X i j l := rfl

@[simp] theorem sliceB_apply {k : Type*} [CommSemiring k] {n : ℕ}
    (j : Fin n) (X : Tensor3 k n) (i l : Fin n) : sliceB j X i l = X i j l := rfl

@[simp] theorem sliceA_apply {k : Type*} [CommSemiring k] {n : ℕ}
    (i : Fin n) (X : Tensor3 k n) (j l : Fin n) : sliceA i X j l = X i j l := rfl

/-- Uncurrying `entries` as a linear map `A⊗B⊗C → (EntryIndex n → k)`.
Used to transport linear independence between the curried simple
tensors (where the slice geometry lives) and the uncurried ones (where
the perturbation-lemma minors and the evaluation points live). -/
def entriesLinear (k : Type*) [CommSemiring k] (n : ℕ) :
    Tensor3 k n →ₗ[k] (EntryIndex n → k) where
  toFun := entries
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem entriesLinear_apply {k : Type*} [CommSemiring k] {n : ℕ}
    (X : Tensor3 k n) : entriesLinear k n X = entries X := rfl

/-! ## 2. Ambient dimensions -/

theorem finrank_matrixSpace (k : Type*) [Field k] (n : ℕ) :
    Module.finrank k (Fin n → Fin n → k) = n * n := by
  simp [Module.finrank_pi_fintype]

theorem finrank_tensor3 (k : Type*) [Field k] (n : ℕ) :
    Module.finrank k (Tensor3 k n) = n * (n * n) := by
  simp [Module.finrank_pi_fintype]

/-! ## 3. The (111) candidate condition (dual form) and its locus -/

/-- `Candidate111 T r` : the *modeled* (111) border-apolarity candidate
condition, in the dual form of CHL Prop 3.1 eq (7) [arXiv:1911.07981]
with BB's min-truncated Hilbert function [arXiv:1910.01944, Thm 1.2].

There exist subspaces `EAB ⊆ A⊗B`, `EAC ⊆ A⊗C`, `EBC ⊆ B⊗C` (all three
ambient spaces are `Fin n → Fin n → k` here), each of dimension exactly
`min r n²`, containing the corresponding flattening image `T(C*)`,
`T(B*)`, `T(A*)`, such that the triple intersection
`(EAB⊗C) ∩ (EAC⊗B) ∩ (EBC⊗A)` inside `A⊗B⊗C` — implemented as the meet
of slicewise comaps — has dimension at least `min r n³`.

Correspondence with CHL §3 step (iii): `EAB = F110^⊥` etc., and the
(111) test "the image of `F110⊗C* ⊕ F101⊗B* ⊕ F011⊗A* → A*⊗B*⊗C*`
(eq (4)) has codimension ≥ r" is equivalent to "the triple intersection
of the perps has dimension ≥ r" (CHL Prop 3.1, eq (7)). The
exact-dimension conditions are CHL §2.3 (ii) (`codim I_ijk = r` for
total degree > 1, at the three degrees the (111) test sees),
min-truncated per BB Thm 1.2 (`h_r(D) = min(r, dim S_D)`) so that
degenerate parameters (`r > n²`) stay well-posed. Containment in the
annihilator (CHL §2.3 (i)) is the dual containment `T(C*) ⊆ EAB` etc.

What is checked and what is NOT: see the MODELED SCOPE note in this
file's header — the (210)/(120)-family pre-tests, degree-(100) pieces,
higher degrees, ideal extendability, Borel-fixedness (a WLOG for CHL's
search-side finiteness only), and smoothability are all deliberately
omitted; every omission RELAXES the condition. -/
def Candidate111 {k : Type*} [Field k] {n : ℕ} (T : Tensor3 k n) (r : ℕ) : Prop :=
  ∃ EAB EAC EBC : Submodule k (Fin n → Fin n → k),
    LinearMap.range (flatteningC T) ≤ EAB ∧
    LinearMap.range (flatteningB T) ≤ EAC ∧
    LinearMap.range (flatteningA T) ≤ EBC ∧
    Module.finrank k EAB = min r (n * n) ∧
    Module.finrank k EAC = min r (n * n) ∧
    Module.finrank k EBC = min r (n * n) ∧
    min r (n * (n * n)) ≤ Module.finrank k
      ↥((⨅ l, EAB.comap (sliceC l)) ⊓ (⨅ j, EAC.comap (sliceB j)) ⊓
        (⨅ i, EBC.comap (sliceA i)))

/-- The (111) accept locus: the set of entry vectors of tensors passing
the modeled (111) candidate search — the exact analogue of `rankLocus`
(BorderRank.lean), as a subset of the point space
`EntryIndex n → k` that `MvPolynomial.vanishingIdeal` consumes. -/
def test111Locus (k : Type*) [Field k] (n r : ℕ) : Set (EntryIndex n → k) :=
  {x | ∃ T : Tensor3 k n, Candidate111 T r ∧ x = entries T}

theorem mem_test111Locus {k : Type*} [Field k] {n r : ℕ} {x : EntryIndex n → k} :
    x ∈ test111Locus k n r ↔ ∃ T : Tensor3 k n, Candidate111 T r ∧ x = entries T :=
  Iff.rfl

/-! ## 4. A finrank extension helper

Mathlib has `exists_linearIndependent_of_le_finrank` (a free family of
any size up to the dimension) but no "extend a submodule to one of any
prescribed intermediate finrank"; this supplies it. -/

/-- Any submodule of a finite-dimensional space extends to a submodule
of any prescribed finrank between its own finrank and the ambient one. -/
theorem exists_superset_finrank_eq {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] {M : Submodule k V} {d : ℕ}
    (h1 : Module.finrank k M ≤ d) (h2 : d ≤ Module.finrank k V) :
    ∃ E : Submodule k V, M ≤ E ∧ Module.finrank k E = d := by
  obtain ⟨g, hg⟩ := exists_linearIndependent_of_le_finrank
    (R := k) (M := V ⧸ M) (n := d - Module.finrank k M)
    (by have := Submodule.finrank_quotient_add_finrank M; omega)
  set S : Submodule k (V ⧸ M) := Submodule.span k (Set.range g) with hS
  have hME : M ≤ S.comap M.mkQ := fun x hx => by
    simp only [Submodule.mem_comap, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero M).mpr hx]
    exact S.zero_mem
  refine ⟨S.comap M.mkQ, hME, ?_⟩
  · have hker : LinearMap.ker (M.mkQ.domRestrict (S.comap M.mkQ)) =
        M.comap (S.comap M.mkQ).subtype := by
      rw [LinearMap.ker_domRestrict, Submodule.ker_mkQ]
    have hrange : LinearMap.range (M.mkQ.domRestrict (S.comap M.mkQ)) = S := by
      have hcomp : M.mkQ.domRestrict (S.comap M.mkQ) =
          M.mkQ.comp (S.comap M.mkQ).subtype := rfl
      rw [hcomp, LinearMap.range_comp, Submodule.range_subtype,
        Submodule.map_comap_eq, Submodule.range_mkQ, top_inf_eq]
    have hrn := LinearMap.finrank_range_add_finrank_ker
      (M.mkQ.domRestrict (S.comap M.mkQ))
    rw [hrange, hker] at hrn
    have hkerrk : Module.finrank k (M.comap (S.comap M.mkQ).subtype) =
        Module.finrank k M := (Submodule.comapSubtypeEquivOfLe hME).finrank_eq
    have hSrk : Module.finrank k S = d - Module.finrank k M := by
      rw [hS, finrank_span_eq_card hg, Fintype.card_fin]
    omega

/-! ## 5. Lemma A-spread

A tensor with a SPREAD decomposition — `r` simple tensors that are
linearly independent — satisfies the (111) candidate condition. This is
the witness-producing heart of soundness: take each `E` to be an
extension of the span of the corresponding projected simple tensors,
and observe that the simple tensors themselves lie in the triple
intersection (slicewise membership), which therefore has dimension
≥ r = min r n³.

Per the WP-B review (MINOR-4) the independence hypothesis is stated on
the UNCURRIED simple tensors `x ↦ a s x.1 * b s x.2.1 * c s x.2.2`
(elements of `EntryIndex n → k`, where the perturbation minors and the
evaluation points also live); `entriesLinear` transports it to the
curried side. -/

private theorem range_flatteningC_le_span {k : Type*} [Field k] {n r : ℕ}
    (a b c : Fin r → Fin n → k) :
    LinearMap.range (flatteningC (fun i j l => ∑ s, a s i * b s j * c s l)) ≤
      Submodule.span k (Set.range fun s => (fun i j => a s i * b s j : Fin n → Fin n → k)) := by
  rintro _ ⟨z, rfl⟩
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun s => ∑ l, c s l * z l, ?_⟩
  funext i j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, flatteningC_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun l _ => by ring

private theorem range_flatteningB_le_span {k : Type*} [Field k] {n r : ℕ}
    (a b c : Fin r → Fin n → k) :
    LinearMap.range (flatteningB (fun i j l => ∑ s, a s i * b s j * c s l)) ≤
      Submodule.span k (Set.range fun s => (fun i l => a s i * c s l : Fin n → Fin n → k)) := by
  rintro _ ⟨y, rfl⟩
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun s => ∑ j, b s j * y j, ?_⟩
  funext i l
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, flatteningB_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun j _ => by ring

private theorem range_flatteningA_le_span {k : Type*} [Field k] {n r : ℕ}
    (a b c : Fin r → Fin n → k) :
    LinearMap.range (flatteningA (fun i j l => ∑ s, a s i * b s j * c s l)) ≤
      Submodule.span k (Set.range fun s => (fun j l => b s j * c s l : Fin n → Fin n → k)) := by
  rintro _ ⟨x, rfl⟩
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun s => ∑ i, a s i * x i, ?_⟩
  funext j l
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, flatteningA_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by ring

/-- **Lemma A-spread.** If `T = ∑_{s<r} a_s⊗b_s⊗c_s` with the simple
tensors linearly independent (as uncurried vectors of
`EntryIndex n → k`), then `T` satisfies the modeled (111) candidate
condition at rank `r`. Any field. -/
theorem candidate111_of_linearIndependent {k : Type*} [Field k] {n r : ℕ}
    {a b c : Fin r → Fin n → k}
    (h : LinearIndependent k fun s => (fun x : EntryIndex n =>
      a s x.1 * b s x.2.1 * c s x.2.2)) :
    Candidate111 (fun i j l => ∑ s, a s i * b s j * c s l) r := by
  -- transport independence to the curried simple tensors
  have hw : LinearIndependent k
      (fun s => (fun i j l => a s i * b s j * c s l : Tensor3 k n)) := by
    apply LinearIndependent.of_comp (entriesLinear k n)
    exact h
  -- extend the three projected spans to exact dimension min r n²
  have hext : ∀ m : Fin r → (Fin n → Fin n → k),
      ∃ E, Submodule.span k (Set.range m) ≤ E ∧
        Module.finrank k E = min r (n * n) := fun m =>
    exists_superset_finrank_eq
      (le_min
        ((finrank_range_le_card _).trans_eq (Fintype.card_fin r))
        ((Submodule.finrank_le _).trans_eq (finrank_matrixSpace k n)))
      ((min_le_right _ _).trans_eq (finrank_matrixSpace k n).symm)
  obtain ⟨EAB, hEAB_le, hEAB_rk⟩ :=
    hext fun s => (fun i j => a s i * b s j : Fin n → Fin n → k)
  obtain ⟨EAC, hEAC_le, hEAC_rk⟩ :=
    hext fun s => (fun i l => a s i * c s l : Fin n → Fin n → k)
  obtain ⟨EBC, hEBC_le, hEBC_rk⟩ :=
    hext fun s => (fun j l => b s j * c s l : Fin n → Fin n → k)
  refine ⟨EAB, EAC, EBC,
    (range_flatteningC_le_span a b c).trans hEAB_le,
    (range_flatteningB_le_span a b c).trans hEAC_le,
    (range_flatteningA_le_span a b c).trans hEBC_le,
    hEAB_rk, hEAC_rk, hEBC_rk, ?_⟩
  -- the simple tensors lie in the triple intersection
  have hspan_le : Submodule.span k
      (Set.range fun s => (fun i j l => a s i * b s j * c s l : Tensor3 k n)) ≤
      (⨅ l, EAB.comap (sliceC l)) ⊓ (⨅ j, EAC.comap (sliceB j)) ⊓
        (⨅ i, EBC.comap (sliceA i)) := by
    rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · refine (Submodule.mem_iInf _).mpr fun l => Submodule.mem_comap.mpr ?_
      have hsl : sliceC l (fun i j l' => a s i * b s j * c s l' : Tensor3 k n) =
          c s l • (fun i j => a s i * b s j : Fin n → Fin n → k) := by
        funext i j
        simp only [sliceC_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hsl]
      exact EAB.smul_mem _ (hEAB_le (Submodule.subset_span ⟨s, rfl⟩))
    · refine (Submodule.mem_iInf _).mpr fun j => Submodule.mem_comap.mpr ?_
      have hsl : sliceB j (fun i j' l => a s i * b s j' * c s l : Tensor3 k n) =
          b s j • (fun i l => a s i * c s l : Fin n → Fin n → k) := by
        funext i l
        simp only [sliceB_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hsl]
      exact EAC.smul_mem _ (hEAC_le (Submodule.subset_span ⟨s, rfl⟩))
    · refine (Submodule.mem_iInf _).mpr fun i => Submodule.mem_comap.mpr ?_
      have hsl : sliceA i (fun i' j l => a s i' * b s j * c s l : Tensor3 k n) =
          a s i • (fun j l => b s j * c s l : Fin n → Fin n → k) := by
        funext j l
        simp only [sliceA_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hsl]
      exact EBC.smul_mem _ (hEBC_le (Submodule.subset_span ⟨s, rfl⟩))
  calc min r (n * (n * n)) ≤ r := min_le_left _ _
    _ = Module.finrank k (Submodule.span k
        (Set.range fun s => (fun i j l => a s i * b s j * c s l : Tensor3 k n))) := by
        rw [finrank_span_eq_card hw, Fintype.card_fin]
    _ ≤ _ := Submodule.finrank_mono hspan_le

/-! ## 6. The degenerate band -/

/-- For `n² ≤ r` EVERY tensor satisfies the modeled (111) candidate
condition: take all three subspaces to be `⊤` (dimension
`n² = min r n²`); the triple intersection is everything (dimension
`n³ ≥ min r n³`). This is the honest degenerate-parameter behaviour of
the min-truncated Hilbert function — the test says nothing at huge
ranks. See the CONTENT WINDOW note in the file header: vacuity in fact
begins at `r ≈ (2/3)n²` (not formalized); this band suffices for the
soundness case split and for the documented `DecidedByVP` degeneracy. -/
theorem candidate111_of_sq_le {k : Type*} [Field k] {n r : ℕ} (hr : n * n ≤ r)
    (T : Tensor3 k n) : Candidate111 T r := by
  have htop : Module.finrank k (⊤ : Submodule k (Fin n → Fin n → k)) = min r (n * n) := by
    rw [finrank_top, finrank_matrixSpace, min_eq_right hr]
  refine ⟨⊤, ⊤, ⊤, le_top, le_top, le_top, htop, htop, htop, ?_⟩
  have htop3 : ((⨅ l, (⊤ : Submodule k (Fin n → Fin n → k)).comap (sliceC l)) ⊓
      (⨅ j, (⊤ : Submodule k (Fin n → Fin n → k)).comap (sliceB j)) ⊓
      (⨅ i, (⊤ : Submodule k (Fin n → Fin n → k)).comap (sliceA i))) = ⊤ := by
    rw [eq_top_iff]
    refine le_inf (le_inf (le_iInf fun l => ?_) (le_iInf fun j => ?_))
      (le_iInf fun i => ?_) <;> simp [Submodule.comap_top]
  rw [htop3, finrank_top, finrank_tensor3]
  exact min_le_right _ _

/-! ## 7. The perturbation lemma and the soundness core

`vanishingIdeal_test111Locus_le` : every polynomial vanishing on the
(111) accept locus vanishes on the whole rank-≤ r locus. For `r ≥ n²`
this is pointwise (§6). For `r < n²`, given an arbitrary decomposition
`T = ∑ a_s⊗b_s⊗c_s`, interpolate each vector linearly towards a spread
reference configuration (`r` distinct standard basis tensors — they
exist since `r < n² ≤ n³`). The `r × r` matrix of the moving simple
tensors' entries at the reference indices has polynomial entries and
determinant 1 at time 1, so its determinant is a nonzero polynomial;
off its finitely many roots the configuration is spread, hence in the
accept locus by Lemma A-spread, hence kills `p`. The univariate
polynomial `t ↦ p(entries T_t)` therefore has infinitely many roots
(`k` infinite), so it is zero; its value at `t = 0` is `p(entries T)`. -/

/-- The straight line `t ↦ u + t·(v − u)` from `u` (at `t = 0`) to `v`
(at `t = 1`), as a univariate polynomial. -/
noncomputable def linePoly {k : Type*} [CommRing k] (u v : k) : Polynomial k :=
  Polynomial.C u + Polynomial.C (v - u) * Polynomial.X

theorem linePoly_eval {k : Type*} [CommRing k] (u v t : k) :
    (linePoly u v).eval t = u + (v - u) * t := by
  simp [linePoly]

theorem linePoly_eval_zero {k : Type*} [CommRing k] (u v : k) :
    (linePoly u v).eval 0 = u := by
  simp [linePoly]

theorem linePoly_eval_one {k : Type*} [CommRing k] (u v : k) :
    (linePoly u v).eval 1 = v := by
  simp [linePoly]

/-- Perturbation core: over an infinite field, a polynomial vanishing on
the (111) accept locus vanishes at the entry vector of every tensor
given with a rank-≤ r decomposition, provided `r < n²` (the case
`n² ≤ r` is handled pointwise by `candidate111_of_sq_le`). -/
private theorem aeval_eq_zero_of_lt_sq {k : Type*} [Field k] [Infinite k] {n r : ℕ}
    (hr : r < n * n) (a b c : Fin r → Fin n → k)
    {p : MvPolynomial (EntryIndex n) k}
    (hp : ∀ x ∈ test111Locus k n r, MvPolynomial.aeval x p = 0) :
    MvPolynomial.aeval (entries fun i j l => ∑ s, a s i * b s j * c s l) p = 0 := by
  -- n ≥ 1 (otherwise r < 0)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact absurd hr (by simp)
  -- an injection of the r summands into the n³ entry indices
  obtain ⟨ι⟩ : Nonempty (Fin r ↪ EntryIndex n) := by
    apply Function.Embedding.nonempty_of_card_le
    simp only [Fintype.card_fin, Fintype.card_prod]
    exact hr.le.trans (Nat.le_mul_of_pos_left _ hn)
  -- entrywise interpolation from the given decomposition (t = 0) to the
  -- spread reference configuration e_{ι s} (t = 1)
  set pa : Fin r → Fin n → Polynomial k :=
    fun s i => linePoly (a s i) (if (ι s).1 = i then 1 else 0) with hpa
  set pb : Fin r → Fin n → Polynomial k :=
    fun s j => linePoly (b s j) (if (ι s).2.1 = j then 1 else 0) with hpb
  set pc : Fin r → Fin n → Polynomial k :=
    fun s l => linePoly (c s l) (if (ι s).2.2 = l then 1 else 0) with hpc
  -- the spreadness detector: the ι-indexed minor of the moving simple tensors
  set N : Matrix (Fin r) (Fin r) (Polynomial k) :=
    Matrix.of fun s s' => pa s (ι s').1 * pb s (ι s').2.1 * pc s (ι s').2.2 with hN
  have hdet_map : ∀ t : k, (N.det).eval t = (N.map (Polynomial.eval t)).det := by
    intro t
    have h := RingHom.map_det (Polynomial.evalRingHom t) N
    simpa [RingHom.mapMatrix_apply, Polynomial.coe_evalRingHom] using h
  -- at t = 1 the detector matrix is the identity
  have hN1 : N.map (Polynomial.eval 1) = 1 := by
    ext s s'
    simp only [Matrix.map_apply, hN, Matrix.of_apply, hpa, hpb, hpc,
      Polynomial.eval_mul, linePoly_eval_one]
    by_cases hss : s = s'
    · subst hss
      simp
    · rw [Matrix.one_apply_ne hss]
      by_cases h1 : (ι s).1 = (ι s').1
      · by_cases h2 : (ι s).2.1 = (ι s').2.1
        · by_cases h3 : (ι s).2.2 = (ι s').2.2
          · exact absurd (ι.injective (Prod.ext h1 (Prod.ext h2 h3))) hss
          · simp [h3]
        · simp [h2]
      · simp [h1]
  have hNdet : N.det ≠ 0 := by
    intro h0
    have h1 : (N.det).eval 1 = 1 := by rw [hdet_map, hN1, Matrix.det_one]
    rw [h0] at h1
    simp at h1
  -- the substituted univariate polynomial q(t) = p(entries T_t)
  set P : EntryIndex n → Polynomial k :=
    fun x => ∑ s, pa s x.1 * pb s x.2.1 * pc s x.2.2 with hP
  set q : Polynomial k := MvPolynomial.aeval P p with hq
  have hqeval : ∀ t : k, q.eval t = MvPolynomial.eval (fun x => (P x).eval t) p := by
    intro t
    have h := MvPolynomial.comp_aeval_apply (φ := Polynomial.aeval t) (f := P) (p := p)
    simpa [Polynomial.coe_aeval_eq_eval, MvPolynomial.aeval_eq_eval] using h
  -- off the detector's roots the configuration is spread, so q vanishes
  have hqzero : ∀ t : k, ¬ (N.det).IsRoot t → q.IsRoot t := by
    intro t ht
    have hdt : (N.map (Polynomial.eval t)).det ≠ 0 := by
      rw [← hdet_map]
      exact ht
    have hrows := Matrix.linearIndependent_rows_of_det_ne_zero hdt
    have hindep : LinearIndependent k (fun s => (fun x : EntryIndex n =>
        (pa s x.1).eval t * (pb s x.2.1).eval t * (pc s x.2.2).eval t)) := by
      apply LinearIndependent.of_comp (LinearMap.funLeft k k ι)
      have hEq : (⇑(LinearMap.funLeft k k ⇑ι) ∘ fun s => (fun x : EntryIndex n =>
          (pa s x.1).eval t * (pb s x.2.1).eval t * (pc s x.2.2).eval t)) =
          fun s => (N.map (Polynomial.eval t)) s := by
        funext s s'
        simp [LinearMap.funLeft_apply, hN, Polynomial.eval_mul]
      rw [hEq]
      exact hrows
    have hcand := candidate111_of_linearIndependent
      (a := fun s i => (pa s i).eval t) (b := fun s j => (pb s j).eval t)
      (c := fun s l => (pc s l).eval t) hindep
    have hmem : (fun x : EntryIndex n => (P x).eval t) ∈ test111Locus k n r := by
      refine ⟨fun i j l => ∑ s, (pa s i).eval t * (pb s j).eval t * (pc s l).eval t,
        hcand, ?_⟩
      funext x
      simp [hP, entries, Polynomial.eval_finsetSum]
    have hz := hp _ hmem
    show q.eval t = 0
    rw [hqeval t]
    simpa [MvPolynomial.aeval_eq_eval] using hz
  -- infinitely many roots kill q
  have hq0 : q = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot q
      (((Polynomial.finite_setOfPred_isRoot hNdet).infinite_compl).mono
        (by simpa [Set.compl_ofPred] using fun t ht => hqzero t ht))
  -- evaluate the vanishing at t = 0
  have h0 : (fun x : EntryIndex n => (P x).eval 0) =
      entries (fun i j l => ∑ s, a s i * b s j * c s l) := by
    funext x
    simp [hP, hpa, hpb, hpc, entries, Polynomial.eval_finsetSum, linePoly_eval_zero]
  have hfinal := hqeval 0
  rw [hq0, h0] at hfinal
  simp only [Polynomial.eval_zero] at hfinal
  simpa [MvPolynomial.aeval_eq_eval] using hfinal.symm

/-- **Soundness core.** Over an infinite field, every polynomial
vanishing on the (111) accept locus vanishes on the rank-≤ r locus:
`vanishingIdeal (test111Locus) ≤ vanishingIdeal (rankLocus)`. Combined
with `zeroLocus` antitonicity this yields
`passes111_of_borderRankLE` (Vp2.lean).

`[Infinite k]` is genuinely used (the perturbation line needs more
parameter values than the detector's roots); see the FIELD SCOPE note
in the file header for why the finite case is out of the sources'
scope and left unclaimed. -/
theorem vanishingIdeal_test111Locus_le {k : Type*} [Field k] [Infinite k] {n r : ℕ} :
    MvPolynomial.vanishingIdeal k (test111Locus k n r) ≤
      MvPolynomial.vanishingIdeal k (rankLocus k n r) := by
  intro p hp
  rw [MvPolynomial.mem_vanishingIdeal_iff] at hp ⊢
  rintro x ⟨T, ⟨a, b, c, rfl⟩, rfl⟩
  rcases Nat.lt_or_ge r (n * n) with hr | hr
  · exact aeval_eq_zero_of_lt_sq hr a b c hp
  · exact hp _ ⟨_, candidate111_of_sq_le hr _, rfl⟩

end Vp2
