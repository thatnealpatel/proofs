/-
  Scratch/CommutingPairsEuler — a complete, sorry-free proof of the
  OEIS A061256 annotation on commuting pairs in symmetric
  groups: the number of orbits of `{(g, h) ∈ Sₙ × Sₙ : gh = hg}` under
  simultaneous conjugation equals the Euler transform of σ at `n`
  (`commPairClassCount_perm`, at the bottom of this file).

  Ground truth (re-pinned from `oeis show A061256`, 2026-08-19):

    A061256: "Euler transform of sigma(n), cf. A000203."
    terms: 1, 1, 4, 8, 21, 39, 92, 170, 360, 667, 1316, …
    comment: "According to a message on a blog page by 'Allan' (see Secret
    Blogging Seminar link) it appears that a(n) = number of conjugacy classes
    of commutative ordered pairs in Symm(n)."

  Provenance correction vs. the campaign card
  (`Formalize/A061256-adams-watters.md`): the ordered-PAIRS claim is recorded
  in the entry as a blog comment by "Allan", not as a statement by Franklin T.
  Adams-Watters; Adams-Watters conjectured the commuting-TRIPLES statement
  (a(n) = |{(f,g,h) : all commute}| / n!), which J. R. Britnell proved in 2012.
  The pairs annotation ("it appears") is still recorded in hedged form on the
  entry, but the FACT is not open: it is the genus-1 case of
  Liskovets–Mednykh (2009) — stated explicitly as A061256 on p. 49/53 of
  Mednykh's lecture slides, a link the OEIS entry itself carries (local copy:
  References/EnumerationMapPresentation/paper.txt) — and it also follows from
  Britnell's displayed equation T(G)/|G| = Σ k(C_G(g_i)) by Burnside's lemma
  in one step.  What this file contributes is an independent, self-contained,
  machine-checked proof importing neither.

  Novelty tier: KNOWN (published; the OEIS comment is merely stale).  The
  ingredient map: orbits of commuting pairs under simultaneous conjugation
  are isomorphism classes of ℤ²-actions on an n-point set, equivalently
  degree-n covers of the torus (standard covering theory); transitive
  ℤ²-sets of size d are index-d subgroups of ℤ², counted by σ(d) via Hermite
  normal form (Tad White, arXiv:1304.2830, Lemma 2 at r = 2 — local copy at
  References/arXiv-1304-2830/EulerTransformPaper.tex; White's §3 exponential
  formula, for which he cites Lubotzky, "Counting finite index subgroups",
  Prop. 1.10, counts LABELED actions — the unlabeled multiset assembly used
  here is the content of Liskovets–Mednykh's Euler-transform relation, Ars
  Math. Contemp. 2009, presented as Theorem 11 in Mednykh's slides; journal
  numbering unverified); Bryan–Fulman, arXiv:math/9712248, Theorem 1, has
  the m-tuple generating function.  This file is a machine-checked proof
  unified in one formal development — we found no record of a prior
  formalization (corpora: Mathlib/.lake packages by grep, 2026-08-20; a
  wider assistant/web sweep was NOT completed, so no "first" is claimed) —
  and NOT a first proof of the mathematical fact.  The proof is complete:
  the file compiles
  with no `sorry`, no `admit`, no `axiom`, no `native_decide`, and
  `#print axioms` on every theorem reports a subset of
  `{propext, Classical.choice, Quot.sound}`.  Structure:

  * `a061256`, a division-free computable Euler-transform-of-σ, pinned to the
    11 leading OEIS terms by kernel `decide`;
  * `commPairs`/`commPairClassCount`, the orbit count of commuting pairs under
    simultaneous conjugation (via Mathlib's `ConjAct` and `orbitRel`), and the
    reduction `z2RepsEquivCommPairOrbits` identifying those orbits with
    conjugacy classes of monoid homs `Multiplicative (ℤ × ℤ) →* G`, i.e. iso
    classes of ℤ²-actions;
  * K1 (`card_addSubgroup_index_eq_sigma1`): index-`d` subgroups of ℤ² number
    σ(d), by an explicit Hermite-normal-form bijection with index computed by
    `Submodule.natAbs_det_equiv`;
  * K3 (`card_weightedMS`): weight-`n` multisets of finite-index subgroups
    are counted by the Euler coefficient recursion, by induction on the
    largest allowed part with `Sym.card_sym_eq_multichoose`;
  * K2 (`classifyOrbit_bijective`): the stabilizer-multiset invariant is a
    complete invariant — conjugation-invariant (transport along equivariant
    bijections), injective (the reassembly theorem
    `exists_equivariant_of_actionOrbitMultiset_eq`, via the canonical
    orbit/coset decomposition `quotDecompEquiv` and a fiberwise matching
    `exists_equiv_of_map_univ_eq`), and surjective (the coset model
    `ModelSpace`);
  * the assembled annotation `commPairClassCount_perm`, plus independent
    kernel-`decide` certificates for n = 0, 1, 2, 3, 4 as cross-checks
    (no `native_decide` anywhere, per the repo trust policy).
-/
import Mathlib
import GroupTPP.HigherCommProb

set_option autoImplicit false

open Equiv Function MulAction

namespace GroupCount.CommutingPairsEuler

/-! ### The Euler transform of σ (the OEIS side) -/

/-- Sum of divisors, `σ(n) = ∑_{d ∣ n} d`; computable and kernel-reducible. -/
def sigma1 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `sigma1` is Mathlib's `ArithmeticFunction.sigma 1`. -/
theorem sigma1_eq_sigma_one (n : ℕ) : sigma1 n = ArithmeticFunction.sigma 1 n :=
  (ArithmeticFunction.sigma_one_apply n).symm

example : sigma1 1 = 1 := by decide
example : sigma1 6 = 12 := by decide
example : sigma1 12 = 28 := by decide

/-- `eulerCoeff c d n` is the coefficient of `x^n` in `∏_{k=1}^{d} (1-x^k)^(-c k)`:
the number of multisets of total weight `n` built from parts of each size
`k ∈ [1, d]` available in `c k` colours.  The binomial factor
`(c k + m - 1).choose m` is `Nat.multichoose (c k) m` (see
`eulerCoeff_succ_multichoose`); the `choose` form is used so that the kernel
can reduce it (`Nat.multichoose` is compiled by well-founded recursion, which
`decide` cannot unfold).  For `d ≥ n` this is the `n`-th term of the Euler
transform of `c` in the OEIS sense. -/
def eulerCoeff (c : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, n => if n = 0 then 1 else 0
  | d + 1, n =>
    ∑ m ∈ Finset.range (n / (d + 1) + 1),
      (c (d + 1) + m - 1).choose m * eulerCoeff c d (n - (d + 1) * m)

/-- The recursion step of `eulerCoeff`, written with `Nat.multichoose`:
each part size contributes a multiset-coefficient factor. -/
theorem eulerCoeff_succ_multichoose (c : ℕ → ℕ) (d n : ℕ) :
    eulerCoeff c (d + 1) n =
      ∑ m ∈ Finset.range (n / (d + 1) + 1),
        Nat.multichoose (c (d + 1)) m * eulerCoeff c d (n - (d + 1) * m) := by
  simp only [eulerCoeff, Nat.multichoose_eq]

-- Euler transform of the all-ones sequence = partition numbers p(n).
example : eulerCoeff (fun _ => 1) 5 5 = 7 := by decide
example : eulerCoeff (fun _ => 1) 10 10 = 42 := by decide

/-- OEIS A061256, the Euler transform of σ: coefficient of `x^n` in
`∏_{k≥1} (1-x^k)^(-σ(k))` (parts of size greater than `n` cannot contribute,
so the product is truncated at `k = n`). -/
def a061256 (n : ℕ) : ℕ := eulerCoeff sigma1 n n

/-- Pin to the OEIS entry: the eleven leading terms of A061256. -/
example :
    (List.range 11).map a061256 =
      [1, 1, 4, 8, 21, 39, 92, 170, 360, 667, 1316] := by decide

/-! ### Commuting pairs under simultaneous conjugation (the group side) -/

/-- The set of commuting pairs `{(g, h) : g * h = h * g}` as a
conjugation-invariant sub-action of `G × G` under `ConjAct G`
(componentwise simultaneous conjugation). -/
def commPairs (G : Type*) [Group G] : SubMulAction (ConjAct G) (G × G) where
  carrier := {p | Commute p.1 p.2}
  smul_mem' := fun c _p hp => hp.map (MulAut.conj (ConjAct.ofConjAct c))

/-- Membership is exactly the commuting condition. -/
theorem mem_commPairs_iff {G : Type*} [Group G] (p : G × G) :
    p ∈ commPairs G ↔ Commute p.1 p.2 := Iff.rfl

/-- Decidable membership for permutation groups (needed for kernel `decide`). -/
instance decMemCommPairs (n : ℕ) :
    DecidablePred (· ∈ commPairs (Equiv.Perm (Fin n))) := fun p =>
  decidable_of_iff (p.1 * p.2 = p.2 * p.1) (commute_iff_eq p.1 p.2).symm

-- Ground truth: a commuting and a non-commuting pair in S₃.
example : ((Equiv.swap (0 : Fin 3) 1, Equiv.swap (0 : Fin 3) 1) :
    Perm (Fin 3) × Perm (Fin 3)) ∈ commPairs (Perm (Fin 3)) := by decide
example : ((Equiv.swap (0 : Fin 3) 1, Equiv.swap (1 : Fin 3) 2) :
    Perm (Fin 3) × Perm (Fin 3)) ∉ commPairs (Perm (Fin 3)) := by decide

-- Ground truth for the action: conjugating (swap 0 1, 1) by swap 1 2
-- relabels the transposition to swap 0 2.
example :
    (ConjAct.toConjAct (Equiv.swap (1 : Fin 3) 2)) •
        (⟨(Equiv.swap (0 : Fin 3) 1, 1), by decide⟩ : commPairs (Perm (Fin 3))) =
      ⟨(Equiv.swap (0 : Fin 3) 2, 1), by decide⟩ := by decide

/-- Bridge to `commTuples` from `GroupTPP/HigherCommProb`: commuting pairs are
the length-2 pairwise-commuting tuples. -/
def commPairsEquivCommTuplesTwo (G : Type*) [Group G] : commPairs G ≃ commTuples G 2 :=
  (Equiv.subtypeEquivRight fun _p => Iff.rfl).trans (commTuples_two_equiv G).symm

/-- Ground truth pinning which bijection `commPairsEquivCommTuplesTwo` is:
the pair maps to the tuple in coordinate order. -/
theorem commPairsEquivCommTuplesTwo_apply {G : Type*} [Group G] (p : commPairs G) :
    (commPairsEquivCommTuplesTwo G p).1 = ![(p : G × G).1, (p : G × G).2] := rfl

/-- The number of orbits of commuting pairs under simultaneous conjugation:
the quantity the OEIS annotation asserts to be `a061256 n` for
`G = Equiv.Perm (Fin n)`. -/
noncomputable def commPairClassCount (G : Type*) [Group G] : ℕ :=
  Nat.card (orbitRel.Quotient (ConjAct G) (commPairs G))

/-! ### ℤ²-representations: orbits of commuting pairs are conjugacy classes
of homs `ℤ² →* G` -/

/-- ℤ² written multiplicatively; homs `Z2 →* G` are ℤ²-representations,
and for `G = Equiv.Perm (Fin n)` they are ℤ²-actions on an `n`-point set. -/
abbrev Z2 : Type := Multiplicative (ℤ × ℤ)

/-- The first standard generator `(1, 0)` of ℤ². -/
def zGen1 : Z2 := Multiplicative.ofAdd (1, 0)

/-- The second standard generator `(0, 1)` of ℤ². -/
def zGen2 : Z2 := Multiplicative.ofAdd (0, 1)

-- Ground truth: the generators multiply coordinatewise and are distinct.
example : zGen1 * zGen2 = Multiplicative.ofAdd (1, 1) := rfl
example : zGen1 ≠ zGen2 := by decide

/-- Every element of ℤ² is the obvious word in the two generators. -/
theorem zGen_decomp (m : Z2) : zGen1 ^ m.toAdd.1 * zGen2 ^ m.toAdd.2 = m := by
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_zpow, zGen1, zGen2, toAdd_ofAdd, Prod.smul_mk, smul_eq_mul,
    mul_one, mul_zero, Prod.mk_add_mk, add_zero, zero_add]

variable {G : Type*} [Group G]

/-- Monoid homs `ℤ² →* G` are the same data as commuting pairs in `G`:
a hom is determined by the commuting images of the two generators, and any
commuting pair `(g, h)` induces the hom `(a, b) ↦ g^a * h^b`. -/
def homEquivCommPair : (Z2 →* G) ≃ commPairs G where
  toFun φ := ⟨(φ zGen1, φ zGen2), (show Commute zGen1 zGen2 from mul_comm _ _).map φ⟩
  invFun p :=
    { toFun := fun m => (p : G × G).1 ^ m.toAdd.1 * (p : G × G).2 ^ m.toAdd.2
      map_one' := by
        show (p : G × G).1 ^ (0 : ℤ) * (p : G × G).2 ^ (0 : ℤ) = 1
        rw [zpow_zero, zpow_zero, mul_one]
      map_mul' := fun m k => by
        have hc : Commute (p : G × G).1 (p : G × G).2 := p.2
        rw [toAdd_mul, Prod.fst_add, Prod.snd_add, zpow_add, zpow_add,
          (hc.zpow_zpow _ _).mul_mul_mul_comm] }
  left_inv φ := MonoidHom.ext fun m => by
    show φ zGen1 ^ m.toAdd.1 * φ zGen2 ^ m.toAdd.2 = φ m
    rw [← map_zpow, ← map_zpow, ← map_mul, zGen_decomp]
  right_inv p := by
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · show (p : G × G).1 ^ (1 : ℤ) * (p : G × G).2 ^ (0 : ℤ) = (p : G × G).1
      rw [zpow_one, zpow_zero, mul_one]
    · show (p : G × G).1 ^ (0 : ℤ) * (p : G × G).2 ^ (1 : ℤ) = (p : G × G).2
      rw [zpow_zero, zpow_one, one_mul]

/-- Ground truth pinning which bijection `homEquivCommPair` is: a hom maps to
the images of the two generators, in order. -/
theorem homEquivCommPair_apply (φ : Z2 →* G) :
    (homEquivCommPair φ : G × G) = (φ zGen1, φ zGen2) := rfl

/-- Conjugation action of `G` on homs `M →* G` by post-composition with the
inner automorphism, `(c • φ) m = c * φ m * c⁻¹` (pinned by
`homConjAction_smul_apply`).  For `G = Equiv.Perm X` an orbit of this action
is a permutation-representation of `M` on `X` up to relabelling of `X`, i.e.
an iso class of `M`-actions on the fixed carrier `X`. -/
scoped instance homConjAction {M : Type*} [Monoid M] : MulAction (ConjAct G) (M →* G) where
  smul c φ := (MulAut.conj (ConjAct.ofConjAct c)).toMonoidHom.comp φ
  one_smul φ := MonoidHom.ext fun m => by
    show ConjAct.ofConjAct (1 : ConjAct G) * φ m * (ConjAct.ofConjAct (1 : ConjAct G))⁻¹ = φ m
    rw [ConjAct.ofConjAct_one, one_mul, inv_one, mul_one]
  mul_smul c d φ := MonoidHom.ext fun m => by
    show ConjAct.ofConjAct (c * d) * φ m * (ConjAct.ofConjAct (c * d))⁻¹ =
      ConjAct.ofConjAct c * (ConjAct.ofConjAct d * φ m * (ConjAct.ofConjAct d)⁻¹) *
        (ConjAct.ofConjAct c)⁻¹
    rw [map_mul, mul_inv_rev]
    simp only [mul_assoc]

/-- The conjugation action on homs, unfolded. -/
theorem homConjAction_smul_apply {M : Type*} [Monoid M] (c : ConjAct G) (φ : M →* G) (m : M) :
    (c • φ) m = ConjAct.ofConjAct c * φ m * (ConjAct.ofConjAct c)⁻¹ := rfl

/-- `homEquivCommPair` intertwines conjugation of homs with simultaneous
conjugation of pairs. -/
theorem homEquivCommPair_smul (c : ConjAct G) (φ : Z2 →* G) :
    homEquivCommPair (c • φ) = c • homEquivCommPair φ := rfl

/-- An equivariant bijection induces a bijection of orbit spaces. -/
def orbitQuotientCongr {H α β : Type*} [Group H] [MulAction H α] [MulAction H β]
    (e : α ≃ β) (he : ∀ (g : H) (a : α), e (g • a) = g • e a) :
    orbitRel.Quotient H α ≃ orbitRel.Quotient H β := by
  refine Quotient.congr e (fun a b => ?_)
  rw [orbitRel_apply, orbitRel_apply, MulAction.mem_orbit_iff, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, (he g b).symm⟩
  · rintro ⟨g, hg⟩
    refine ⟨g, e.injective ?_⟩
    rw [he, hg]

/-- **Reduction.** Conjugacy classes of ℤ²-representations in `G` are exactly
the orbits of commuting pairs under simultaneous conjugation.  For
`G = Equiv.Perm (Fin n)` the left-hand side is the set of isomorphism classes
of ℤ²-actions on an `n`-point set — the object whose count is the Euler
transform of σ by the classical orbit/subgroup analysis. -/
def z2RepsEquivCommPairOrbits (G : Type*) [Group G] :
    orbitRel.Quotient (ConjAct G) (Z2 →* G) ≃ orbitRel.Quotient (ConjAct G) (commPairs G) :=
  orbitQuotientCongr homEquivCommPair (fun c φ => homEquivCommPair_smul c φ)

/-- `commPairClassCount` counts conjugacy classes of ℤ²-representations. -/
theorem commPairClassCount_eq_card_z2Reps (G : Type*) [Group G] :
    commPairClassCount G = Nat.card (orbitRel.Quotient (ConjAct G) (Z2 →* G)) :=
  (Nat.card_congr (z2RepsEquivCommPairOrbits G)).symm

/-! ### Degenerate-model sanity: abelian groups -/

/-- Over an abelian group conjugation is trivial on pairs. -/
theorem commPairs_smul_eq_self {A : Type*} [CommGroup A] (c : ConjAct A) (p : commPairs A) :
    c • p = p := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · show ConjAct.ofConjAct c * (p : A × A).1 * (ConjAct.ofConjAct c)⁻¹ = (p : A × A).1
    rw [mul_comm (ConjAct.ofConjAct c), mul_inv_cancel_right]
  · show ConjAct.ofConjAct c * (p : A × A).2 * (ConjAct.ofConjAct c)⁻¹ = (p : A × A).2
    rw [mul_comm (ConjAct.ofConjAct c), mul_inv_cancel_right]

/-- If a group action is trivial, the orbit space is the space itself. -/
def orbitQuotientEquivOfTrivial {H α : Type*} [Group H] [MulAction H α]
    (h : ∀ (g : H) (a : α), g • a = a) : orbitRel.Quotient H α ≃ α where
  toFun := Quotient.lift id (fun a b hab => by
    have hab' : a ∈ MulAction.orbit H b := hab
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hab'
    show a = b
    rw [← hg, h g b])
  invFun := Quotient.mk _
  left_inv q := Quotient.inductionOn q fun _a => rfl
  right_inv _a := rfl

/-- Non-vacuity witness at the opposite extreme from `Equiv.Perm`: for an
abelian group every pair commutes and every orbit is a singleton, so the class
count is `|A|²`.  (Consistent with the `n = 2` certificate below: `S₂` is
abelian of order 2 and `a061256 2 = 4`.  For infinite `A` both sides are `0`
by the `Nat.card` junk-value convention; the content is at finite `A`, as
instantiated at `Multiplicative (ZMod 3)` below.) -/
theorem commPairClassCount_commGroup (A : Type*) [CommGroup A] :
    commPairClassCount A = Nat.card A * Nat.card A := by
  let e : orbitRel.Quotient (ConjAct A) (commPairs A) ≃ A × A :=
    (orbitQuotientEquivOfTrivial commPairs_smul_eq_self).trans
      (Equiv.subtypeUnivEquiv fun p => mul_comm p.1 p.2)
  rw [commPairClassCount, Nat.card_congr e, Nat.card_prod]

example : commPairClassCount (Multiplicative (ZMod 3)) = 9 := by
  rw [commPairClassCount_commGroup, Nat.card_eq_fintype_card]
  decide

/-! ### Kernel-certified instances of the annotation, `n ≤ 4`

All certificates go through kernel `decide` on computable `Fintype` instances;
no `native_decide` (repo trust policy, cf. `GroupCount/Gnu.lean`). -/

/-- The simultaneous-conjugation orbit relation on commuting pairs of
permutations is decidable by finite search over the conjugators. -/
instance orbitRelDecidable (n : ℕ) :
    DecidableRel (orbitRel (ConjAct (Equiv.Perm (Fin n)))
      (commPairs (Equiv.Perm (Fin n)))).r := fun p q =>
  decidable_of_iff (∃ c : ConjAct (Equiv.Perm (Fin n)), c • q = p)
    MulAction.mem_orbit_iff.symm

/-- Computable `Fintype` structure on the orbit space, for kernel evaluation. -/
instance quotFintype (n : ℕ) :
    Fintype (orbitRel.Quotient (ConjAct (Equiv.Perm (Fin n)))
      (commPairs (Equiv.Perm (Fin n)))) :=
  @Quotient.fintype _ _ (orbitRel _ _) (orbitRelDecidable n)

/-- The annotation at `n = 0`: one (empty) pair, `a061256 0 = 1`. -/
theorem commPairClassCount_perm_zero :
    commPairClassCount (Equiv.Perm (Fin 0)) = a061256 0 :=
  (@Nat.card_eq_fintype_card _ (quotFintype 0)).trans (by decide)

/-- The annotation at `n = 1`. -/
theorem commPairClassCount_perm_one :
    commPairClassCount (Equiv.Perm (Fin 1)) = a061256 1 :=
  (@Nat.card_eq_fintype_card _ (quotFintype 1)).trans (by decide)

/-- The annotation at `n = 2`: `S₂` abelian, all 4 pairs, `a061256 2 = 4`. -/
theorem commPairClassCount_perm_two :
    commPairClassCount (Equiv.Perm (Fin 2)) = a061256 2 :=
  (@Nat.card_eq_fintype_card _ (quotFintype 2)).trans (by decide)

/-- The annotation at `n = 3`: 18 commuting pairs in `S₃` fall into
`a061256 3 = 8` classes. -/
theorem commPairClassCount_perm_three :
    commPairClassCount (Equiv.Perm (Fin 3)) = a061256 3 :=
  (@Nat.card_eq_fintype_card _ (quotFintype 3)).trans (by decide)

set_option maxRecDepth 40000 in
/-- The annotation at `n = 4`: 120 commuting pairs in `S₄` fall into
`a061256 4 = 21` classes.  Kernel-only `decide` (≈ 15 s of kernel reduction;
`maxRecDepth` raised for the deep `Finset` dedup). -/
theorem commPairClassCount_perm_four :
    commPairClassCount (Equiv.Perm (Fin 4)) = a061256 4 :=
  (@Nat.card_eq_fintype_card _ (quotFintype 4)).trans (by decide +kernel)

/-! ### K1: Hermite normal form — index-`d` subgroups of ℤ² number σ(d)

`hnfSubgroup a b c` is the sublattice with basis rows `(a, b)` and `(0, c)`;
White (arXiv:1304.2830), Lemma 2 at `r = 2`. -/

/-- The ℤ-linear map with column images `(a, b)` and `(0, c)`:
`(k, l) ↦ (k*a, k*b + l*c)`.  Its range is the HNF sublattice. -/
def hnfMap (a b c : ℤ) : (ℤ × ℤ) →ₗ[ℤ] (ℤ × ℤ) where
  toFun p := (p.1 * a, p.1 * b + p.2 * c)
  map_add' p q := by
    ext
    · simp only [Prod.fst_add, add_mul]
    · simp only [Prod.fst_add, Prod.snd_add, add_mul]
      ring
  map_smul' m p := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply] <;> ring

/-- The subgroup of ℤ² generated by the Hermite-normal-form rows `(a, b)`
and `(0, c)`. -/
def hnfSubgroup (a b c : ℤ) : AddSubgroup (ℤ × ℤ) :=
  (LinearMap.range (hnfMap a b c)).toAddSubgroup

/-- Membership in the HNF subgroup: integer combinations of the two rows. -/
theorem mem_hnfSubgroup_iff {a b c : ℤ} (x : ℤ × ℤ) :
    x ∈ hnfSubgroup a b c ↔ ∃ k l : ℤ, (k * a, k * b + l * c) = x := by
  constructor
  · rintro ⟨⟨k, l⟩, rfl⟩
    exact ⟨k, l, rfl⟩
  · rintro ⟨k, l, rfl⟩
    exact ⟨(k, l), rfl⟩

/-- With nonzero diagonal the HNF map is injective. -/
theorem hnfMap_injective {a b c : ℤ} (ha : a ≠ 0) (hc : c ≠ 0) :
    Injective (hnfMap a b c) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨k, l⟩ h
  have h1 : k * a = 0 := congrArg Prod.fst h
  have h2 : k * b + l * c = 0 := congrArg Prod.snd h
  have hk : k = 0 := by
    rcases mul_eq_zero.mp h1 with hk | hA
    · exact hk
    · exact absurd hA ha
  have hl : l = 0 := by
    rw [hk, zero_mul, zero_add] at h2
    rcases mul_eq_zero.mp h2 with hl | hC
    · exact hl
    · exact absurd hC hc
  rw [hk, hl]
  rfl

/-- The index of the HNF subgroup is the absolute value of the determinant
`a * c` (via `Submodule.natAbs_det_equiv`). -/
theorem hnfSubgroup_index (a b c : ℤ) (ha : a ≠ 0) (hc : c ≠ 0) :
    (hnfSubgroup a b c).index = (a * c).natAbs := by
  have hinj : Injective (hnfMap a b c) := hnfMap_injective ha hc
  have hdet :
      (LinearMap.det ((LinearMap.range (hnfMap a b c)).subtype ∘ₗ
        AddMonoidHom.toIntLinearMap
          ((LinearEquiv.ofInjective (hnfMap a b c) hinj : (ℤ × ℤ) →+
            LinearMap.range (hnfMap a b c))))).natAbs =
      Nat.card ((ℤ × ℤ) ⧸ LinearMap.range (hnfMap a b c)) :=
    Submodule.natAbs_det_equiv _ (LinearEquiv.ofInjective (hnfMap a b c) hinj)
  have hcomp :
      (LinearMap.range (hnfMap a b c)).subtype ∘ₗ
        AddMonoidHom.toIntLinearMap
          ((LinearEquiv.ofInjective (hnfMap a b c) hinj : (ℤ × ℤ) →+
            LinearMap.range (hnfMap a b c))) = hnfMap a b c :=
    LinearMap.ext fun _x => rfl
  rw [hcomp] at hdet
  have hindex : (hnfSubgroup a b c).index =
      Nat.card ((ℤ × ℤ) ⧸ LinearMap.range (hnfMap a b c)) := rfl
  rw [hindex, ← hdet]
  congr 1
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℤ)]
  have hmat : LinearMap.toMatrix (Module.Basis.finTwoProd ℤ) (Module.Basis.finTwoProd ℤ) (hnfMap a b c) =
      !![a, 0; b, c] := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    fin_cases j <;> fin_cases i <;>
      simp [hnfMap, Module.Basis.finTwoProd_zero, Module.Basis.finTwoProd_one, Module.Basis.coe_finTwoProd_repr]
  rw [hmat, Matrix.det_fin_two]
  simp

/-- Every additive subgroup of ℤ is `zmultiples` of a natural number. -/
theorem exists_nat_zmultiples (S : AddSubgroup ℤ) :
    ∃ g : ℕ, S = AddSubgroup.zmultiples (g : ℤ) := by
  obtain ⟨a, ha⟩ := Int.subgroup_cyclic S
  refine ⟨a.natAbs, ?_⟩
  ext x
  rw [ha, AddSubgroup.mem_closure_singleton, Int.mem_zmultiples_iff, Int.natAbs_dvd]
  constructor
  · rintro ⟨n, rfl⟩
    exact Dvd.intro n (mul_comm a n)
  · rintro ⟨n, rfl⟩
    exact ⟨n, (mul_comm a n).symm⟩

/-- First projection image of the HNF subgroup. -/
theorem map_fst_hnfSubgroup (a b c : ℤ) :
    (hnfSubgroup a b c).map (AddMonoidHom.fst ℤ ℤ) = AddSubgroup.zmultiples a := by
  ext x
  rw [AddSubgroup.mem_map, Int.mem_zmultiples_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨k, l, rfl⟩ := (mem_hnfSubgroup_iff y).mp hy
    exact dvd_mul_left a k
  · rintro ⟨k, rfl⟩
    refine ⟨(k * a, k * b), (mem_hnfSubgroup_iff _).mpr ⟨k, 0, by simp⟩, ?_⟩
    exact mul_comm k a

/-- Second-coordinate fiber of the HNF subgroup over `0`. -/
theorem comap_inr_hnfSubgroup (a b c : ℤ) (ha : a ≠ 0) :
    (hnfSubgroup a b c).comap (AddMonoidHom.inr ℤ ℤ) = AddSubgroup.zmultiples c := by
  ext y
  rw [AddSubgroup.mem_comap, Int.mem_zmultiples_iff]
  constructor
  · intro hy
    obtain ⟨k, l, hkl⟩ := (mem_hnfSubgroup_iff _).mp hy
    have h1 : k * a = 0 := congrArg Prod.fst hkl
    have h2 : k * b + l * c = y := congrArg Prod.snd hkl
    have hk : k = 0 := by
      rcases mul_eq_zero.mp h1 with hk | hA
      · exact hk
      · exact absurd hA ha
    rw [hk, zero_mul, zero_add] at h2
    exact Dvd.intro_left l h2
  · rintro ⟨l, rfl⟩
    exact (mem_hnfSubgroup_iff _).mpr ⟨0, l, by simp [mul_comm]⟩

/-- The first HNF row belongs to the subgroup. -/
theorem row_mem_hnfSubgroup (a b c : ℤ) : (a, b) ∈ hnfSubgroup a b c :=
  (mem_hnfSubgroup_iff _).mpr ⟨1, 0, by simp⟩

/-- The second HNF row belongs to the subgroup. -/
theorem row2_mem_hnfSubgroup (a b c : ℤ) : (0, c) ∈ hnfSubgroup a b c :=
  (mem_hnfSubgroup_iff _).mpr ⟨0, 1, by simp⟩

/-- A subgroup all of whose elements have first coordinate `0` has infinite
index (`Nat.card` junk value `0`). -/
theorem index_eq_zero_of_fst_bot {H : AddSubgroup (ℤ × ℤ)}
    (hfst : ∀ x ∈ H, (x : ℤ × ℤ).1 = 0) : H.index = 0 := by
  have hinj : Injective (fun z : ℤ => QuotientAddGroup.mk (s := H) (z, 0)) := by
    intro x y hxy
    have hmem : (-(x, 0) + ((y, 0) : ℤ × ℤ)) ∈ H := (QuotientAddGroup.eq).mp hxy
    have h1 : (-(x, 0) + ((y, 0) : ℤ × ℤ)).1 = 0 := hfst _ hmem
    have : -x + y = 0 := h1
    linarith
  have : Infinite ((ℤ × ℤ) ⧸ H) := Infinite.of_injective _ hinj
  exact Nat.card_eq_zero_of_infinite

/-- A subgroup meeting the second axis only at `0` has infinite index. -/
theorem index_eq_zero_of_snd_fiber_bot {H : AddSubgroup (ℤ × ℤ)}
    (hsnd : ∀ y : ℤ, ((0 : ℤ), y) ∈ H → y = 0) : H.index = 0 := by
  have hinj : Injective (fun z : ℤ => QuotientAddGroup.mk (s := H) (0, z)) := by
    intro x y hxy
    have hmem : (-(0, x) + ((0, y) : ℤ × ℤ)) ∈ H := (QuotientAddGroup.eq).mp hxy
    have h1 : -x + y = 0 := hsnd _ (by simpa using hmem)
    linarith
  have : Infinite ((ℤ × ℤ) ⧸ H) := Infinite.of_injective _ hinj
  exact Nat.card_eq_zero_of_infinite

/-- The generator determines the subgroup: `zmultiples` on ℕ-casts is injective. -/
theorem zmultiples_natCast_inj {g g' : ℕ}
    (h : AddSubgroup.zmultiples (g : ℤ) = AddSubgroup.zmultiples (g' : ℤ)) : g = g' := by
  have h1 : (g : ℤ) ∣ g' := by
    rw [← Int.mem_zmultiples_iff, h]
    exact AddSubgroup.mem_zmultiples _
  have h2 : (g' : ℤ) ∣ g := by
    rw [← Int.mem_zmultiples_iff, ← h]
    exact AddSubgroup.mem_zmultiples _
  exact_mod_cast Int.dvd_antisymm (by positivity) (by positivity) h1 h2

/-- HNF triples with positive `a`, `c` and `0 ≤ b < c` are determined by their
subgroup. -/
theorem hnf_inj {a a' c c' : ℕ} {b b' : ℤ} (ha : a ≠ 0) (ha' : a' ≠ 0)
    (hb0 : 0 ≤ b) (hbc : b < c) (hb0' : 0 ≤ b') (hbc' : b' < c')
    (h : hnfSubgroup (a : ℤ) b (c : ℤ) = hnfSubgroup (a' : ℤ) b' (c' : ℤ)) :
    a = a' ∧ c = c' ∧ b = b' := by
  have haa : a = a' := by
    apply zmultiples_natCast_inj
    rw [← map_fst_hnfSubgroup (a : ℤ) b c, ← map_fst_hnfSubgroup (a' : ℤ) b' c', h]
  have hcc : c = c' := by
    apply zmultiples_natCast_inj
    rw [← comap_inr_hnfSubgroup (a : ℤ) b c (by exact_mod_cast ha),
      ← comap_inr_hnfSubgroup (a' : ℤ) b' c' (by exact_mod_cast ha'), h]
  refine ⟨haa, hcc, ?_⟩
  -- both rows (a, b) and (a, b') lie in the same subgroup
  have hrow : ((a : ℤ), b) ∈ hnfSubgroup (a' : ℤ) b' (c' : ℤ) := h ▸ row_mem_hnfSubgroup _ _ _
  have hrow' : ((a : ℤ), b') ∈ hnfSubgroup (a' : ℤ) b' (c' : ℤ) := by
    rw [haa]; exact row_mem_hnfSubgroup _ _ _
  have hdiff : ((0 : ℤ), b - b') ∈ hnfSubgroup (a' : ℤ) b' (c' : ℤ) := by
    have hsub := AddSubgroup.sub_mem _ hrow hrow'
    have heq : (((a : ℤ), b) - ((a : ℤ), b')) = ((0 : ℤ), b - b') := by
      ext
      · simp
      · simp
    rwa [heq] at hsub
  have hdvd : (c' : ℤ) ∣ b - b' := by
    have hmem : b - b' ∈ (hnfSubgroup (a' : ℤ) b' (c' : ℤ)).comap (AddMonoidHom.inr ℤ ℤ) :=
      hdiff
    rwa [comap_inr_hnfSubgroup _ _ _ (by exact_mod_cast ha'), Int.mem_zmultiples_iff] at hmem
  -- both remainders lie in [0, c') so they agree
  have hmodeq : b' % (c' : ℤ) = b % (c' : ℤ) := Int.modEq_iff_dvd.mpr hdvd
  rw [Int.emod_eq_of_lt hb0' hbc', Int.emod_eq_of_lt hb0 (hcc ▸ hbc)] at hmodeq
  exact hmodeq.symm

/-- Every finite-index subgroup of ℤ² is an HNF subgroup with normalized data. -/
theorem exists_hnf_eq {H : AddSubgroup (ℤ × ℤ)} (hH : H.index ≠ 0) :
    ∃ (a c : ℕ) (b : ℤ), a ≠ 0 ∧ c ≠ 0 ∧ 0 ≤ b ∧ b < c ∧
      H = hnfSubgroup (a : ℤ) b (c : ℤ) := by
  obtain ⟨a, hA⟩ := exists_nat_zmultiples (H.map (AddMonoidHom.fst ℤ ℤ))
  obtain ⟨c, hK⟩ := exists_nat_zmultiples (H.comap (AddMonoidHom.inr ℤ ℤ))
  have ha : a ≠ 0 := by
    rintro rfl
    refine hH (index_eq_zero_of_fst_bot ?_)
    intro x hx
    have hx1 : x.1 ∈ H.map (AddMonoidHom.fst ℤ ℤ) := ⟨x, hx, rfl⟩
    rw [hA, Int.mem_zmultiples_iff] at hx1
    exact_mod_cast zero_dvd_iff.mp (by exact_mod_cast hx1)
  have hc : c ≠ 0 := by
    rintro rfl
    refine hH (index_eq_zero_of_snd_fiber_bot ?_)
    intro y hy
    have hy' : y ∈ H.comap (AddMonoidHom.inr ℤ ℤ) := hy
    rw [hK, Int.mem_zmultiples_iff] at hy'
    exact_mod_cast zero_dvd_iff.mp (by exact_mod_cast hy')
  have hcz : ((c : ℤ)) ≠ 0 := by exact_mod_cast hc
  have hcpos : (0 : ℤ) < c := lt_of_le_of_ne (by positivity) (Ne.symm hcz)
  -- a witness row over the generator a
  have haA : ((a : ℤ)) ∈ H.map (AddMonoidHom.fst ℤ ℤ) := by
    rw [hA]; exact AddSubgroup.mem_zmultiples _
  obtain ⟨x, hxH, hx1⟩ := haA
  have hxa : (((a : ℤ)), x.2) ∈ H := by
    have hx1' : x.1 = (a : ℤ) := hx1
    rw [← hx1']
    exact hxH
  set y := x.2 with hydef
  set b := y % (c : ℤ) with hbdef
  have hb0 : 0 ≤ b := Int.emod_nonneg y hcz
  have hbc : b < c := Int.emod_lt_of_pos y hcpos
  refine ⟨a, c, b, ha, hc, hb0, hbc, ?_⟩
  have hcH : ((0 : ℤ), (c : ℤ)) ∈ H := by
    have hmem : (c : ℤ) ∈ H.comap (AddMonoidHom.inr ℤ ℤ) := by
      rw [hK]; exact AddSubgroup.mem_zmultiples _
    exact hmem
  have habH : (((a : ℤ)), b) ∈ H := by
    have hsub := AddSubgroup.sub_mem _ hxa (AddSubgroup.zsmul_mem _ hcH (y / (c : ℤ)))
    have heq : (((a : ℤ), y) - (y / (c : ℤ)) • ((0 : ℤ), (c : ℤ))) = (((a : ℤ)), b) := by
      ext
      · simp
      · show y - (y / (c : ℤ)) • (c : ℤ) = b
        rw [smul_eq_mul, hbdef, Int.emod_def, mul_comm]
    rwa [heq] at hsub
  ext z
  constructor
  · intro hz
    have hz1 : (a : ℤ) ∣ z.1 := by
      have hmem : z.1 ∈ H.map (AddMonoidHom.fst ℤ ℤ) := ⟨z, hz, rfl⟩
      rwa [hA, Int.mem_zmultiples_iff] at hmem
    obtain ⟨k, hk⟩ := hz1
    have hz2 : ((0 : ℤ), z.2 - k * b) ∈ H := by
      have hsub := AddSubgroup.sub_mem _ hz (AddSubgroup.zsmul_mem _ habH k)
      have heq : (z - k • (((a : ℤ)), b)) = ((0 : ℤ), z.2 - k * b) := by
        ext
        · show z.1 - k • (a : ℤ) = 0
          rw [smul_eq_mul, hk]; ring
        · show z.2 - k • b = z.2 - k * b
          rw [smul_eq_mul]
      rwa [heq] at hsub
    have hz2' : z.2 - k * b ∈ H.comap (AddMonoidHom.inr ℤ ℤ) := hz2
    rw [hK, Int.mem_zmultiples_iff] at hz2'
    obtain ⟨l, hl⟩ := hz2'
    refine (mem_hnfSubgroup_iff z).mpr ⟨k, l, ?_⟩
    ext
    · show k * (a : ℤ) = z.1
      rw [hk]; ring
    · show k * b + l * (c : ℤ) = z.2
      have : z.2 - k * b = (c : ℤ) * l := hl
      linarith [this]
  · intro hz
    obtain ⟨k, l, rfl⟩ := (mem_hnfSubgroup_iff z).mp hz
    have hcomb := AddSubgroup.add_mem _ (AddSubgroup.zsmul_mem _ habH k)
      (AddSubgroup.zsmul_mem _ hcH l)
    have heq : (k • (((a : ℤ)), b) + l • ((0 : ℤ), (c : ℤ))) = (k * (a : ℤ), k * b + l * (c : ℤ)) := by
      ext
      · show k • (a : ℤ) + l • (0 : ℤ) = k * (a : ℤ)
        rw [smul_eq_mul, smul_eq_mul]; ring
      · show k • b + l • (c : ℤ) = k * b + l * (c : ℤ)
        rw [smul_eq_mul, smul_eq_mul]
    rwa [heq] at hcomb

/-- Hermite-normal-form data for an index-`d` subgroup of ℤ²: a factorization
`a * c = d` together with an off-diagonal entry `b < c`. -/
abbrev HNFData (d : ℕ) : Type :=
  Σ p : {p : ℕ × ℕ // p ∈ Nat.divisorsAntidiagonal d}, Fin p.1.2

/-- The subgroup encoded by HNF data, with its index certificate. -/
def hnfOfData (d : ℕ) (t : HNFData d) : {H : AddSubgroup (ℤ × ℤ) // H.index = d} :=
  ⟨hnfSubgroup (t.1.1.1 : ℤ) (t.2 : ℕ) (t.1.1.2 : ℤ), by
    obtain ⟨⟨⟨a, c⟩, hp⟩, b⟩ := t
    obtain ⟨hac, hd0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have ha : a ≠ 0 := left_ne_zero_of_mul (hac.symm ▸ hd0 : a * c ≠ 0)
    have hc : c ≠ 0 := right_ne_zero_of_mul (hac.symm ▸ hd0 : a * c ≠ 0)
    rw [hnfSubgroup_index _ _ _ (by exact_mod_cast ha) (by exact_mod_cast hc)]
    rw [← Nat.cast_mul, Int.natAbs_natCast]
    exact hac⟩

/-- HNF data parametrizes the index-`d` subgroups exactly once. -/
theorem hnfOfData_bijective (d : ℕ) (hd : d ≠ 0) : Function.Bijective (hnfOfData d) := by
  constructor
  · rintro ⟨⟨⟨a, c⟩, hp⟩, b⟩ ⟨⟨⟨a', c'⟩, hp'⟩, b'⟩ h
    have hsub : hnfSubgroup (a : ℤ) (b : ℕ) (c : ℤ) = hnfSubgroup (a' : ℤ) (b' : ℕ) (c' : ℤ) :=
      congrArg Subtype.val h
    obtain ⟨hac, hd0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    obtain ⟨hac', _⟩ := Nat.mem_divisorsAntidiagonal.mp hp'
    have ha : a ≠ 0 := left_ne_zero_of_mul (hac.symm ▸ hd0 : a * c ≠ 0)
    have ha' : a' ≠ 0 := left_ne_zero_of_mul (hac'.symm ▸ hd0 : a' * c' ≠ 0)
    obtain ⟨haa, hcc, hbb⟩ := hnf_inj ha ha' (by positivity) (by exact_mod_cast b.isLt)
      (by positivity) (by exact_mod_cast b'.isLt) hsub
    subst haa
    subst hcc
    have hb : b = b' := Fin.ext (by exact_mod_cast hbb)
    subst hb
    rfl
  · rintro ⟨H, hidx⟩
    have hH : H.index ≠ 0 := by rw [hidx]; exact hd
    obtain ⟨a, c, b, ha, hc, hb0, hbc, hHeq⟩ := exists_hnf_eq hH
    have hbn : b = ((b.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hb0).symm
    have hblt : b.toNat < c := by omega
    have hacd : a * c = d := by
      have h1 : H.index = a * c := by
        rw [hHeq, hnfSubgroup_index _ _ _ (by exact_mod_cast ha) (by exact_mod_cast hc),
          ← Nat.cast_mul, Int.natAbs_natCast]
      rw [← hidx, h1]
    refine ⟨⟨⟨(a, c), Nat.mem_divisorsAntidiagonal.mpr ⟨hacd, hd⟩⟩, ⟨b.toNat, hblt⟩⟩, ?_⟩
    apply Subtype.ext
    show hnfSubgroup (a : ℤ) (b.toNat : ℕ) (c : ℤ) = H
    rw [hHeq, ← hbn]

/-- **K1.** The number of index-`d` subgroups of ℤ² is σ(d). -/
theorem card_addSubgroup_index_eq_sigma1 (d : ℕ) (hd : d ≠ 0) :
    Nat.card {H : AddSubgroup (ℤ × ℤ) // H.index = d} = sigma1 d := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (hnfOfData_bijective d hd))]
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_sigma]
  have hterm : ∀ p : {p : ℕ × ℕ // p ∈ Nat.divisorsAntidiagonal d},
      Fintype.card (Fin p.1.2) = p.1.2 := fun p => Fintype.card_fin _
  rw [Finset.sum_congr rfl (fun p _ => hterm p)]
  rw [Finset.sum_coe_sort (Nat.divisorsAntidiagonal d) (fun p => p.2)]
  rw [Nat.sum_divisorsAntidiagonal (fun _ y => y) (n := d)]
  simpa [sigma1] using Nat.sum_div_divisors d id

/-- The finite-index subgroups of each index form a finite type. -/
theorem finite_addSubgroup_index (d : ℕ) (hd : d ≠ 0) :
    Finite {H : AddSubgroup (ℤ × ℤ) // H.index = d} :=
  Finite.of_surjective _ (hnfOfData_bijective d hd).surjective


/-! ### K3: counting weighted multisets of finite-index subgroups -/

noncomputable section

/-- A finite-index subgroup of ℤ², the iso type of a transitive ℤ²-set. -/
abbrev FIndexSubgroup : Type := {H : AddSubgroup (ℤ × ℤ) // H.index ≠ 0}

/-- The index (= size of the corresponding transitive ℤ²-set). -/
def fidx (H : FIndexSubgroup) : ℕ := H.1.index

/-- Total weight of a multiset of finite-index subgroups. -/
def msWeight (M : Multiset FIndexSubgroup) : ℕ := (M.map fidx).sum

/-- Weight is additive over multiset union. -/
theorem msWeight_add (A B : Multiset FIndexSubgroup) :
    msWeight (A + B) = msWeight A + msWeight B := by
  rw [msWeight, Multiset.map_add, Multiset.sum_add]; rfl

/-- The subgroups of index exactly `e`. -/
abbrev Grade (e : ℕ) : Type := {H : FIndexSubgroup // fidx H = e}

/-- Grade slices are the index-`e` subgroups. -/
def gradeEquiv (e : ℕ) (he : e ≠ 0) :
    Grade e ≃ {H : AddSubgroup (ℤ × ℤ) // H.index = e} where
  toFun t := ⟨t.1.1, t.2⟩
  invFun H := ⟨⟨H.1, by rw [H.2]; exact he⟩, H.2⟩
  left_inv t := rfl
  right_inv H := rfl

/-- Each grade is a finite type (empty at `e = 0`, K1 otherwise). -/
theorem finite_grade (e : ℕ) : Finite (Grade e) := by
  rcases eq_or_ne e 0 with rfl | he
  · haveI : IsEmpty (Grade 0) := ⟨fun t => t.1.2 t.2⟩
    exact @Finite.of_fintype _ Fintype.ofIsEmpty
  · haveI := finite_addSubgroup_index e he
    exact Finite.of_equiv _ (gradeEquiv e he).symm

/-- Grade `e ≠ 0` has exactly σ(e) elements. -/
theorem card_grade (e : ℕ) (he : e ≠ 0) : Nat.card (Grade e) = sigma1 e := by
  rw [Nat.card_congr (gradeEquiv e he), card_addSubgroup_index_eq_sigma1 e he]

/-- Multisets of subgroups of total weight `n`, all parts of index at most `d`. -/
abbrev BoundedMS (d n : ℕ) : Type :=
  {M : Multiset FIndexSubgroup // msWeight M = n ∧ ∀ H ∈ M, fidx H ≤ d}

/-- Multisets of subgroups of total weight `n`. -/
abbrev WeightedMS (n : ℕ) : Type := {M : Multiset FIndexSubgroup // msWeight M = n}

/-- A `0`-bounded multiset has no parts (indices are nonzero). -/
theorem boundedMS_zero_val {n : ℕ} (X : BoundedMS 0 n) : X.1 = 0 := by
  apply Multiset.eq_zero_of_forall_notMem
  intro H hH
  exact H.2 (Nat.le_zero.mp (X.2.2 H hH))

/-- `0`-bounded multisets are unique when they exist. -/
instance boundedMS_zero_subsingleton (n : ℕ) : Subsingleton (BoundedMS 0 n) :=
  ⟨fun a b => Subtype.ext ((boundedMS_zero_val a).trans (boundedMS_zero_val b).symm)⟩

/-- The empty multiset has weight `0`. -/
theorem msWeight_zero : msWeight 0 = 0 := rfl

/-- Base case of the assembly count: only the empty multiset, only at
weight `0`. -/
theorem card_boundedMS_zero (n : ℕ) :
    Nat.card (BoundedMS 0 n) = if n = 0 then 1 else 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · haveI : Nonempty (BoundedMS 0 0) :=
      ⟨⟨0, msWeight_zero, fun H hH => absurd hH (Multiset.notMem_zero H)⟩⟩
    rw [if_pos rfl]
    exact Nat.card_unique
  · haveI : IsEmpty (BoundedMS 0 n) := ⟨fun X => by
      have h1 := X.2.1
      rw [boundedMS_zero_val X, msWeight_zero] at h1
      exact hn h1.symm⟩
    rw [if_neg hn]
    exact Nat.card_of_isEmpty

/-- Weight of a multiset all of whose parts sit in one grade. -/
theorem msWeight_of_grade {e : ℕ} (m : ℕ) (s : Sym (Grade e) m) :
    msWeight ((s : Multiset (Grade e)).map Subtype.val) = e * m := by
  have hrep : ((s : Multiset (Grade e)).map Subtype.val).map fidx =
      Multiset.replicate m e := by
    rw [Multiset.eq_replicate]
    constructor
    · rw [Multiset.card_map, Multiset.card_map, Sym.card_coe]
    · intro b hb
      obtain ⟨t, _ht, rfl⟩ := Multiset.mem_map.mp hb
      obtain ⟨u, _hu, rfl⟩ := Multiset.mem_map.mp _ht
      exact u.2
  rw [msWeight, hrep, Multiset.sum_replicate, smul_eq_mul, mul_comm]

/-- Repackage a multiset whose parts all have index `e` as a multiset of
grade-`e` subgroups. -/
def gradeAttachFun (e : ℕ) (T : Multiset FIndexSubgroup) (hT : ∀ H ∈ T, fidx H = e)
    (t : {x // x ∈ T}) : Grade e := ⟨t.1, hT t.1 t.2⟩

/-- Repackage a multiset whose parts all have index `e` as a multiset of
grade-`e` subgroups.  (Kept as a named definition: an inline lambda here
sends the elaborator into `AddSubgroup.index` reduction.) -/
def gradeAttach (e : ℕ) (T : Multiset FIndexSubgroup) (hT : ∀ H ∈ T, fidx H = e) :
    Multiset (Grade e) :=
  T.attach.map (gradeAttachFun e T hT)

/-- `gradeAttach` preserves cardinality. -/
theorem gradeAttach_card (e : ℕ) (T : Multiset FIndexSubgroup)
    (hT : ∀ H ∈ T, fidx H = e) : (gradeAttach e T hT).card = T.card := by
  rw [gradeAttach, Multiset.card_map, Multiset.card_attach]

/-- Forgetting the grade recovers the original multiset. -/
theorem gradeAttach_map_val (e : ℕ) (T : Multiset FIndexSubgroup)
    (hT : ∀ H ∈ T, fidx H = e) : (gradeAttach e T hT).map Subtype.val = T := by
  rw [gradeAttach, Multiset.map_map]
  have hcomp : (Subtype.val ∘ gradeAttachFun e T hT) = fun t => t.1 := rfl
  rw [hcomp]
  exact Multiset.attach_map_val T

/-- The assembly map for the recursion step: a batch of grade-`(d+1)` parts
together with a `d`-bounded remainder assembles to a `(d+1)`-bounded multiset. -/
def stepAssemble (d n : ℕ)
    (x : Σ m : Fin (n / (d + 1) + 1), Sym (Grade (d + 1)) (m : ℕ) ×
      BoundedMS d (n - (d + 1) * (m : ℕ))) :
    BoundedMS (d + 1) n := by
  refine ⟨(x.2.1 : Multiset (Grade (d + 1))).map Subtype.val + x.2.2.1, ?_, ?_⟩
  · have hmle : (d + 1) * (x.1 : ℕ) ≤ n := by
      have h1 : (x.1 : ℕ) ≤ n / (d + 1) := Nat.lt_succ_iff.mp x.1.isLt
      calc (d + 1) * (x.1 : ℕ) ≤ (d + 1) * (n / (d + 1)) := Nat.mul_le_mul_left _ h1
        _ = (n / (d + 1)) * (d + 1) := mul_comm _ _
        _ ≤ n := Nat.div_mul_le_self n (d + 1)
    rw [msWeight_add, msWeight_of_grade _ x.2.1, x.2.2.2.1]
    omega
  · intro H hH
    rcases Multiset.mem_add.mp hH with hA | hB
    · obtain ⟨t, _ht, rfl⟩ := Multiset.mem_map.mp hA
      exact le_of_eq t.2
    · exact le_trans (x.2.2.2.2 H hB) (Nat.le_succ d)

/-- Filtering the assembled multiset recovers the grade-`(d+1)` batch. -/
theorem filter_stepAssemble (d _n : ℕ) (m : ℕ) (s : Sym (Grade (d + 1)) m)
    (R : Multiset FIndexSubgroup) (hR : ∀ H ∈ R, fidx H ≤ d) :
    Multiset.filter (fun H => fidx H = d + 1)
        ((s : Multiset (Grade (d + 1))).map Subtype.val + R) =
      (s : Multiset (Grade (d + 1))).map Subtype.val := by
  rw [Multiset.filter_add]
  rw [Multiset.filter_eq_self.mpr, Multiset.filter_eq_nil.mpr, add_zero]
  · intro H hH
    have := hR H hH
    omega
  · intro H hH
    obtain ⟨t, _ht, rfl⟩ := Multiset.mem_map.mp hH
    exact t.2

/-- Assembly is a bijection: the batch is recovered by filtering on the top
grade, the remainder by cancellation. -/
theorem stepAssemble_bijective (d n : ℕ) : Function.Bijective (stepAssemble d n) := by
  constructor
  · rintro ⟨m, s, R⟩ ⟨m', s', R'⟩ h
    have hval : (s : Multiset (Grade (d + 1))).map Subtype.val + R.1 =
        (s' : Multiset (Grade (d + 1))).map Subtype.val + R'.1 :=
      congrArg Subtype.val h
    have hs : (s : Multiset (Grade (d + 1))).map Subtype.val =
        (s' : Multiset (Grade (d + 1))).map Subtype.val := by
      rw [← filter_stepAssemble d n m s R.1 (fun H hH => R.2.2 H hH),
        ← filter_stepAssemble d n m' s' R'.1 (fun H hH => R'.2.2 H hH), hval]
    have hss : (s : Multiset (Grade (d + 1))) = (s' : Multiset (Grade (d + 1))) :=
      Multiset.map_injective Subtype.val_injective hs
    have hm : m = m' := by
      apply Fin.ext
      rw [← Sym.card_coe (s := s), ← Sym.card_coe (s := s'), hss]
    subst hm
    have hR : R.1 = R'.1 := by
      rw [hs] at hval
      exact add_left_cancel hval
    exact congrArg (Sigma.mk m) (Prod.ext (Sym.coe_injective hss) (Subtype.ext hR))
  · rintro ⟨M, hw, hb⟩
    set top := M.filter (fun H => fidx H = d + 1) with htopdef
    set rest := M.filter (fun H => ¬ fidx H = d + 1) with hrestdef
    have hM : top + rest = M := Multiset.filter_add_not _ M
    have htopall : ∀ H ∈ top, fidx H = d + 1 := fun H hH => (Multiset.mem_filter.mp hH).2
    have htopw : msWeight top = (d + 1) * top.card := by
      have hrep : top.map fidx = Multiset.replicate top.card (d + 1) := by
        rw [Multiset.eq_replicate]
        exact ⟨Multiset.card_map _ _, fun b hb => by
          obtain ⟨H, hH, rfl⟩ := Multiset.mem_map.mp hb
          exact htopall H hH⟩
      rw [msWeight, hrep, Multiset.sum_replicate, smul_eq_mul, mul_comm]
    have hsplit : msWeight top + msWeight rest = n := by
      rw [← msWeight_add, hM, hw]
    have hle : (d + 1) * top.card ≤ n := by omega
    have hmlt : top.card < n / (d + 1) + 1 :=
      Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le (Nat.succ_pos d)).mpr
        (by rw [mul_comm]; exact hle))
    have hrestw : msWeight rest = n - (d + 1) * top.card := by omega
    have hrestb : ∀ H ∈ rest, fidx H ≤ d := by
      intro H hH
      have h1 : fidx H ≤ d + 1 := hb H (Multiset.mem_of_mem_filter hH)
      have h2 : ¬ fidx H = d + 1 := (Multiset.mem_filter.mp hH).2
      omega
    refine ⟨⟨⟨top.card, hmlt⟩,
      ⟨Sym.mk (gradeAttach (d + 1) top htopall) (gradeAttach_card (d + 1) top htopall),
        ⟨rest, hrestw, hrestb⟩⟩⟩, ?_⟩
    apply Subtype.ext
    show (gradeAttach (d + 1) top htopall).map Subtype.val + rest = M
    rw [gradeAttach_map_val, hM]

/-- The recursion-step equivalence. -/
noncomputable def stepEquiv (d n : ℕ) :
    (Σ m : Fin (n / (d + 1) + 1), Sym (Grade (d + 1)) (m : ℕ) ×
      BoundedMS d (n - (d + 1) * (m : ℕ))) ≃ BoundedMS (d + 1) n :=
  Equiv.ofBijective _ (stepAssemble_bijective d n)

/-- Bounded weighted multisets form a finite type. -/
theorem finite_boundedMS (d n : ℕ) : Finite (BoundedMS d n) := by
  induction d generalizing n with
  | zero => exact Finite.of_subsingleton
  | succ d ih =>
    haveI : ∀ k, Finite (BoundedMS d k) := ih
    haveI : ∀ e, Finite (Grade e) := finite_grade
    exact Finite.of_equiv _ (stepEquiv d n)

/-- Symmetric powers of a finite type count multisets by multichoose. -/
theorem nat_card_sym (α : Type*) [Finite α] (m : ℕ) :
    Nat.card (Sym α m) = (Nat.card α + m - 1).choose m := by
  letI := Fintype.ofFinite α
  letI := Classical.decEq α
  rw [Nat.card_eq_fintype_card (α := Sym α m), Sym.card_sym_eq_multichoose,
    Nat.multichoose_eq, Fintype.card_eq_nat_card]

/-- **K3.** Bounded weighted multisets of subgroups are counted by the Euler
coefficient recursion. -/
theorem card_boundedMS (d n : ℕ) : Nat.card (BoundedMS d n) = eulerCoeff sigma1 d n := by
  induction d generalizing n with
  | zero =>
    rw [card_boundedMS_zero]
    rfl
  | succ d ih =>
    haveI : ∀ k, Finite (BoundedMS d k) := finite_boundedMS d
    haveI : ∀ e, Finite (Grade e) := finite_grade
    rw [← Nat.card_congr (stepEquiv d n), Nat.card_sigma]
    have hterm : ∀ m : Fin (n / (d + 1) + 1),
        Nat.card (Sym (Grade (d + 1)) (m : ℕ) × BoundedMS d (n - (d + 1) * (m : ℕ))) =
          (sigma1 (d + 1) + (m : ℕ) - 1).choose (m : ℕ) *
            eulerCoeff sigma1 d (n - (d + 1) * (m : ℕ)) := by
      intro m
      rw [Nat.card_prod, nat_card_sym, card_grade _ (Nat.succ_ne_zero d), ih]
    rw [Finset.sum_congr rfl (fun m _ => hterm m)]
    rw [Fin.sum_univ_eq_sum_range (fun m =>
      (sigma1 (d + 1) + m - 1).choose m * eulerCoeff sigma1 d (n - (d + 1) * m))]
    rfl

/-- Any part of a weight-`n` multiset has index at most `n`. -/
theorem fidx_le_of_mem {n : ℕ} {M : Multiset FIndexSubgroup} (hw : msWeight M = n)
    {H : FIndexSubgroup} (hH : H ∈ M) : fidx H ≤ n := by
  have hmem : fidx H ∈ M.map fidx := Multiset.mem_map_of_mem fidx hH
  have := Multiset.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
  rwa [← msWeight, hw] at this

/-- **K3, assembled.** Weighted multisets of finite-index subgroups of ℤ² are
counted by the Euler transform of σ. -/
theorem card_weightedMS (n : ℕ) : Nat.card (WeightedMS n) = eulerCoeff sigma1 n n := by
  let he : WeightedMS n ≃ BoundedMS n n :=
    Equiv.subtypeEquivRight (fun M => ⟨fun hw => ⟨hw, fun H hH => fidx_le_of_mem hw hH⟩,
      fun h => h.1⟩)
  rw [Nat.card_congr he, card_boundedMS]

end

-- Ground truth for the HNF subgroup: explicit members, a non-member, and an
-- index computation.
example : ((2 : ℤ), (1 : ℤ)) ∈ hnfSubgroup 2 1 3 :=
  (mem_hnfSubgroup_iff _).mpr ⟨1, 0, by norm_num⟩
example : ((0 : ℤ), (3 : ℤ)) ∈ hnfSubgroup 2 1 3 :=
  (mem_hnfSubgroup_iff _).mpr ⟨0, 1, by norm_num⟩
example : ((1 : ℤ), (0 : ℤ)) ∉ hnfSubgroup 2 1 3 := by
  rintro h
  obtain ⟨k, l, hkl⟩ := (mem_hnfSubgroup_iff _).mp h
  have h1 : k * 2 = 1 := congrArg Prod.fst hkl
  omega
example : (hnfSubgroup 2 1 3).index = 6 := by
  rw [hnfSubgroup_index 2 1 3 (by norm_num) (by norm_num)]
  norm_num

-- Ground truth for K1 at `d = 1` and `d = 2`: `⊤` is the unique index-1
-- subgroup; σ(2) = 3.
example : Nat.card {H : AddSubgroup (ℤ × ℤ) // H.index = 1} = 1 := by
  rw [card_addSubgroup_index_eq_sigma1 1 one_ne_zero]
  decide
example : Nat.card {H : AddSubgroup (ℤ × ℤ) // H.index = 2} = 3 := by
  rw [card_addSubgroup_index_eq_sigma1 2 two_ne_zero]
  decide

-- Ground truth for the multiset layer: the full lattice `⊤` is a
-- finite-index subgroup of weight 1.
example : msWeight {(⟨⊤, by simp [AddSubgroup.index_top]⟩ : FIndexSubgroup)} = 1 := by
  simp [msWeight, fidx, AddSubgroup.index_top]

/-! ### K2: the classifying bijection — conjugacy classes of representations
are the weighted subgroup multisets -/

noncomputable section

/-! ### K2a generalized: the stabilizer-multiset invariant of a finite ℤ²-set -/

/-- Stabilizers of a commutative group action are constant on orbits. -/
theorem stabilizer_eq_of_mem_orbit {G α : Type*} [CommGroup G] [MulAction G α]
    {x y : α} (h : y ∈ orbit G x) : stabilizer G y = stabilizer G x := by
  obtain ⟨g, rfl⟩ := h
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  have hconj : (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
    ext a
    show g * a * g⁻¹ = a
    rw [mul_comm g a, mul_inv_cancel_right]
  rw [hconj, Subgroup.map_id]

/-- The multiplicative-additive dictionary preserves the index. -/
theorem index_toAddSubgroup' {A : Type*} [AddGroup A] (H : Subgroup (Multiplicative A)) :
    (Subgroup.toAddSubgroup' H : AddSubgroup A).index = H.index := by
  apply Nat.card_congr
  refine Quotient.congr Multiplicative.toAdd (fun a b => ?_)
  rw [QuotientGroup.leftRel_apply, QuotientAddGroup.leftRel_apply,
    Subgroup.mem_toAddSubgroup']
  constructor
  · intro hab
    exact hab
  · intro hab
    exact hab

variable (X : Type*) [MulAction Z2 X] [Finite X]

/-- The stabilizer of (a representative of) an orbit of a finite ℤ²-set,
as a finite-index subgroup of ℤ². -/
def actionStabPack (ω : orbitRel.Quotient Z2 X) : FIndexSubgroup :=
  ⟨Subgroup.toAddSubgroup' (stabilizer Z2 (Quotient.out ω)), by
    rw [index_toAddSubgroup', MulAction.index_stabilizer]
    have hfin : (orbit Z2 (Quotient.out ω)).Finite := Set.toFinite _
    have hne : (orbit Z2 (Quotient.out ω)).Nonempty := ⟨_, mem_orbit_self _⟩
    exact ((Set.ncard_pos hfin).mpr hne).ne'⟩

/-- The complete invariant of a finite ℤ²-set: the multiset of orbit
stabilizers. -/
def actionOrbitMultiset : Multiset FIndexSubgroup :=
  letI := Fintype.ofFinite (orbitRel.Quotient Z2 X)
  (Finset.univ : Finset (orbitRel.Quotient Z2 X)).val.map (actionStabPack X)

/-- The stabilizer multiset has total weight the size of the set:
orbit sizes sum to the cardinality. -/
theorem msWeight_actionOrbitMultiset : msWeight (actionOrbitMultiset X) = Nat.card X := by
  letI := Fintype.ofFinite (orbitRel.Quotient Z2 X)
  have h1 : msWeight (actionOrbitMultiset X) =
      ∑ ω : orbitRel.Quotient Z2 X, fidx (actionStabPack X ω) := by
    rw [msWeight, actionOrbitMultiset, Multiset.map_map]
    rfl
  have h2 : ∀ ω : orbitRel.Quotient Z2 X, fidx (actionStabPack X ω) =
      Nat.card (orbit Z2 (Quotient.out ω)) := by
    intro ω
    rw [fidx, actionStabPack, index_toAddSubgroup', MulAction.index_stabilizer,
      Nat.card_coe_set_eq]
  have h3 : Nat.card (Σ ω : orbitRel.Quotient Z2 X, orbit Z2 (Quotient.out ω)) =
      Nat.card X := Nat.card_congr (selfEquivSigmaOrbits Z2 X).symm
  rw [Nat.card_sigma] at h3
  rw [h1, Finset.sum_congr rfl (fun ω _ => h2 ω), h3]

variable {X}

/-- Transport: an equivariant bijection preserves the packed stabilizers
along the induced map of orbit spaces (`orbitQuotientCongr`). -/
theorem actionStabPack_congr {Y : Type*} [MulAction Z2 Y] [Finite Y]
    (f : X ≃ Y) (hf : ∀ (a : Z2) (x : X), f (a • x) = a • f x)
    (ω : orbitRel.Quotient Z2 X) :
    actionStabPack Y (orbitQuotientCongr f hf ω) = actionStabPack X ω := by
  have hrel : (orbitRel Z2 Y) (Quotient.out (orbitQuotientCongr f hf ω))
      (f (Quotient.out ω)) := by
    apply Quotient.exact
    rw [Quotient.out_eq]
    conv_lhs => rw [← Quotient.out_eq ω]
    rfl
  have hmem : Quotient.out (orbitQuotientCongr f hf ω) ∈ orbit Z2 (f (Quotient.out ω)) := by
    rw [← orbitRel_apply]
    exact hrel
  have hstab1 : stabilizer Z2 (Quotient.out (orbitQuotientCongr f hf ω)) =
      stabilizer Z2 (f (Quotient.out ω)) := stabilizer_eq_of_mem_orbit hmem
  have hstab2 : stabilizer Z2 (f (Quotient.out ω)) = stabilizer Z2 (Quotient.out ω) := by
    ext a
    rw [mem_stabilizer_iff, mem_stabilizer_iff, ← hf a (Quotient.out ω)]
    exact ⟨fun h => f.injective h, fun h => congrArg f h⟩
  exact Subtype.ext (congrArg
    (fun S : Subgroup Z2 => (Subgroup.toAddSubgroup' S : AddSubgroup (ℤ × ℤ)))
    (hstab1.trans hstab2))

/-- Transport: an equivariant bijection preserves the stabilizer multiset. -/
theorem actionOrbitMultiset_congr {Y : Type*} [MulAction Z2 Y] [Finite Y]
    (f : X ≃ Y) (hf : ∀ (a : Z2) (x : X), f (a • x) = a • f x) :
    actionOrbitMultiset Y = actionOrbitMultiset X := by
  letI := Fintype.ofFinite (orbitRel.Quotient Z2 X)
  letI := Fintype.ofFinite (orbitRel.Quotient Z2 Y)
  have huniv : (Finset.univ : Finset (orbitRel.Quotient Z2 Y)) =
      (Finset.univ : Finset (orbitRel.Quotient Z2 X)).map
        (orbitQuotientCongr f hf).toEmbedding :=
    (Finset.map_univ_equiv (orbitQuotientCongr f hf)).symm
  rw [actionOrbitMultiset, huniv, Finset.map_val, Multiset.map_map, actionOrbitMultiset]
  apply Multiset.map_congr rfl
  intro ω _
  exact actionStabPack_congr f hf ω

/-! ### Specialization to permutation representations on `Fin n` -/

variable {n : ℕ}

/-- The ℤ²-action on `Fin n` induced by a permutation representation. -/
abbrev permAction (φ : Z2 →* Equiv.Perm (Fin n)) : MulAction Z2 (Fin n) :=
  MulAction.compHom (Fin n) φ

/-- Applying a conjugated permutation along the conjugator. -/
theorem perm_conj_apply (σ τ : Equiv.Perm (Fin n)) (x : Fin n) :
    (σ * τ * σ⁻¹) (σ x) = σ (τ x) := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply]

/-- The stabilizer-multiset invariant of a permutation representation. -/
def orbitMultiset (φ : Z2 →* Equiv.Perm (Fin n)) : Multiset FIndexSubgroup :=
  @actionOrbitMultiset (Fin n) (permAction φ) _

/-- The invariant has total weight `n`. -/
theorem msWeight_orbitMultiset (φ : Z2 →* Equiv.Perm (Fin n)) :
    msWeight (orbitMultiset φ) = n := by
  letI := permAction φ
  rw [orbitMultiset, msWeight_actionOrbitMultiset, Nat.card_fin]

/-- The invariant is conjugation-invariant. -/
theorem orbitMultiset_conj_smul (c : ConjAct (Equiv.Perm (Fin n)))
    (φ : Z2 →* Equiv.Perm (Fin n)) :
    orbitMultiset (c • φ) = orbitMultiset φ := by
  refine @actionOrbitMultiset_congr (Fin n) (permAction φ) _ (Fin n)
    (permAction (c • φ)) _ (ConjAct.ofConjAct c : Equiv.Perm (Fin n)) ?_
  intro a x
  show ConjAct.ofConjAct c (φ a x) =
    (ConjAct.ofConjAct c * φ a * (ConjAct.ofConjAct c)⁻¹) (ConjAct.ofConjAct c x)
  rw [perm_conj_apply]

/-- The classifying invariant, descended to conjugacy classes of
representations. -/
def classifyOrbit (n : ℕ) :
    orbitRel.Quotient (ConjAct (Equiv.Perm (Fin n))) (Z2 →* Equiv.Perm (Fin n)) →
      WeightedMS n :=
  Quotient.lift (fun φ => (⟨orbitMultiset φ, msWeight_orbitMultiset φ⟩ : WeightedMS n))
    (by
      intro φ ψ hrel
      have hrel' : φ ∈ orbit (ConjAct (Equiv.Perm (Fin n))) ψ := hrel
      obtain ⟨c, rfl⟩ := hrel'
      exact Subtype.ext (orbitMultiset_conj_smul c ψ))

/-! ### The matching lemma: equal image multisets over finite types give a
fiberwise bijection -/

/-- If two finite families have the same image multiset, some bijection of the
index types intertwines them. -/
theorem exists_equiv_of_map_univ_eq {α β γ : Type*} [Fintype α] [Fintype β]
    (f : α → γ) (g : β → γ)
    (h : Multiset.map f (Finset.univ : Finset α).val =
      Multiset.map g (Finset.univ : Finset β).val) :
    ∃ e : α ≃ β, ∀ a, g (e a) = f a := by
  classical
  have hcard : ∀ c : γ, Fintype.card {a : α // f a = c} = Fintype.card {b : β // g b = c} := by
    intro c
    have hc1 : Fintype.card {a : α // f a = c} =
        Multiset.count c (Multiset.map f (Finset.univ : Finset α).val) := by
      rw [Multiset.count_map, Fintype.card_subtype, Finset.card_def, Finset.filter_val]
      congr 1
      exact Multiset.filter_congr (fun x _ => eq_comm)
    have hc2 : Fintype.card {b : β // g b = c} =
        Multiset.count c (Multiset.map g (Finset.univ : Finset β).val) := by
      rw [Multiset.count_map, Fintype.card_subtype, Finset.card_def, Finset.filter_val]
      congr 1
      exact Multiset.filter_congr (fun x _ => eq_comm)
    rw [hc1, hc2, h]
  let efib : ∀ c : γ, {a : α // f a = c} ≃ {b : β // g b = c} := fun c =>
    Fintype.equivOfCardEq (hcard c)
  let e : α ≃ β :=
    (Equiv.sigmaFiberEquiv f).symm.trans
      ((Equiv.sigmaCongrRight efib).trans (Equiv.sigmaFiberEquiv g))
  refine ⟨e, fun a => ?_⟩
  show g ((Equiv.sigmaFiberEquiv g) ((Equiv.sigmaCongrRight efib)
    ((Equiv.sigmaFiberEquiv f).symm a))) = f a
  have h1 : (Equiv.sigmaFiberEquiv f).symm a = ⟨f a, ⟨a, rfl⟩⟩ := rfl
  rw [h1]
  have h2 : (Equiv.sigmaCongrRight efib) (⟨f a, ⟨a, rfl⟩⟩ :
      Σ c : γ, {a : α // f a = c}) = ⟨f a, efib (f a) ⟨a, rfl⟩⟩ := rfl
  rw [h2]
  exact (efib (f a) ⟨a, rfl⟩).2

/-! ### K2c: surjectivity — every weighted multiset of subgroups is realized -/

/-- The subgroup of ℤ² (written multiplicatively) named by a finite-index
additive subgroup. -/
def subOf (H : FIndexSubgroup) : Subgroup Z2 := Subgroup.toAddSubgroup'.symm H.1

/-- `subOf` preserves the index. -/
theorem index_subOf (H : FIndexSubgroup) : (subOf H).index = fidx H := by
  have h := index_toAddSubgroup' (subOf H)
  rw [subOf, OrderIso.apply_symm_apply] at h
  exact h.symm

/-- Coset spaces of finite-index subgroups are finite. -/
instance quotFiniteOfFIndex (H : FIndexSubgroup) : Finite (Z2 ⧸ subOf H) := by
  have h : Nat.card (Z2 ⧸ subOf H) ≠ 0 := by
    rw [← Subgroup.index_eq_card, index_subOf]
    exact H.2
  exact (Nat.card_ne_zero.mp h).2

/-- The model ℤ²-set of a list of finite-index subgroups: the disjoint union
of the coset spaces. -/
abbrev ModelSpace (L : List FIndexSubgroup) : Type :=
  Σ i : Fin L.length, Z2 ⧸ subOf (L.get i)

/-- Summing over `Fin l.length` is summing over the list. -/
theorem sum_fin_get {α : Type*} (l : List α) (f : α → ℕ) :
    ∑ i : Fin l.length, f (l.get i) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [List.get_cons_zero, List.map_cons, List.sum_cons]
    have hsucc : ∀ i : Fin t.length, f ((h :: t).get i.succ) = f (t.get i) := fun _ => rfl
    rw [Finset.sum_congr rfl (fun i _ => hsucc i), ih]

/-- The model space has cardinality the weight of the list. -/
theorem card_modelSpace (L : List FIndexSubgroup) :
    Nat.card (ModelSpace L) = msWeight (↑L : Multiset FIndexSubgroup) := by
  rw [Nat.card_sigma]
  have hterm : ∀ i : Fin L.length, Nat.card (Z2 ⧸ subOf (L.get i)) = fidx (L.get i) := by
    intro i
    rw [← Subgroup.index_eq_card, index_subOf]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), sum_fin_get L fidx]
  rw [msWeight, Multiset.map_coe, Multiset.sum_coe]

/-- The orbits of the model space are its summands. -/
def modelOrbitEquiv (L : List FIndexSubgroup) :
    orbitRel.Quotient Z2 (ModelSpace L) ≃ Fin L.length where
  toFun := Quotient.lift (fun x : ModelSpace L => x.1) (by
    rintro x y ⟨a, rfl⟩
    rfl)
  invFun i := Quotient.mk _ ⟨i, ((1 : Z2) : Z2 ⧸ subOf (L.get i))⟩
  left_inv := by
    refine Quotient.ind (fun x => ?_)
    obtain ⟨i, q⟩ := x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    apply Quotient.sound
    refine ⟨g⁻¹, ?_⟩
    show g⁻¹ • (⟨i, QuotientGroup.mk g⟩ : ModelSpace L) =
      ⟨i, ((1 : Z2) : Z2 ⧸ subOf (L.get i))⟩
    rw [Sigma.smul_mk, MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel]
  right_inv i := rfl

/-- Stabilizers in a sigma type live in the component. -/
theorem stabilizer_sigma {ι : Type*} {Y : ι → Type*} [∀ i, MulAction Z2 (Y i)]
    (i : ι) (y : Y i) :
    stabilizer Z2 (⟨i, y⟩ : Σ j, Y j) = stabilizer Z2 y := by
  ext a
  rw [mem_stabilizer_iff, mem_stabilizer_iff, Sigma.smul_mk]
  constructor
  · intro h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  · intro h
    rw [h]

/-- The model space realizes the list as its stabilizer multiset. -/
theorem actionOrbitMultiset_modelSpace (L : List FIndexSubgroup) :
    actionOrbitMultiset (ModelSpace L) = (↑L : Multiset FIndexSubgroup) := by
  letI := Fintype.ofFinite (orbitRel.Quotient Z2 (ModelSpace L))
  have hpack : ∀ i : Fin L.length,
      actionStabPack (ModelSpace L) ((modelOrbitEquiv L).symm i) = L.get i := by
    intro i
    have hout : Quotient.out ((modelOrbitEquiv L).symm i) ∈
        orbit Z2 (⟨i, ((1 : Z2) : Z2 ⧸ subOf (L.get i))⟩ : ModelSpace L) := by
      rw [← orbitRel_apply]
      apply Quotient.exact
      rw [Quotient.out_eq]
      rfl
    have hstab : stabilizer Z2 (Quotient.out ((modelOrbitEquiv L).symm i)) =
        subOf (L.get i) := by
      rw [stabilizer_eq_of_mem_orbit hout, stabilizer_sigma]
      exact MulAction.stabilizer_quotient (subOf (L.get i))
    apply Subtype.ext
    show (Subgroup.toAddSubgroup'
      (stabilizer Z2 (Quotient.out ((modelOrbitEquiv L).symm i))) : AddSubgroup (ℤ × ℤ)) =
      (L.get i).1
    rw [hstab, subOf, OrderIso.apply_symm_apply]
  have huniv : (Finset.univ : Finset (orbitRel.Quotient Z2 (ModelSpace L))) =
      (Finset.univ : Finset (Fin L.length)).map (modelOrbitEquiv L).symm.toEmbedding :=
    (Finset.map_univ_equiv (modelOrbitEquiv L).symm).symm
  rw [actionOrbitMultiset, huniv, Finset.map_val, Multiset.map_map]
  have hfun : (actionStabPack (ModelSpace L) ∘ (modelOrbitEquiv L).symm.toEmbedding) =
      fun i : Fin L.length => L.get i := by
    funext i
    exact hpack i
  rw [hfun]
  rw [Fin.univ_val_map, List.ofFn_get]

/-- **K2c.** The classifying map is surjective: every weight-`n` multiset of
finite-index subgroups arises from a representation. -/
theorem classifyOrbit_surjective (n : ℕ) : Surjective (classifyOrbit n) := by
  rintro ⟨M, hw⟩
  letI := Fintype.ofFinite (ModelSpace M.toList)
  have hcard : Fintype.card (ModelSpace M.toList) = n := by
    rw [Fintype.card_eq_nat_card, card_modelSpace, Multiset.coe_toList, hw]
  set e0 : ModelSpace M.toList ≃ Fin n := Fintype.equivFinOfCardEq hcard with he0
  set φ : Z2 →* Equiv.Perm (Fin n) :=
    ((Equiv.permCongrHom e0 : Equiv.Perm (ModelSpace M.toList) ≃* Equiv.Perm (Fin n))
        : Equiv.Perm (ModelSpace M.toList) →* Equiv.Perm (Fin n)).comp
      (MulAction.toPermHom Z2 (ModelSpace M.toList)) with hφ
  refine ⟨Quotient.mk _ φ, ?_⟩
  apply Subtype.ext
  show orbitMultiset φ = M
  have hequi : ∀ (a : Z2) (x : ModelSpace M.toList), e0 (a • x) = φ a • e0 x := by
    intro a x
    show e0 (a • x) = (Equiv.permCongr e0 (MulAction.toPerm a)) (e0 x)
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, MulAction.toPerm_apply]
  have htrans : orbitMultiset φ = actionOrbitMultiset (ModelSpace M.toList) := by
    exact @actionOrbitMultiset_congr (ModelSpace M.toList) _ _ (Fin n)
      (permAction φ) _ e0 hequi
  rw [htrans, actionOrbitMultiset_modelSpace, Multiset.coe_toList]

/-! ### K2b: injectivity — the stabilizer multiset is a complete invariant -/

/-- The canonical decomposition map: a pair (orbit, coset of its stabilizer)
names a point. -/
def quotDecomp (X : Type*) [MulAction Z2 X]
    (p : Σ ω : orbitRel.Quotient Z2 X, Z2 ⧸ stabilizer Z2 (Quotient.out ω)) : X :=
  Quotient.liftOn p.2 (fun g => g • Quotient.out p.1) (by
    intro g h hgh
    have hmem : g⁻¹ * h ∈ stabilizer Z2 (Quotient.out p.1) :=
      (QuotientGroup.leftRel_apply).mp hgh
    have hfix : (g⁻¹ * h) • Quotient.out p.1 = Quotient.out p.1 := hmem
    show g • Quotient.out p.1 = h • Quotient.out p.1
    have hh : h = g * (g⁻¹ * h) := by rw [← mul_assoc, mul_inv_cancel, one_mul]
    conv_rhs => rw [hh]
    rw [mul_smul, hfix])

/-- Decomposition on a named coset representative. -/
theorem quotDecomp_mk (X : Type*) [MulAction Z2 X] (ω : orbitRel.Quotient Z2 X)
    (g : Z2) :
    quotDecomp X ⟨ω, QuotientGroup.mk g⟩ = g • Quotient.out ω := rfl

/-- Decomposition is equivariant. -/
theorem quotDecomp_equivariant (X : Type*) [MulAction Z2 X] (a : Z2)
    (p : Σ ω : orbitRel.Quotient Z2 X, Z2 ⧸ stabilizer Z2 (Quotient.out ω)) :
    quotDecomp X (a • p) = a • quotDecomp X p := by
  obtain ⟨ω, q⟩ := p
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have h1 : a • (⟨ω, QuotientGroup.mk g⟩ :
      Σ ω : orbitRel.Quotient Z2 X, Z2 ⧸ stabilizer Z2 (Quotient.out ω)) =
    ⟨ω, QuotientGroup.mk (a * g)⟩ := by
    rw [Sigma.smul_mk, MulAction.Quotient.smul_mk, smul_eq_mul]
  rw [h1, quotDecomp_mk, quotDecomp_mk, mul_smul]

/-- Decomposition is a bijection. -/
theorem quotDecomp_bijective (X : Type*) [MulAction Z2 X] :
    Bijective (quotDecomp X) := by
  constructor
  · rintro ⟨ω, q⟩ ⟨ω', q'⟩ h
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective q'
    rw [quotDecomp_mk, quotDecomp_mk] at h
    have hω : ω = ω' := by
      have h1 : (Quotient.mk _ (g • Quotient.out ω) : orbitRel.Quotient Z2 X) = ω := by
        have hs : (Quotient.mk _ (g • Quotient.out ω) : orbitRel.Quotient Z2 X) =
            Quotient.mk _ (Quotient.out ω) := Quotient.sound ⟨g, rfl⟩
        rw [hs, Quotient.out_eq]
      have h2 : (Quotient.mk _ (g' • Quotient.out ω') : orbitRel.Quotient Z2 X) = ω' := by
        have hs : (Quotient.mk _ (g' • Quotient.out ω') : orbitRel.Quotient Z2 X) =
            Quotient.mk _ (Quotient.out ω') := Quotient.sound ⟨g', rfl⟩
        rw [hs, Quotient.out_eq]
      rw [← h1, ← h2, h]
    subst hω
    have hg : (QuotientGroup.mk g : Z2 ⧸ stabilizer Z2 (Quotient.out ω)) =
        QuotientGroup.mk g' := by
      rw [QuotientGroup.eq]
      show (g⁻¹ * g') • Quotient.out ω = Quotient.out ω
      rw [mul_smul, ← h, ← mul_smul, inv_mul_cancel, one_smul]
    rw [hg]
  · intro x
    have hrel : (orbitRel Z2 X) (Quotient.out (Quotient.mk _ x : orbitRel.Quotient Z2 X)) x :=
      Quotient.mk_out x
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp ((orbitRel_apply).mp hrel)
    refine ⟨⟨Quotient.mk _ x, QuotientGroup.mk g⁻¹⟩, ?_⟩
    rw [quotDecomp_mk]
    rw [← hg, ← mul_smul, inv_mul_cancel, one_smul]

/-- Decomposition as an equivalence. -/
noncomputable def quotDecompEquiv (X : Type*) [MulAction Z2 X] :
    (Σ ω : orbitRel.Quotient Z2 X, Z2 ⧸ stabilizer Z2 (Quotient.out ω)) ≃ X :=
  Equiv.ofBijective _ (quotDecomp_bijective X)

/-- Inverses of equivariant bijections are equivariant. -/
theorem equivariant_symm {α β : Type*} [MulAction Z2 α] [MulAction Z2 β]
    (f : α ≃ β) (hf : ∀ (a : Z2) (x : α), f (a • x) = a • f x) (a : Z2) (y : β) :
    f.symm (a • y) = a • f.symm y :=
  f.injective (by rw [Equiv.apply_symm_apply, hf, Equiv.apply_symm_apply])

/-- **The reassembly theorem.** Two finite ℤ²-sets with the same stabilizer
multiset are equivariantly isomorphic. -/
theorem exists_equivariant_of_actionOrbitMultiset_eq {X Y : Type*}
    [MulAction Z2 X] [MulAction Z2 Y] [Finite X] [Finite Y]
    (h : actionOrbitMultiset X = actionOrbitMultiset Y) :
    ∃ f : X ≃ Y, ∀ (a : Z2) (x : X), f (a • x) = a • f x := by
  letI := Fintype.ofFinite (orbitRel.Quotient Z2 X)
  letI := Fintype.ofFinite (orbitRel.Quotient Z2 Y)
  rw [actionOrbitMultiset, actionOrbitMultiset] at h
  obtain ⟨e, he⟩ := exists_equiv_of_map_univ_eq (actionStabPack X) (actionStabPack Y) h
  have hstab : ∀ ω : orbitRel.Quotient Z2 X,
      stabilizer Z2 (Quotient.out (e ω)) = stabilizer Z2 (Quotient.out ω) := by
    intro ω
    have hval := congrArg Subtype.val (he ω)
    exact Subgroup.toAddSubgroup'.injective hval
  let F : ∀ ω : orbitRel.Quotient Z2 X,
      (Z2 ⧸ stabilizer Z2 (Quotient.out ω)) ≃ (Z2 ⧸ stabilizer Z2 (Quotient.out (e ω))) :=
    fun ω => (QuotientGroup.quotientMulEquivOfEq (hstab ω).symm).toEquiv
  let mid : (Σ ω : orbitRel.Quotient Z2 X, Z2 ⧸ stabilizer Z2 (Quotient.out ω)) ≃
      (Σ ω' : orbitRel.Quotient Z2 Y, Z2 ⧸ stabilizer Z2 (Quotient.out ω')) :=
    Equiv.sigmaCongr e F
  refine ⟨(quotDecompEquiv X).symm.trans (mid.trans (quotDecompEquiv Y)), ?_⟩
  intro a x
  simp only [Equiv.trans_apply]
  have h1 : (quotDecompEquiv X).symm (a • x) = a • (quotDecompEquiv X).symm x :=
    equivariant_symm _ (quotDecomp_equivariant X) a x
  rw [h1]
  have h2 : ∀ p : Σ ω : orbitRel.Quotient Z2 X, Z2 ⧸ stabilizer Z2 (Quotient.out ω),
      mid (a • p) = a • mid p := by
    rintro ⟨ω, q⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hs : a • (⟨ω, QuotientGroup.mk g⟩ :
        Σ ω : orbitRel.Quotient Z2 X, Z2 ⧸ stabilizer Z2 (Quotient.out ω)) =
      ⟨ω, QuotientGroup.mk (a * g)⟩ := by
      rw [Sigma.smul_mk, MulAction.Quotient.smul_mk, smul_eq_mul]
    rw [hs]
    show (⟨e ω, F ω (QuotientGroup.mk (a * g))⟩ :
        Σ ω' : orbitRel.Quotient Z2 Y, Z2 ⧸ stabilizer Z2 (Quotient.out ω')) =
      a • ⟨e ω, F ω (QuotientGroup.mk g)⟩
    have hF : ∀ u : Z2, F ω (QuotientGroup.mk u) = QuotientGroup.mk u := fun u =>
      QuotientGroup.quotientMulEquivOfEq_mk _ u
    rw [hF, hF, Sigma.smul_mk, MulAction.Quotient.smul_mk, smul_eq_mul]
  rw [h2]
  exact quotDecomp_equivariant Y a _

/-- **K2b.** The classifying map is injective. -/
theorem classifyOrbit_injective (n : ℕ) : Injective (classifyOrbit n) := by
  refine Quotient.ind (fun φ => Quotient.ind (fun ψ => fun h => ?_))
  have hms : orbitMultiset φ = orbitMultiset ψ := congrArg Subtype.val h
  obtain ⟨f, hf⟩ := @exists_equivariant_of_actionOrbitMultiset_eq (Fin n) (Fin n)
    (permAction φ) (permAction ψ) _ _ hms
  apply Quotient.sound
  refine ⟨(ConjAct.toConjAct f)⁻¹, ?_⟩
  show (ConjAct.toConjAct f)⁻¹ • ψ = φ
  apply MonoidHom.ext
  intro a
  apply Equiv.ext
  intro x
  show (ConjAct.ofConjAct (ConjAct.toConjAct f)⁻¹ * ψ a *
      (ConjAct.ofConjAct (ConjAct.toConjAct f)⁻¹)⁻¹) x = φ a x
  rw [map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  have hfx : f (φ a x) = ψ a (f x) := hf a x
  rw [← hfx, Equiv.Perm.inv_def, Equiv.symm_apply_apply]

/-- The classifying map is a bijection. -/
theorem classifyOrbit_bijective (n : ℕ) : Bijective (classifyOrbit n) :=
  ⟨classifyOrbit_injective n, classifyOrbit_surjective n⟩

end

/-! ### The annotation, proved -/

/-- **K2, packaged.**  Conjugacy classes of ℤ²-representations on `Fin n`
correspond to weight-`n` multisets of finite-index subgroups of ℤ², via the
stabilizer-multiset invariant (`classifyOrbit`), which is well defined by
`orbitMultiset_conj_smul`, injective by the reassembly theorem
`exists_equivariant_of_actionOrbitMultiset_eq`, and surjective by the coset
model `ModelSpace`. -/
theorem z2RepClasses_equiv_weightedMS (n : ℕ) :
    Nonempty (orbitRel.Quotient (ConjAct (Equiv.Perm (Fin n))) (Z2 →* Equiv.Perm (Fin n)) ≃
      WeightedMS n) :=
  ⟨Equiv.ofBijective _ (classifyOrbit_bijective n)⟩

/-- **The A061256 annotation, in full**: the number of orbits of commuting
pairs of permutations of `n` points under simultaneous conjugation equals the
Euler transform of σ at `n`.  This machine-checks the "it appears" comment on
OEIS A061256 (blog observation by "Allan", recorded in the entry; the fact is
published — Liskovets–Mednykh 2009, genus-1 case — see header).  Chain:
commuting pairs = ℤ²-representations (`homEquivCommPair`), orbits =
conjugacy classes of representations (`z2RepsEquivCommPairOrbits`), which the
stabilizer multiset classifies (K2, `classifyOrbit_bijective`), and weighted
subgroup multisets are counted by the Euler transform of σ (K3
`card_weightedMS`, fed by the Hermite-normal-form count K1
`card_addSubgroup_index_eq_sigma1`). -/
theorem commPairClassCount_perm (n : ℕ) :
    commPairClassCount (Equiv.Perm (Fin n)) = a061256 n := by
  obtain ⟨e⟩ := z2RepClasses_equiv_weightedMS n
  rw [commPairClassCount_eq_card_z2Reps, Nat.card_congr e, card_weightedMS]
  rfl

end GroupCount.CommutingPairsEuler
