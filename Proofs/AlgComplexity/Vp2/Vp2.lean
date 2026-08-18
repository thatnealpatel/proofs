/-
  Vp2 — the OPEN QUESTION, made machine-precise (sorry-free since
  2026-07-12):

    "The (111) border apolarity test is structurally outside the
     algebraic natural-proofs framework: it is a smoothability search
     in the Hilbert scheme, not the evaluation of a polynomial in the
     tensor entries. Whether this structural distinction constitutes a
     provable escape from the barrier remains an open question."

  This began as a FEASIBILITY SURVEY (a sorry-skeleton). The file's job
  is to (a) give type-level objects for every noun in the sentence
  above, and (b) state the open question as a machine-precise `Prop`.
  Both are now done with real definitions: the last two `sorry`s
  (`Passes111`, `passes111_of_borderRankLE`) were discharged by the
  apolarity layer `AlgComplexity.Vp2.Apolarity` (see the 2026-07-12 WP-B
  CHANGELOG entry below for scope and recorded deviations). The
  smoothability/Hilbert-scheme side of the quoted sentence remains OUT
  OF MODELED SCOPE — the modeled verdict is CHL's (111) RANK TEST,
  documented loudly in §3 and in Apolarity.lean. Task cards for the
  missing full formalizations: `.tasks/research/docs/Vp2.md`.

  FOUNDATIONS NOTE (binding — see `.tasks/research/docs/Vp1.md`).
  The Vp1 resolution is UNPINNED-ANALOGY: *no primary source proves*
  that the (111) test escapes the algebraic natural-proofs barrier.
  Stating "the (111) test escapes" as a `theorem ... := by sorry` would
  assert a proof exists where none does — a mis-stated theorem, which
  the doctrine forbids. Therefore the open question is packaged here as
  a named `Prop` (`Vp2OpenQuestion`), NOT as a theorem we claim to have
  proved. Of the two facts the sources DO support (Np1 §2), (i)
  "flattening minors are VP-computable distinguishers covered by the
  barrier" is PROVED sorry-free at the family level
  (`exists_flattening_vpDistinguisher`), and (ii) "the (111) verdict
  has the wrong type to be such a distinguisher (it is an existential
  search over candidate graded-ideal data)" is now carried by REAL
  definitions instead of sorrys: `Passes111` quantifies over all
  polynomials vanishing on the accept locus of the existential search
  `Candidate111` (Vp2/Apolarity.lean) — a search over subspace triples,
  the low-degree graded pieces of a candidate apolar ideal — and the
  soundness anchor `passes111_of_borderRankLE` is proved over infinite
  fields. The smoothability witness in the original sentence is OUT OF
  MODELED SCOPE (no Hilbert scheme in Mathlib): the modeled verdict is
  CHL's (111) rank test, strictly weaker than the sources' full test,
  and every affected docstring says so. The final `theorem`
  (`vp2OpenQuestion_iff`, proved) records the EQUIVALENCE between
  the open question and a precise inexpressibility statement —
  formalizing that the open question is well-posed, not that it is
  resolved.

  Mathlib substrate actually reused (survey in docs/Vp2.md):
    · `MvPolynomial (entries) k`        — distinguisher polynomials       [EXISTS]
    · `MvPolynomial.eval`               — evaluation at the tensor entries [EXISTS]
    · `Matrix.det`                      — flattening / Koszul determinants [EXISTS]
    · `MvPolynomial.zeroLocus` /
      `MvPolynomial.vanishingIdeal`     — polynomial-closure border rank [EXISTS]
    · `Matrix.rank` + minor lemmas      — flattening rank bounds          [EXISTS]
    · `HomogeneousIdeal (graded ring)`  — Z-graded apolar candidate ideal  [EXISTS]
    · `Module.length`                   — length of a finite scheme        [EXISTS]
    · `IsReduced` / `Ideal.IsRadical`   — reduced = "distinct smooth pts"  [EXISTS]
  Nothing is `sorry`-defined here anymore. Of the infrastructure that
  was genuinely absent: polynomial-closure border rank is REAL
  (`AlgComplexity.Vp2.BorderRank`, imported below); arithmetic circuits are
  REAL
  (`AlgComplexity.Vp2.Circuit`, imported below — `Circuit`, `size`, `eval`,
  `ComputedInSize`, `VPFamily`), and since the 2026-07-12 family
  retyping this file's statements quantify over distinguisher FAMILIES
  via `VPFamily` (see the CHANGELOG below and §2); the low-degree
  APOLARITY layer used by the (111) rank test is REAL
  (`AlgComplexity.Vp2.Apolarity`, imported below — flattening/slice maps,
  `Candidate111`, `test111Locus`, the soundness core). Still absent
  from Mathlib and NOT modeled (documented scenery and docstrings, no
  sorrys): classical secant/cactus varieties as schemes, the Hilbert scheme
  of points, smoothability/Slip-membership.

  CHANGELOG (2026-07-12, task WP-B — the (111) test made real; the
  final two sorrys discharged, file now sorry-free):
    · `AlgComplexity.Vp2.Apolarity` (NEW, imported): concrete flattening and
      slice `LinearMap`s; the DUAL-form candidate condition
      `Candidate111` (CHL Prop 3.1 eq (7), arXiv:1911.07981; Hilbert
      function min-truncated per BB Thm 1.2, arXiv:1910.01944); the
      accept locus `test111Locus`; Lemma A-spread
      (`candidate111_of_linearIndependent`); the degenerate band
      (`candidate111_of_sq_le`); the soundness core
      `vanishingIdeal_test111Locus_le` (perturbation of an arbitrary
      rank decomposition along a polynomial line; `[Infinite k]`).
      Imported by the root: `Proofs/AlgComplexity.lean:1` is
      `import AlgComplexity.Vp2.Apolarity`, so this module is inside the
      default build target. (Supersedes an earlier note here claiming it was
      "NOT imported by root AlgComplexity.lean pending user sign-off on the
      import-list convention" — that claim contradicted the import graph.)
    · `Passes111` REAL (SORRY[Test111] discharged): the polynomial
      closure of `test111Locus` — the same closure wrap as
      `BorderRankLE`. DEVIATION (recorded): gains `[Field k]` (the
      sorry-era scaffold had no constraint on `k`).
    · `passes111_of_borderRankLE` PROVED (SORRY[Test111-sound]
      discharged) via `zeroLocus_anti_mono`. DEVIATION (recorded):
      gains `[Infinite k]` — BB/CHL prove the FULL Slip test sound over
      algebraically closed fields; the theorem here is about the WEAKER
      modeled (111) test's polynomial closure over any infinite field
      (strictly weaker hypothesis, strictly weaker test: different
      theorems, neither subsuming the other). Over finite `k` the
      closure degenerates pointwise and no claim is made.
    · NEW `passes111_iff` (unfold mirror of `borderRankLE_iff`),
      `Candidate111.passes111` (locus ⊆ closure, mirror of
      `RankLE.borderRankLE`), and the degenerate-parameter lemma
      `passes111_of_sq_le` (`n² ≤ r` ⟹ every tensor passes; hence the
      zero family decides such ranks and `Vp2OpenQuestion` is FALSE for
      eventually-degenerate rank families).
    · §3 prose and §4 docstrings scoped by the CONTENT WINDOW (WP-B
      adversarial review, MAJOR-1): the formalized question is
      informative exactly in the superlinear band
      `n ≲ r < 2n³/(3n−1)`; outside it the answer is settled by
      degenerate-parameter effects with no barrier content.
      `ApolarCandidate` stays as documented scenery (byte-identical).
    · Modeled-scope omissions, all documented (each RELAXES the test,
      so soundness is a fortiori): the (210)/(120)-family sibling
      pre-tests, the degree-(100) pieces (CHL set them to 0 by
      conciseness; a strict relaxation exactly when r < n), total
      degree ≥ 4, extendability to a genuine graded ideal,
      Borel-fixedness (a WLOG for CHL's search-side enumeration only;
      needs algebraically closed k), smoothability/Slip-membership
      (the cactus gap). See Apolarity.lean's header.

  CHANGELOG (2026-07-12, task VPCircuit — the family retyping):
    · `AlgComplexity.Vp2.Circuit` is now imported, and the single-n sorry-def
      `IsVP` is DELETED — discharged exactly as its annotation
      prescribed, by retyping the VP side of this file over FAMILIES
      `D : (n : ℕ) → MvPolynomial (EntryIndex n) k` quantified by the
      honest `VPFamily D` (∃ c, ∀ n, `D n` computed in size (n³ + c)^c,
      Circuit.lean). No pinned single-n size threshold anywhere; no
      statement weakened; three sorrys discharged (`IsVP`,
      `exists_flattening_vpDistinguisher`, `vp2OpenQuestion_iff`).
    · `VPDistinguisher` (single n) replaced by `VPDistinguisherFamily`
      over an n-indexed target rank `r : ℕ → ℕ`, with a `threshold`
      field: members must be nonzero and vanish on the polynomial-closure
      border-rank-≤ `r n` locus over that field for all `n ≥ threshold`.
      The "for sufficiently large n"
      quantifier is the standard asymptotic convention of the barrier
      literature: FSV (Defn 2.1) and GKSS quantify over poly-size
      circuit FAMILIES, whose size and agreement conditions are
      asymptotic. The fixed-n `Distinguisher` and the sorry-free
      `exists_flattening_distinguisher` STAY unchanged.
    · `exists_flattening_vpDistinguisher` retyped to constant-rank
      families and PROVED sorry-free: witness `flatteningMinorFamily`
      with threshold `r + 1`; legs by `flatteningMinorFamily_of_le` +
      `det_genericFlattening_submatrix_ne_zero`,
      `BorderRankLE.eval_det_genericFlattening_submatrix_eq_zero`, and
      `vpFamily_flatteningMinorFamily` (all Circuit/BorderRank.lean).
    · `DecidedByVP` / `Vp2OpenQuestion` retyped over families: one VP
      family whose vanishing agrees with `Passes111 T (r n)` for all
      `T`, for all `n` beyond some `n₀` (same asymptotic convention).
      `vp2OpenQuestion_iff` restated accordingly and PROVED (pure
      classical logic: unfold + `push Not`, Mathlib's current name for
      push_neg) — the well-posedness certificate is no longer a sorry.
    · Remaining sorrys (2, both on the (111) side, other task cards):
      the def `Passes111` (SORRY[Test111]) and the soundness anchor
      `passes111_of_borderRankLE` (SORRY[Test111-sound]); both are
      single-T, single-r statements, untouched by the retyping apart
      from `Passes111` now being referenced at rank `r n`.

  CHANGELOG (2026-07-11, task Pf2 — arithmetic circuit model):
    · `AlgComplexity.Vp2.Circuit` (NEW; imported here only since 2026-07-12 —
      Pf2 itself changed no statement in this file) provides the repo's
      first arithmetic-circuit-size infrastructure: `Circuit σ k`
      (expression trees), `size`,
      `eval : Circuit σ k → MvPolynomial σ k`, builders with exact size
      lemmas, the degree bound `totalDegree_eval_le`, completeness
      `exists_circuit` (every polynomial has a circuit, with explicit
      size), and the honest predicates `ComputedInSize s D` / `VPFamily D`.
    · The `isVP` leg's honest content is PROVED there: the flattening
      minor witnessing `exists_flattening_distinguisher` below is
      `ComputedInSize ((r+1)!·(2·(r+1)+4)+1)` — a bound constant in `n` —
      (`computedInSize_flatteningMinor`), and the fixed-r minor family is
      a genuine `VPFamily` (`vpFamily_flatteningMinorFamily`).
    · `IsVP` stayed sorry-defined ON PURPOSE at that point: "poly-size"
      at a single fixed `n` is vacuous — `Vp2.exists_computedInSize`
      proves EVERY polynomial is "computed in some size" — and any
      non-vacuous single-n reading would pin an arbitrary threshold, a
      dishonest definition. The honest discharge — retyping this file's
      objects over families — is exactly what the 2026-07-12 entry above
      records. No statement here was weakened.

  CHANGELOG (2026-07-11, task Pf1 — polynomial-closure border-rank
  infrastructure):
    · `BorderRankLE` is no longer `sorry`-defined. Vp2/BorderRank.lean
      defines it as membership of `entries T` in the zero locus of the
      vanishing ideal of the rank-≤ r locus (`MvPolynomial.zeroLocus`,
      `MvPolynomial.vanishingIdeal`; Mathlib.RingTheory.Nullstellensatz).
      This formalizes only polynomial-closure membership over the chosen
      field. Equivalence over `ℂ` with classical complex border rank requires
      a separate bridge through algebraic closedness, Segre secant loci,
      Zariski closure, and the relevant topology; that bridge is not proved
      here. This polynomial-closure property is exactly what
      `Distinguisher.vanishes` consumes. See the header of BorderRank.lean.
    · `Tensor3`, `EntryIndex`, `entries`, `flattening` moved VERBATIM to
      Vp2/BorderRank.lean, which now sits upstream of this file.
    · `Distinguisher` / `VPDistinguisher` binders strengthened from
      `CommSemiring k` to `Field k`: the real `BorderRankLE` needs a
      field (Mathlib's `zeroLocus` is field-valued), and every downstream
      theorem here already assumed one.
    · NEW sorry-free `exists_flattening_distinguisher`: flattening minors
      are genuine distinguishers (`ne_zero` + `vanishes` both proved).
      Of `exists_flattening_vpDistinguisher` only the `isVP` leg remained
      open, blocked solely on the `VPCircuit` task card (discharged
      2026-07-12 — see the entry above).

  Primary sources (labels/lines as in docs/Vp1.md, docs/Np1.md):
    FSV  arXiv:1701.05328  Defn 2.1 (distinguisher), barrier theorem.
    GKSS arXiv:1701.01717  algebraic natural proofs = succinct hitting set.
    CHL  arXiv:1911.07981  border apolarity, the (210)/(120)/(111) tests.
    Buczynski arXiv:2602.11309  cactus barrier, smoothability = breaking it.

  AI disclosure: skeleton produced with AI assistance (see Proofs/README).
-/
import AlgComplexity.Vp2.Apolarity
import AlgComplexity.Vp2.BorderRank
import AlgComplexity.Vp2.Circuit
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Length

namespace Vp2

open scoped Classical

/-! ## 0. Base objects: tensors and their entry vectors

`Tensor3`, `EntryIndex`, `entries`, and the `j`-flattening `flattening`
now live in `AlgComplexity.Vp2.BorderRank` (imported above, same namespace),
together with the ordinary rank-≤ `r` locus and polynomial-closure border
rank over the chosen field. -/

/-! ## 1. Polynomial-closure border rank  [REAL — AlgComplexity.Vp2.BorderRank]

`BorderRankLE T r` is no longer `sorry`-defined. BorderRank.lean defines
it as membership of `entries T` in
`zeroLocus k (vanishingIdeal k (rankLocus k n r))`: every polynomial
vanishing on all rank-≤ r tensors vanishes at `T` (`borderRankLE_iff`).
Only polynomial-closure membership over the arbitrary field is formalized.
Equivalence over `ℂ` with classical complex border rank requires a separate
bridge through algebraic closedness, the Segre secant locus, Zariski closure,
and the relevant topology; that bridge is not proved here. This
polynomial-closure property is precisely what `Distinguisher.vanishes` below
consumes. Supporting infrastructure proved there, all sorry-free:
`RankLE.borderRankLE`, monotonicity in `r` of both notions, the
flattening rank bound `RankLE.rank_flattening_le`, minor vanishing
`det_submatrix_eq_zero_of_rank_le`, and the generic flattening minors
(nonzero as polynomials; identically zero on the formal polynomial-closure
border-rank locus). -/

/-! ## 2. VP-computable distinguishers  [circuit model: AlgComplexity.Vp2.Circuit]

A distinguisher (FSV Defn 2.1) is a nonzero `D ∈ k[c_{ijk}]` vanishing on
all `T` with `BorderRankLE T r`. It is *VP-natural* when `D` is computed
by a poly(N)-size algebraic circuit (`N = n³`). Mathlib still has no
algebraic computation model ("circuit" = matroid circuit), but this
development does: `AlgComplexity.Vp2.Circuit` (task Pf2, imported above) defines
expression trees with `size`/`eval` into `MvPolynomial`, the honest
fixed-bound predicate `ComputedInSize s D`, and the family-level class
`VPFamily`. "Poly-size" is a growth condition on a FAMILY, not on one
polynomial at one `n` — at any fixed `n` EVERY polynomial is computed in
*some* size (`Vp2.exists_computedInSize`) — so the VP-natural objects
below are families quantified via `VPFamily` directly; the former
single-n `IsVP` sorry-def is gone (see the retrospective note below). -/

/-! #### Retrospective (2026-07-12): the former `IsVP` sorry-def is gone

Until 2026-07-12 this file carried
`def IsVP (n : ℕ) (D : MvPolynomial (EntryIndex n) k) : Prop := sorry`
(SORRY[VPCircuit-family]) — opaque because a non-vacuous "poly(n³)-size"
predicate cannot exist at one fixed `n`: every polynomial is computed in
*some* size (`Vp2.exists_computedInSize`, Circuit.lean), and any
non-vacuous single-n reading would pin an arbitrary size threshold, a
dishonest definition. Its annotation prescribed the honest discharge:
retype `VPDistinguisher` / `DecidedByVP` / `Vp2OpenQuestion` /
`vp2OpenQuestion_iff` over distinguisher FAMILIES quantified by
`VPFamily` (Circuit.lean). That retyping is now done — see
`VPDistinguisherFamily`, `DecidedByVP`, `Vp2OpenQuestion` below — so the
sorry is DISCHARGED BY DELETION: there is no per-`n` "IsVP" predicate to
define, and nothing below is blocked on the circuit model. -/

/-- A *distinguisher* for the formal polynomial-closure border-rank-`≤ r`
locus over `k`: a nonzero polynomial in the tensor entries that vanishes on
every tensor satisfying `BorderRankLE T r`. FSV Defn 2.1 is source-side
language about the classical secant variety `σ_r(Seg)`; identifying that
variety with this formal locus over `ℂ` requires the separate algebraically
closed/secant/Zariski/topological bridge not proved here. `[Field k]` is
required because `BorderRankLE` is field-valued. -/
structure Distinguisher (k : Type*) [Field k] (n r : ℕ) where
  /-- the polynomial in the `n³` entry variables -/
  poly : MvPolynomial (EntryIndex n) k
  /-- it is not identically zero -/
  ne_zero : poly ≠ 0
  /-- it vanishes on the formal polynomial-closure border-rank-`≤ r` locus -/
  vanishes : ∀ T : Tensor3 k n, BorderRankLE T r → MvPolynomial.eval (entries T) poly = 0

/-- A *VP-natural proof* against the formal polynomial-closure border-rank
loci at ranks `r n`, over `k`, at
the honest family level: for each side `n` a polynomial `poly n` in the
`n³` tensor entries which, for every sufficiently large `n`
(`threshold ≤ n`), is a genuine distinguisher for rank `r n` — nonzero
and vanishing on the whole polynomial-closure border-rank-≤ `r n` locus —
and which as a family is VP-computable (`VPFamily`, Circuit.lean). This is
exactly the
object the algebraic natural-proofs barrier governs (Np1 §2d, item 4):
FSV Defn 2.1 / GKSS quantify over poly-size circuit FAMILIES, and their
size and agreement conditions are asymptotic, whence the `threshold`
("for sufficiently large n") field. At each `n ≥ threshold` the data
specializes to a fixed-n `Distinguisher k n (r n)`. -/
structure VPDistinguisherFamily (k : Type*) [Field k] (r : ℕ → ℕ) where
  /-- for each side `n`, a polynomial in the `n³` entry variables -/
  poly : (n : ℕ) → MvPolynomial (EntryIndex n) k
  /-- distinguishing is required only from this side on — the standard
  "for sufficiently large `n`" of asymptotic complexity -/
  threshold : ℕ
  /-- beyond the threshold, the member is not identically zero -/
  ne_zero : ∀ n, threshold ≤ n → poly n ≠ 0
  /-- beyond the threshold, the member vanishes on the whole formal
  polynomial-closure border-rank-≤ `r n` locus over `k`. The classical
  source-side notation `σ_{r n}(Seg)` requires the separate bridge noted
  above and is not identified with this locus here. -/
  vanishes : ∀ n, threshold ≤ n → ∀ T : Tensor3 k n,
    BorderRankLE T (r n) → MvPolynomial.eval (entries T) (poly n) = 0
  /-- the family is VP-computable: computed by circuits of size
  polynomial in `n³` -/
  isVP : VPFamily poly

/-! ### 2a. Flattenings are VP-distinguishers (the SUPPORTED fact)

The `(j)`-flattening of `T` is the `n × n²` matrix `M_T` with
`(M_T)_{i,(j,k)} = c_{ijk}` (`flattening`, now in BorderRank.lean); if
`BorderRankLE T r` then this matrix has rank `≤ r`, so every
`(r+1)×(r+1)` minor (a degree-`r+1` determinantal polynomial in the
entries) vanishes (Np1 §2; Sager: 84 degree-3 minors witness this for
`n = r = 3`). ALL legs of this supported fact are now PROVED, sorry-free:
at fixed `n`, `exists_flattening_distinguisher` (via Vp2/BorderRank.lean)
gives the nonzero minor vanishing on the whole formal polynomial-closure
border-rank-≤ `r` locus over the chosen field; at
the family level, `exists_flattening_vpDistinguisher` (via
Vp2/Circuit.lean) adds VP-computability of the minor family. -/

/-- Flattening minors are genuine distinguishers for the formal
polynomial-closure border-rank-`≤ r` locus whenever `r + 1 ≤ n`: a fixed
`(r+1)×(r+1)` minor of the generic flattening is a nonzero polynomial in the
tensor entries (BorderRank.lean §5) that vanishes on every tensor of
polynomial-closure border rank at most `r` (BorderRank.lean §6). The source
literature describes the corresponding classical complex locus as
`σ_r(Seg)`, but that correspondence needs the separate bridge not proved
here. Sorry-free — the fixed-`n` part of the SUPPORTED fact (Np1 §2);
VP-computability of the minor family is added, also sorry-free, by
`exists_flattening_vpDistinguisher` below. -/
theorem exists_flattening_distinguisher
    {k : Type*} [Field k] {n r : ℕ} (h : r + 1 ≤ n) :
    Nonempty (Distinguisher k n r) :=
  ⟨{ poly := ((genericFlattening k n).submatrix (Fin.castLE h)
        fun t => (Fin.castLE h t, Fin.castLE h t)).det
     ne_zero := det_genericFlattening_submatrix_ne_zero (Fin.castLE_injective h)
        fun _ _ htt' => Fin.castLE_injective h (congrArg Prod.fst htt')
     vanishes := fun _T hT => hT.eval_det_genericFlattening_submatrix_eq_zero _ _ }⟩

/-- **Flattening minors are a VP-natural proof** (the SUPPORTED fact,
Np1 §2 — now sorry-free end to end). For every fixed target rank `r`,
the family of `(r+1)×(r+1)` diagonal minors of the generic flattening
(`flatteningMinorFamily`, Circuit.lean) is a `VPDistinguisherFamily`
for the constant rank function `fun _ => r`, with threshold `r + 1`
(the side must be large enough for the minor to be nontrivial). Legs:
nonzero on injective picks (`det_genericFlattening_submatrix_ne_zero`);
vanishing on the formal polynomial-closure border-rank-≤ `r` locus
(`BorderRankLE.eval_det_genericFlattening_submatrix_eq_zero`);
VP-computability (`vpFamily_flatteningMinorFamily` — Leibniz circuits
of size `(r+1)!·(2(r+1)+4)+1`, constant in `n`). Hence the barrier's
hypothesis is nonvacuous for the tensor setting. -/
theorem exists_flattening_vpDistinguisher {k : Type*} [Field k] (r : ℕ) :
    Nonempty (VPDistinguisherFamily k (fun _ => r)) :=
  ⟨{ poly := flatteningMinorFamily k r
     threshold := r + 1
     ne_zero := fun n hn => by
       rw [flatteningMinorFamily_of_le hn]
       exact det_genericFlattening_submatrix_ne_zero (Fin.castLE_injective hn)
         fun _ _ htt' => Fin.castLE_injective hn (congrArg Prod.fst htt')
     vanishes := fun n hn T hT => by
       rw [flatteningMinorFamily_of_le hn]
       exact hT.eval_det_genericFlattening_submatrix_eq_zero _ _
     isVP := vpFamily_flatteningMinorFamily k r }⟩

/-! ## 3. The (111) border apolarity test  [modeled: AlgComplexity.Vp2.Apolarity]

The structurally DIFFERENT object. CHL's algorithm enumerates Borel-fixed
graded ideals (candidate apolar ideals of length-`r` schemes) and checks
rank conditions; the (111) verdict is sound because the candidate must be
the flat limit of ideals of *smooth* (reduced) length-`r` schemes —
i.e. a smoothability search in the Hilbert scheme (Vp1 §2, Cb1 §1).

Modeled for real (Vp2/Apolarity.lean): the (111) RANK TEST itself — the
candidate search `Candidate111` over subspace triples (the
(110)/(101)/(011) graded pieces of a candidate ideal, in the dual form
of CHL Prop 3.1 eq (7)) — and, below, the polynomial closure of its
accept locus (`Passes111`). The verdict is `∃` over candidates, not
`eval` of a polynomial: exactly the type mismatch this file is about.

Documented scenery only (`ApolarCandidate` below): the full graded-ideal
picture with scheme length and the SMOOTHABILITY witness — what the
sources' full test adds on top of the rank test, and what Mathlib cannot
yet express (no Hilbert scheme of points, no smoothable component). Its
omission from `Candidate111` RELAXES the modeled test, which keeps the
soundness direction (`passes111_of_borderRankLE`) honest a fortiori. -/

variable (S : Type*) [CommRing S]

/-- A candidate apolar ideal for the (111) test: a homogeneous (graded)
ideal of the coordinate/Cox ring `S`, recording its scheme length and
whether it is a flat limit of *smoothable* (reduced) ideals. Mathlib
supplies `HomogeneousIdeal` and `Module.length`; smoothability is opaque.

`𝒜` is the grading datum on `S` (an internal grading by some monoid `ι`). -/
structure ApolarCandidate {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    (𝒜 : ι → Submodule ℤ S) [GradedAlgebra 𝒜] where
  /-- the candidate graded ideal `I ⊆ S` (CHL: Borel-fixed; we keep only
  the homogeneity, which is the Mathlib-expressible part) -/
  ideal : HomogeneousIdeal 𝒜
  /-- the length of the quotient scheme `Spec(S/I)`; for an apolar scheme
  of a source-side classical border-rank-`r` decomposition this equals `r` -/
  length : ℕ
  /-- SMOOTHABILITY witness: `I` is the flat limit of homogeneous ideals
  of *reduced* (distinct-point) length-`length` schemes. This is the
  Hilbert-scheme condition that makes the (111) test sound and is exactly
  what is ABSENT from Mathlib (no Hilbert scheme of points, no smoothable
  component). Opaque pending the `Smoothability` task card. -/
  smoothable : Prop

/-- `Passes111 T r` : the (111) border-apolarity verdict for `T` at
target rank `r`, in polynomial-closure form: `entries T` lies in the
zero locus of the vanishing ideal of the accept locus `test111Locus` of
the modeled (111) candidate search (`Candidate111`, Vp2/Apolarity.lean)
— every polynomial in the `n³` entry variables that vanishes at all
tensors passing the modeled (111) test also vanishes at `T`.

SHAPE HONESTY (the crux): `Candidate111` is an existential SEARCH over
subspace triples — the (110)/(101)/(011) graded pieces of a candidate
apolar ideal, per CHL §2.3 (i)–(ii) + §3(iii) eq (4), in the dual form
of Prop 3.1 eq (7) — and `Passes111` quantifies over ALL polynomials
vanishing on that search's accept locus. Neither is
`MvPolynomial.eval D (entries T)` for any fixed `D`; whether some VP
family can nonetheless DECIDE the verdict is exactly `DecidedByVP` (§4).

MODELED SCOPE: the sources' full verdict additionally demands the
(210)/(120)-family pre-tests, degree-(100) conditions, all higher
degrees, extendability to a genuine graded ideal, Borel-fixedness
(search-side WLOG), and the SMOOTHABILITY/Slip-membership witness (the
`ApolarCandidate` scenery above). All are omitted here — each omission
RELAXES the test; see Apolarity.lean's header and the CHL digest.

CLOSURE HONESTY: the wrap mirrors `BorderRankLE` (the file's
established envelope). Over an algebraically closed field the accept
set of the MODELED test is expected to be Zariski-closed by elimination
theory (properness of the Grassmannian incidence variety plus
closedness of the rank conditions), making the wrap a no-op there; BB's
projectivity of Slip is the ANALOGOUS statement for the FULL test,
cited as analogy only, not as the operative mechanism. Over a general
field this is the polynomial-closure notion; over a FINITE field the
closure degenerates (`Passes111 ⟺ Candidate111` pointwise) and no
soundness claim is made (`passes111_of_borderRankLE` needs
`[Infinite k]`).

CONTENT WINDOW: `Passes111 · r` is identically True for `n² ≤ r`
(`passes111_of_sq_le` below) — in fact already for
`r ≥ ⌈2n³/(3n−1)⌉ ≈ (2/3)n²` (dimension count, recorded in
Apolarity.lean's header, not formalized) — and for `r < n` the verdict
is expected to be undecidable by any single polynomial over
algebraically closed fields (codimension ≥ 2 accept set vs codimension
1 hypersurfaces). The informative band is superlinear `r`:
matrix-multiplication territory. See §4.

DEVIATION (recorded in the CHANGELOG): gains `[Field k]` — the
sorry-era scaffold had no constraint on `k`; the real definition needs
the field-valued `zeroLocus`/`vanishingIdeal` vocabulary and the
dimension conditions, like `BorderRankLE` before it. -/
def Passes111 {k : Type*} [Field k] {n : ℕ} (T : Tensor3 k n) (r : ℕ) : Prop :=
  entries T ∈
    MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k (test111Locus k n r))

/-- The defining property, unfolded (mirror of `borderRankLE_iff`):
passing means every polynomial vanishing on the (111) accept locus
vanishes at `entries T`. -/
theorem passes111_iff {k : Type*} [Field k] {n : ℕ} {T : Tensor3 k n} {r : ℕ} :
    Passes111 T r ↔
      ∀ p ∈ MvPolynomial.vanishingIdeal k (test111Locus k n r),
        MvPolynomial.eval (entries T) p = 0 :=
  Iff.rfl

/-- A tensor satisfying the candidate search passes the test: the locus
is contained in the zero locus of its own vanishing ideal (mirror of
`RankLE.borderRankLE`). -/
theorem Candidate111.passes111 {k : Type*} [Field k] {n : ℕ} {T : Tensor3 k n}
    {r : ℕ} (h : Candidate111 T r) : Passes111 T r :=
  MvPolynomial.zeroLocus_vanishingIdeal_le (test111Locus k n r) ⟨T, h, rfl⟩

/-- DEGENERATE-PARAMETER LEMMA (labeled as such on purpose — see the
content-window notes in §4 and Apolarity.lean). For `n² ≤ r` EVERY
tensor passes the modeled (111) test, because `Candidate111` is
satisfied by the full spaces (`candidate111_of_sq_le`). Consequently
the ZERO family decides `Passes111 · (r n)` for any rank family with
eventually `n² ≤ r n`, so `DecidedByVP` holds and `Vp2OpenQuestion` is
FALSE there: a parameter artifact with no barrier content, NOT a
resolution of the open question, which lives in the superlinear band.
Needs neither `[Infinite k]` nor any closure argument. -/
theorem passes111_of_sq_le {k : Type*} [Field k] {n r : ℕ} (hr : n * n ≤ r)
    (T : Tensor3 k n) : Passes111 T r :=
  (candidate111_of_sq_le hr T).passes111

/-! ## 4. The open question, made precise

The barrier governs *polynomial* distinguisher families (§2). The (111)
verdict (§3) is an existential search. The OPEN QUESTION (Vp1,
UNPINNED-ANALOGY) is whether the (111) verdict can nonetheless be
*re-expressed* as the output of some VP-computable distinguisher family
— equivalently, whether the constructible sets `{T : Passes111 T (r n)}`
are cut out (as decisions, for all sufficiently large `n`) by the
vanishing of one VP family. No source resolves this either way.

CONTENT WINDOW (WP-B adversarial review, MAJOR-1 — a binding scope
note). With `Passes111` real, the question is contentful only for rank
families in the superlinear band `n ≲ r n < 2n³/(3n−1)`:
  · if eventually `n² ≤ r n` (in fact already `r n ≥ ⌈2n³/(3n−1)⌉`, by
    a dimension count not formalized here), then `Passes111 · (r n)` is
    identically True (`passes111_of_sq_le`), the ZERO family decides it
    (`VPFamily (fun _ => 0)` holds via `computedInSize_zero`,
    Circuit.lean), so `DecidedByVP k r` HOLDS and `Vp2OpenQuestion k r`
    is FALSE — a degenerate-parameter artifact, not barrier content;
  · for `r n < n` the accept set is expected (over algebraically closed
    fields) to have codimension ≥ 2 while a nonzero polynomial's zero
    set has a codimension-1 component, so `Vp2OpenQuestion` there is
    expected TRUE for pure dimension-counting reasons — again no
    barrier content (not formalized: needs Krull dimension of
    determinantal loci).
The source-side generic complex border-rank heuristic
`n³/(3n−2) ≈ n²/3` sits a factor ~2 below the vacuity threshold; relating
that classical secant-variety quantity to formal `BorderRankLE` requires the
separate bridge not proved here. Matrix-multiplication-type parameters
`r n ~ n^(1+ε)` live inside the informative band, so the intended reading of
`Vp2OpenQuestion` survives — stated out loud rather than implied. -/

/-- `DecidedByVP k r` says a VP family decides the (111) test at target
rank `r n`: there is one VP-computable family `D` of polynomials in the
tensor entries whose vanishing at `entries T` matches `Passes111 T (r n)`
for *all* `T`, for all sufficiently large `n` (the `n₀` cutoff — the same
asymptotic convention as `VPDistinguisherFamily.threshold`).

Degenerate-parameter honesty: for rank families with eventually
`n² ≤ r n` this HOLDS vacuously via the zero family
(`passes111_of_sq_le` makes the right side identically True and
`computedInSize_zero` makes `fun _ => 0` a `VPFamily`); see the §4
content window above. The question is informative only in the
superlinear band. -/
def DecidedByVP (k : Type*) [Field k] (r : ℕ → ℕ) : Prop :=
  ∃ D : (n : ℕ) → MvPolynomial (EntryIndex n) k, VPFamily D ∧
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ T : Tensor3 k n,
      (MvPolynomial.eval (entries T) (D n) = 0 ↔ Passes111 T (r n))

/-- **The open question (Vp2OpenQuestion).** For matrix-multiplication–type
parameters (a target-rank growth `r : ℕ → ℕ` inside the informative
band — see the §4 content window), the modeled (111) border apolarity
verdict is *not* decided by any VP-computable family of polynomials in
the tensor entries. Packaged as a `Prop`, not a theorem: Vp1 establishes
that no primary source proves or refutes it there. A proof would be a
genuine escape from the natural-proofs barrier; a refutation would place
the modeled (111) test back inside it. OUTSIDE the band the `Prop` is
not open: it is FALSE for eventually-degenerate rank families
(`n² ≤ r n` — zero family + `passes111_of_sq_le`) and expected TRUE for
`r n < n` by dimension counting; both are degenerate-parameter artifacts
without barrier content. -/
def Vp2OpenQuestion (k : Type*) [Field k] (r : ℕ → ℕ) : Prop :=
  ¬ DecidedByVP k r

/-- Well-posedness, the formal content actually delivered: the open
question is equivalent to the precise inexpressibility statement "for
every VP-computable family `D` and every cutoff `n₀` there are a side
`n ≥ n₀` and a tensor `T` on which the vanishing of `D n` disagrees with
the (111) verdict at rank `r n`". This is a tautological unfolding (pure
classical logic) — its only purpose is to certify that `Vp2OpenQuestion`
is a sharply stated mathematical proposition, NOT that it has been
answered. -/
theorem vp2OpenQuestion_iff (k : Type*) [Field k] (r : ℕ → ℕ) :
    Vp2OpenQuestion k r ↔
      ∀ D : (n : ℕ) → MvPolynomial (EntryIndex n) k, VPFamily D →
        ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧ ∃ T : Tensor3 k n,
          ¬ (MvPolynomial.eval (entries T) (D n) = 0 ↔ Passes111 T (r n)) := by
  unfold Vp2OpenQuestion DecidedByVP
  push Not
  rfl

/-- Soundness anchor for the modeled test (the supported direction of
CHL's method, Vp1 §2d): if `T` has formal polynomial-closure border rank at
most `r` over the chosen infinite field, the (111) test
passes. Proof: `vanishingIdeal_test111Locus_le` (Vp2/Apolarity.lean —
Lemma A-spread plus the perturbation of an arbitrary rank decomposition
along a polynomial line) gives
`vI (test111Locus) ≤ vI (rankLocus)`; `zeroLocus` antitonicity turns
that into `zeroLocus (vI (rankLocus)) ⊆ zeroLocus (vI (test111Locus))`,
i.e. `BorderRankLE → Passes111`.

CONVERSE FAILURE (why this is one-directional): for the MODELED test
the converse fails for elementary reasons before smoothability ever
enters — `Candidate111` omits the (210)/(120)-family pre-tests, the
degree-(100) conditions (a strict relaxation exactly when `r < n`), all
higher multidegrees, ideal extendability, and Borel-fixedness. For the
sources' FULL test the converse fails further because a surviving
candidate need not be a limit of ideals of SMOOTH schemes
(Slip-membership — the cactus gap, CHL §1.3.1). That last gap is why
the sources' verdict is a *search*, not an equation.

DEVIATION (recorded in the CHANGELOG): gains `[Infinite k]`. BB/CHL
prove soundness of the FULL Slip test over algebraically closed fields;
this theorem is about the WEAKER modeled test's polynomial closure and
holds over any infinite field — a strictly weaker hypothesis for a
strictly weaker test: different theorems, neither subsuming the other.
Over finite `k` the closure collapses pointwise
(`Passes111 ⟺ Candidate111`), the pointwise statement
`RankLE → Candidate111` for degenerate decompositions is not
established by the sources, and no claim is made here. -/
theorem passes111_of_borderRankLE
    {k : Type*} [Field k] [Infinite k] {n r : ℕ} (T : Tensor3 k n)
    (h : BorderRankLE T r) : Passes111 T r :=
  MvPolynomial.zeroLocus_anti_mono vanishingIdeal_test111Locus_le h

end Vp2
