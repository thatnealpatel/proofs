# Border Apolarity Algorithm (Conner–Harper–Landsberg, arXiv:1911.07981)

**Paper:** "New lower bounds for matrix multiplication and det3"
**Authors:** Austin Conner, Alicia Harper, J. M. Landsberg
(confirmed from `References/arXiv-1911-07981/BapolarI-11-18.txt`,
lines 1-2 and the address block at the end).
**Sources:**
- `References/arXiv-1911-07981/BapolarI-11-18.txt` — pdftotext of the
  compiled PDF (arXiv v1, dated 11-18 = Nov 18, 2019). All section,
  theorem, and equation numbers below refer to THIS rendering.
- `References/arXiv-1911-07981/BapolarI-11-18.tex` — a LATER revision:
  it inserts a standalone `\section{$\Mtwo$}` (label `mtwopf`) after
  §4, shifting section numbers by +1 from §5 onward, and adds material
  (e.g. Prop. `filterprop`). Where useful I give the revision-stable
  tex `\label` in parentheses; prefer labels over numbers when citing.

Companion theory paper: Buczyńska–Buczyński (BB), arXiv:1910.01944,
cited as [9] in this paper and digested below.
CAVEAT on BB numbering: the BB digest cites "Theorem 4.18 / Lemma 4.17 /
Prop 4.16"; direct recount of the local BB tex gives the border
apolarity iff as compiled **Thm 3.15** (`thm_nonsaturated_apolarity`)
and the Fixed Ideal Theorem as **Thm 4.3** (`thm_G_invariant_bVSP`).
The two numberings come from different revisions (arXiv vs Duke
published version). Always cite BB by `\label`.

## 1. ambient graded ring and where T lives

§2.1 (txt lines 358-361), verbatim:

> "We will be dealing with ideals on products of three projective
> spaces, that is we will be dealing with polynomials that are
> homogeneous in three sets of variables, so our ideals with [sic]
> be Z3-graded. More precisely, we will study ideals
> I ⊂ Sym(A∗)⊗Sym(B∗)⊗Sym(C∗), and Iijk denotes the component in
> S^i A∗ ⊗ S^j B∗ ⊗ S^k C∗."

So the ring is `Sym(A*)⊗Sym(B*)⊗Sym(C*)` — this IS the Cox ring of
P(A) × P(B) × P(C) (the paper never says "Cox ring"; BB do, for
general toric X). Grading: ℤ³ (effectively ℕ³; all graded pieces
with a negative index are 0). A,B,C are complex vector spaces of
dims a,b,c (§2.1).

T ∈ A⊗B⊗C is identified with an element of the dual of the (1,1,1)
graded piece: `S^1A*⊗S^1B*⊗S^1C* = A*⊗B*⊗C*`, so T ⊥ pairs with
degree-(111) elements. The paper never introduces an explicit
apolarity pairing on higher pieces; it only ever uses the perps
listed in item 2 below. (In BB's language T = F ∈ H^0(L)^* with
L = O(1,1,1); CHL work entirely with the low-degree perps.)

Notation (§2.1): T viewed as a linear map T_C : C* → A⊗B with image
T(C*) ⊂ A⊗B, similarly T_A, T_B; T concise iff T_A, T_B, T_C all
injective. Conciseness gives dim T(C*) = c, etc.

## 2. annihilator of T, graded piece by graded piece

The paper does not define a named ideal "Ann(T)"; condition (i) of
§2.3 (txt lines 405-408) is the operative statement, verbatim:

> "(i) I is contained in the annihilator of T. This condition says
> I110 ⊂ T(C∗)⊥, I101 ⊂ T(B∗)⊥, I011 ⊂ T(A∗)⊥ and
> I111 ⊂ T⊥ ⊂ A∗⊗B∗⊗C∗."

As concrete kernels of linear maps built from T:

- degree (1,1,0): `T(C*)^⊥ = ker( A*⊗B* → C ,  α⊗β ↦ T(α,β,·) )`,
  the transpose of the flattening T_C : C* → A⊗B. For concise T
  this kernel has dim ab − c (codim c).
- degree (1,0,1): `T(B*)^⊥ = ker( A*⊗C* → B )`, dim ac − b.
- degree (0,1,1): `T(A*)^⊥ = ker( B*⊗C* → A )`, dim bc − a.
- degree (1,1,1): `T^⊥ = ker( A*⊗B*⊗C* → ℂ, evaluation on T )`,
  codimension 1 (T ≠ 0).
- degrees (1,0,0),(0,1,0),(0,0,1): for concise T the annihilator
  piece is 0 (T_A injective ⟺ no α ∈ A* kills T), and the algorithm
  sets I100 = I010 = I001 = 0 (§3, txt line 613, "by conciseness").
- degrees not ≤ (1,1,1) componentwise (e.g. (2,0,0), (2,1,0)):
  T imposes no annihilation condition — the pairing of such a piece
  against T is identically zero, so the "annihilator" there is the
  whole graded piece. Constraints in those degrees come only from
  the Hilbert-function and ideal-closure conditions. (This sentence
  is my gloss, not paper text; high confidence.)

## 3. the candidate-ideal conditions

§2.3 (txt lines 405-414), the four conditions a multigraded ideal I
coming from a border rank r decomposition of concise T may be
assumed to satisfy:

> "(i) I is contained in the annihilator of T. [as quoted above]
> (ii) For all (ijk) with i + j + k > 1, codim I_ijk = r.
> (iii) I is an ideal, so the multiplication maps
>   (1) I_{i−1,j,k}⊗A* ⊕ I_{i,j−1,k}⊗B* ⊕ I_{i,j,k−1}⊗C*
>         → S^iA*⊗S^jB*⊗S^kC*
>   have image contained in I_ijk."

(eq (1) tex label: `ijkmap` — note the tex reuses this label twice,
lines 585 and 830, a duplicate-label bug in the source.)

and §2.4 (txt line 434):

> "(iv) Each I_ijk is B_T-fixed."

### Hilbert function: exactly r, under a standing smallness assumption

Condition (ii) demands codim EXACTLY r in every multidegree of total
degree ≥ 2 — not min(r, dim). This is CHL's specialization of BB's
generic Hilbert function h_{r,X}(D) = min(r, dim S_D). The bridge is
§2.3 (txt lines 394-397), verbatim:

> "If the r points are in general position, then codim(I_ijk,t) = r
> as long as r ≤ dim S^iA*⊗S^jB*⊗S^kC*. In our situation r will be
> sufficiently small so that this will hold if at least two of
> i, j, k are nonzero, see e.g., [17, 16, 31]. For all (ijk) with
> i + j + k > 1, we may choose the curves such that codim(I_ijk) = r
> by [9, Thm. 1.2]."

Formalization warning: for arbitrary (T, r) the correct condition is
codim I_D = min(r, dim S_D) (BB Thm 1.2, quoted in item 5). CHL's
"= r" silently assumes r ≤ dim S_D for the degrees they test; this
holds in all their applications (e.g. (110): r ≤ ab). A faithful
general formalization should use min, or carry r ≤ dim S_D as a
hypothesis. Note i+j+k > 1 includes (2,0,0): general position of
the r projected points in PA is what makes codim I_200 = r
plausible; this too silently needs r ≤ dim S²A*.

### Borel-fixedness: a WLOG reduction, not intrinsic to soundness

§2.4 (txt lines 419-435): Lie's theorem ("Let H be a solvable group,
W an H-module, [w] ∈ PW. Then the orbit closure H·[w] contains an
H-fixed point"), assume the symmetry group G_T is reductive (or
contains a nontrivial reductive subgroup), B_T ⊂ G_T a Borel
(maximal solvable) subgroup. Verbatim:

> "By Lie's theorem and the Normal Form Lemma of [22], in order to
> prove R(T) > r, it is sufficient to disprove the existence of a
> border rank decomposition where E0 is a B_T-fixed point of
> PΛ^r(A⊗B⊗C). By the same reasoning, as observed in [9], we may
> assume I_ijk is B_T-fixed for all i, j, k."

[22] = Landsberg–Michałek, SIAM J. Appl. Algebra Geom. 1 (2017)
(MR3633766). The mechanism: the set of ideals satisfying (i)-(iii)
is a closed B_T-stable subset (B_T ⊆ G_T fixes [T], hence preserves
each T(·)^⊥ and T^⊥ and the codim-r Grassmannian strata), and Lie's
theorem replaces any point of it by a B_T-fixed point in its orbit
closure. So (iv) is a WLOG strengthening of the necessary condition
(i)-(iii): it is needed for the LOWER-BOUND conclusion "no B_T-fixed
candidate ⟹ R(T) > r" to be valid, and it is what makes the search
space finite/enumerable (weight-vector combinatorics, §2.5); it is
NOT an extra soundness assumption beyond algebraic closedness and
G_T ⊇ reductive. In BB the packaged statement is the addendum to
their Thm 1.2 (verbatim, from BB tex, label
`thm_border_apolarity_intro`): "if G is a group acting on X and
preserving F, then there exists an I as above which in addition is
invariant under a Borel subgroup of G"; the stronger iff version is
BB's Fixed Ideal Theorem (`thm_G_invariant_bVSP`): br(F) ≤ r iff
there is a B-fixed point in bVSP(F,r) ⊂ Slip, for B ⊂ G connected
solvable. CHL cite the Fixed ideal theorem by name in §1.1 and
§1.3.1 (and remark "the Normal form lemma is the (111) case of the
Fixed ideal theorem", §1.1, txt lines 74-75).

Enumeration of B_T-fixed subspaces: §2.5. In multiplicity-free
weight situations they are finitely many (sets of weight vectors
closed under raising); when a weight occurs with multiplicity,
continuous parameters appear (Examples 2.2, 2.3; handled for
M⟨3⟩/det3 by the parametric rank algorithm of §5, txt lines
841-852: recursive pivoting in R/(p) and R_p, lifting ideals J1, J2
and taking J1·J2).

## 4. the (210), (120), (111) tests as finite linear algebra

All from §3 "The algorithm" (tex `algsect`), steps (i)-(iii).
Input: integer r, concise T with G_T ⊇ reductive, Borel B_T.
Initialize I100 = I010 = I001 = 0.

### (210) and (120) tests — algorithm step (i), verbatim (txt 620-630)

> "(i) For each B_T-fixed weight subspace F110 of codimension r − c
> in T(C∗)⊥ ⊂ A∗⊗B∗ (and codimension r in A∗⊗B∗) compute the ranks
> of the multiplication maps
>   (2) F110⊗A∗ → S²A∗⊗B∗, and       [tex label f210]
>   (3) F110⊗B∗ → A∗⊗S²B∗.           [tex label f120]
> If both have images of codimension at least r, then F110 is a
> candidate I110. Call these maps the (210) and (120) maps and the
> rank conditions the (210) and (120) tests."

So: (i) search space = B_T-fixed F110 ⊂ T(C*)^⊥ with
dim F110 = ab − r (codim r − c inside T(C*)^⊥, which has dim ab − c);
(ii) inequality = codim(image) ≥ r in S²A*⊗B*, i.e.
rank(map (2)) ≤ (a+1)a/2·b − r. DIRECTION: the ideal generated in
degree (210) by F110 must be SMALL — elimination happens when rank
is too LARGE (§1.1: "The eliminations are obtained when the ranks of
certain linear maps are too large"); (iii) containment = F110 ⊂
T(C*)^⊥, imposed on the search space itself.

Step (ii) (txt 631-632): "Perform the analogous tests for potential
I101 ⊂ T(B∗)⊥ and I011 ⊂ T(A∗)⊥ to obtain spaces F101, F011." I.e.
for F101 ⊂ A*⊗C* the (201) and (102) maps F101⊗A* → S²A*⊗C* and
F101⊗C* → A*⊗S²C*; for F011 the (021), (012) maps.

### (111) test — algorithm step (iii), verbatim (txt 634-640)

> "(iii) For each triple F110, F101, F011 passing the above tests,
> compute the rank of the map
>   (4) F110⊗C∗ ⊕ F101⊗B∗ ⊕ F011⊗A∗ → A∗⊗B∗⊗C∗.  [tex label 111map]
> If the codimension of the image is at least r, then one has a
> candidate triple. Call this map the (111)-map and the rank
> condition the (111)-test. A space F111 is a candidate for I111 if
> it is of codimension r, contains the image of (4) and it is
> contained in T⊥."

Concretely: (i) searched space = triples of B_T-fixed subspaces
(F110, F101, F011), F110 ⊂ T(C*)^⊥ of dim ab − r, F101 ⊂ T(B*)^⊥ of
dim ac − r, F011 ⊂ T(A*)^⊥ of dim bc − r, each surviving its two
degree-3 tests; (ii) inequality = rank(map (4)) ≤ abc − r, i.e. the
subspace of A*⊗B*⊗C* generated by the three lower pieces has
codimension ≥ r — small enough to extend to a codim-r I111;
(iii) containments: each F ⊂ its T(·)^⊥, and F111 ⊂ T^⊥. Note
(my derivation, not paper text; high confidence): image(4) ⊆ T^⊥ is
AUTOMATIC given the (110)-level containments — for f ∈ T(C*)^⊥,
γ ∈ C*, ⟨f·γ, T⟩ = f(T(γ)) = 0 — so once rank(4) ≤ abc − r holds, a
codim-r subspace F111 with image(4) ⊆ F111 ⊆ T^⊥ always exists
(extend inside the hyperplane T^⊥; r ≥ 1), and a B_T-fixed one
exists because T^⊥/image(4) is a B_T-module and solvable groups in
char 0 admit full flags of submodules (Lie–Kolchin). Hence the
(111) STEP passes iff the rank inequality holds; the choice of F111
only matters for continuing to total degree ≥ 4.

### dual formulation — Proposition 3.1 (txt 674-691)

> "The codimension of the image of the (210)-map is the dimension of
> the kernel of the skew-symmetrization map
>   (6) F110^⊥⊗A → Λ²A⊗B.            [tex label e210map]
> The codimension of the image of the (ijk)-map is the dimension of
>   (7) (F_{ij,k−1}^⊥⊗C) ∩ (F_{i,j−1,k}^⊥⊗B) ∩ (F_{i−1,j,k}^⊥⊗A)."
>                                      [tex label 110inter]

With E_ijk := F_ijk^⊥ (§4, txt 743): E110 ⊂ A⊗B has dim r and
T(C*) ⊆ E110 (perp of F110 ⊂ T(C*)^⊥). So:

- (210) test ⟺ dim ker( E110⊗A → Λ²A⊗B, e⊗a ↦ skew_A(e)⊗... i.e.
  Σ(x⊗y)⊗a ↦ Σ(x∧a)⊗y ) ≥ r. Source dim ra, target dim (a choose 2)b.
- (111) test ⟺ dim( (E110⊗C) ∩ (E101⊗B) ∩ (E011⊗A) ) ≥ r,
  the intersection taken inside A⊗B⊗C (after the obvious
  reshuffles). Note T itself lies in all three (E ⊇ T(·) image),
  so the intersection is never 0 for concise T.

### higher-degree steps (for completeness)

Step (iv) (txt 641-644): degree (200)/(020)/(002): for each B_T-fixed
F200 ⊂ S²A* of codim r, test codim ≥ r for
F110⊗A* ⊕ F200⊗B* → S²A*⊗B* and F101⊗A* ⊕ F200⊗C* → S²A*⊗C*
(the txt's second target "S²A*⊗B*" is a typo for S²A*⊗C*; low
stakes, flagged, unverified against later revisions).
Step (v) (txt 645-656): general (ijk) map, eq (5)
(second tex `ijkmap`): F_{i−1,j,k}⊗A* ⊕ F_{i,j−1,k}⊗B* ⊕
F_{i,j,k−1}⊗C* → S^iA*⊗S^jB*⊗S^kC*; if codim of image = ξ ≥ r, each
codim-r B_T-fixed subspace of the target containing the image
(equivalently (ξ−r)-dim'l B_T-fixed subspace of a complement — the
image is B_T-fixed by Schur's lemma since (5) is a B_T-module map)
is a candidate F_ijk. Step (vi): no candidates at any point ⟹
R(T) > r. Termination (txt 659-660): "the algorithm is finite: it
must stabilize at latest in multi-degree (r, r, r), see [9]."

All results of this paper use only total degree ≤ 3 (txt 666-667):
M⟨3⟩ and det3 use (210),(120),(111); M⟨2nn⟩/M⟨3nn⟩ use only
(210),(120) (§1.3.3, txt 312-315).

### worked sizes (M⟨2⟩, r = 6; §4 "First proof")

Search: B_T-fixed 2-planes E'110 ⊂ U*⊗sl(V)⊗W (E110 =
U*⊗Id_V⊗W ⊕ E'110); exactly three exist (txt 769-772). The paper
reports (210)/(120) skew-map ranks 20, 20, 19 — all > 24 − 6 = 18,
i.e. kernels 4, 4, 5 < 6, so all fail and R(M⟨2⟩) > 6. Bookkeeping
caveat: the printed matrix size there ("24 × 40" in txt line 774;
"40×24" in the tex revision line 931, attached to the map
F110⊗A* → S²A*⊗B*, which is 40×40) is inconsistent as printed; the
operative comparison 20 > 24 − 6 matches the dual skew map (6) with
source E110⊗A of dim 24 (Remark 4.1 confirms: "the resulting matrix
is of size 24×24" and lists 20 independent image vectors). The
printed sizes are numerically unverified; trust eq (6)/Prop 3.1 and
the threshold rank ≤ dim(E110⊗A) − r.

## 5. soundness (border rank ≤ r ⟹ tests pass) and its proof map

CHL state no standalone soundness theorem; soundness is the
concatenation §2.2 → §2.3 → §2.4, with the hard step outsourced to
BB. The chain:

1. **Decomposition as a curve** (§2.2): border rank r decomposition
   T = lim_{t→0} Σ_j T_j(t) ⟼ curve E_t ∈ G(r, A⊗B⊗C), E_t spanned
   by r rank-ones for t ≠ 0, T ∈ E_0.
2. **Curve of ideals + flat limit** (§2.3): I_t := the ℤ³-graded
   ideal of the r points [T_1(t)],…,[T_r(t)]; for points in general
   position codim I_ijk,t = r when r ≤ dim S_ijk (refs [17],[16],[31]
   = Gallet–Ranestad–Villamizar, Galazka, Teitler); define
   I_ijk := lim_{t→0} I_ijk,t **in the Grassmannian**
   G(dim S_ijk − r, S_ijk) — this is where the flat/Grassmannian
   limit enters CHL's own text. The claim that the curves can be
   chosen so codim I_ijk = r for ALL i+j+k > 1 is exactly the BB
   input: "[9, Thm. 1.2]". Caveat recorded by CHL (txt 402-403):
   "there are subtleties here: the limiting ideal may not be
   saturated. See [9] for a discussion."
3. **BB input** — exact citation: Buczyńska–Buczyński,
   "Apolarity, border rank and multigraded Hilbert scheme",
   arXiv:1910.01944, [9]; theorem used = intro **Theorem 1.2 (Weak
   border apolarity)**, tex label `thm_border_apolarity_intro`,
   verbatim from the BB source:

   > "Suppose a tensor or polynomial F has border rank at most r.
   > Then there exists a (multi)homogeneous ideal I ⊂ S[X] such
   > that: I ⊂ Ann(F); for each multidegree D the D-th graded piece
   > I_D of I has codimension (in S[X]_D) equal to
   > min(r, dim S[X]_D). In addition, if G is a group acting on X
   > and preserving F, then there exists an I as above which in
   > addition is invariant under a Borel subgroup of G."

   One direction only — exactly the soundness direction. Inside
   BB's proof (see the BB digest below): the multigraded
   Hilbert scheme Hilb^{h_{r,X}}_S (Haiman–Sturmfels) hosts the
   limit; PROPERNESS/projectivity of Slip_{r,X} (Haiman–Sturmfels
   Cor. 1.2) is what guarantees the limit ideal exists in the same
   component and the span map has closed image
   (`thm_nonsaturated_apolarity`, iff version; `lem_strong_...`).
   The Borel addendum is BB's Fixed Ideal Theorem
   (`thm_G_invariant_bVSP`) + Lie's theorem; CHL also invoke the
   Normal Form Lemma of Landsberg–Michałek [22] as the (111)-case
   precursor.
4. **Tests are necessary conditions** (§3): conditions (i)-(iv)
   restricted to total degree ≤ 3 are precisely the (210), (120),
   (201), (102), (021), (012), (111) tests: (iii) ideal-closure
   forces image(multiplication maps) ⊆ I_ijk, and (ii) forces
   codim I_ijk = r, hence codim(image) ≥ r. So br(T) ≤ r ⟹ some
   B_T-fixed candidate survives every test. Contrapositive = the
   algorithm's certificate.

## 6. ground field

§2.1 opening (txt line 337): "Throughout, A, B, C, U, V, W will
denote complex vector spaces". Everything is over ℂ. Where
algebraic closedness (and char 0) is genuinely used:

- Lie's theorem / Borel fixed-point argument (§2.4) — needs
  algebraically closed; the paper's statement is the char-0
  Lie–Kolchin flavor. This is the load-bearing use: without it no
  B_T-fixed WLOG, no finite enumeration.
- Highest-weight theory of GL_m/SL_m and Schur's lemma
  (§2.5, §6) — char 0, alg. closed.
- BB input: stated over ℂ (BB Sec. 2: "we assume for the sake of
  clarity that the base field k is the field of complex numbers");
  BB's "Other base fields" subsection (`sec_other_base_fields`)
  claims extension to any algebraically closed k modulo (a) lack of
  documented Cox-ring theory over k ≠ ℂ (harmless for smooth
  projective toric X, e.g. Segre) and (b) "very general" arguments
  degenerate over countable fields, fixed via Zariski openness.
- General position of r points / genericity (§2.3) — wants an
  infinite (in BB's stronger statements, uncountable) field.

Nothing in the paper is claimed over non-closed or positive
characteristic fields.

## 7. converse failure: the Slip gap

The tests are necessary, not sufficient, and the paper says so in
two places.

§3 output (txt 661-665): the algorithm ends with "either a
certificate that R(T) > r or a collection of multi-graded ideals
representing all possible candidates for a B_T-fixed border rank
decomposition. In current work with Buczyńska and Buczyński we are
developing tests to determine if a given multi-graded ideal comes
from a border rank decomposition." I.e. a surviving candidate does
NOT certify R(T) ≤ r.

§1.3.1 (txt 287-298) locates the gap precisely: all determinantal/
rank conditions are equations for the r-th CACTUS variety, which
contains σ_r and fills the ambient space by r = 6m − 4 for
ℂ^m⊗ℂ^m⊗ℂ^m; "The r-th secant variety consists of points on limits
of spans of zero dimensional smooth schemes of length r. The r-th
cactus variety consists of points on limits of spans of zero
dimensional schemes of length r. The algorithm produces ideals, and
thus to break the barrier, one needs to distinguish limits of ideals
of smooth schemes from limits of ideals of non-smoothable schemes."

In BB language: the tests check membership of a candidate in the
multigraded Hilbert scheme Hilb^{h_{r,X}} with I ⊆ Ann(T); border
rank ≤ r additionally requires I ∈ Slip_{r,X} (the closure of ideals
of r DISTINCT points — one irreducible component of the Hilbert
scheme). The iff (BB `thm_nonsaturated_apolarity`) trades exactly on
Slip membership, which is not a rank condition and is not checked by
this paper's algorithm. Smoothability of the limiting scheme is the
geometric content of that membership.

## 8. formalization notes: the (111) step as pure linear algebra

Minimal statement to formalize (soundness only, symmetry-free core;
field k alg. closed char 0, in practice ℂ):

Let T ∈ A⊗B⊗C be concise, a,b,c = dims, r ∈ ℕ with
max(a,b,c) ≤ r ≤ min(ab, ac, bc)   [the upper bound is CHL's
standing smallness assumption making "codim = r" the right Hilbert
function; drop it by switching to min(r, dim) à la BB Thm 1.2].

**(111) criterion, primal form.** If R(T) ≤ r then there exist
subspaces
  F110 ⊆ ker(T_AB : A*⊗B* → C), dim F110 = ab − r,
  F101 ⊆ ker(T_AC : A*⊗C* → B), dim F101 = ac − r,
  F011 ⊆ ker(T_BC : B*⊗C* → A), dim F011 = bc − r,
such that
  dim( F110·C* + F101·B* + F011·A* ) ≤ abc − r
inside A*⊗B*⊗C*, where F110·C* denotes the image of the bilinear
multiplication F110 × C* → A*⊗B*⊗C*, (f, γ) ↦ f⊗γ (suitably
reshuffled), etc. (This is rank(map (4)) ≤ abc − r; the extension to
a codim-r F111 ⊆ T^⊥ containing the sum is then automatic, see §4
notes above.)

**Dual form (recommended for Lean: small dimensions).** Equivalent
via E := F^⊥ (Prop 3.1, eq (7)): there exist
  E110 ⊆ A⊗B, dim r, T(C*) ⊆ E110,
  E101 ⊆ A⊗C, dim r, T(B*) ⊆ E101,
  E011 ⊆ B⊗C, dim r, T(A*) ⊆ E011,
with
  dim( (E110⊗C) ∩ (E101⊗B) ∩ (E011⊗A) ) ≥ r,
the intersection inside A⊗B⊗C under the canonical reshuffles.
(T itself always lies in the triple intersection.) The full
degree-≤3 test adds, for each pair, the skew conditions
  dim ker( E110⊗A → Λ²A⊗B ) ≥ r  and
  dim ker( E110⊗B → A⊗Λ²B ) ≥ r   [(210),(120)],
and their (201),(102),(021),(012) analogues — each equivalent to
"codim of the multiplication image ≥ r" by the transpose argument
in the proof of Prop 3.1.

With symmetry (the paper's actual test): additionally G_T contains
a reductive subgroup with Borel B_T, and the E's may be taken
B_T-fixed (equivalently: quantify only over B_T-fixed triples).
Soundness of that restriction = BB Thm 1.2 addendum / Fixed Ideal
Theorem + Lie's theorem, NOT elementary linear algebra — for a Lean
development, the symmetry-free statement above is the natural first
target, with Borel-fixedness layered on as a separate reduction.

What the criterion is NOT: passing gives no upper bound on R(T)
(item 7); and the exactly-r Hilbert function must become
min(r, dim) outside the smallness regime.

Downstream machinery (matmult-specific, for later): Prop 6.1
(tex `210kerprop`, eqs (13) `210map`, (14)) — Schur-lemma reduction
of the (210) kernel for M⟨u,v,w⟩; §7 outer/inner structures on
U*⊗sl(V)⊗W, local bounds Lemma 7.1 (`absl2`, v=2), Lemma 7.3
(`absl3`, v=3), globalization Lemma 7.6 (`alem2`) via partition
combinatorics Lemma 7.8 (`lemma:singlebound`) and convex
optimization Lemma 7.9 (`lemma:opt`). Results: Thms 1.1
(`mthreethm`), 1.2 (`detthreethm`), 1.3 (`223thm`), 1.4 (`2nnbnds`),
1.5 (`mnnthm`), Cor 1.6 (`3nncor`); Lickteig-style peeling §8
(tex `Lickappen`).


---

# Border Apolarity (Buczyńska–Buczyński, arXiv:1910.01944)

**Paper:** "Apolarity, border rank and multigraded Hilbert scheme"
**Source:** `References/arXiv-1910-01944/apolarity-for-border-rank.tex`

## Field assumptions

The paper works over **k = CC** (stated in Section 3, line 427–429).
Subsection 9.1 ("Other base fields") claims results extend to any
**algebraically closed** field k; no explicit characteristic restriction
for smooth projective toric varieties (class group torsion issues only
arise for non-smooth cases). Full details deferred to future work.

## Hilbert function h_{r,X}

Definition (Section 4.4, before Lemma 4.14):

    h_{r,X}(D) := min(r, dim H^0(X, O_X(D)))   for D in Pic(X).

For X = P^a x P^b x P^c (Segre case with Pic = ZZ^3):

    h_{r,X}(i,j,k) = min(r, C(a+i,a) * C(b+j,b) * C(c+k,c))

Example: X = P^1 x P^1 x P^1 (a=b=c=1, so tensors in C^2 x C^2 x C^2):
  - h_r(1,1,0) = min(r, 2*2*1) = min(r, 4)
  - h_r(1,0,1) = min(r, 2*1*2) = min(r, 4)
  - h_r(0,1,1) = min(r, 1*2*2) = min(r, 4)
  - h_r(1,1,1) = min(r, 2*2*2) = min(r, 8)

## Slip_{r,X} — Scheme of Limits of Ideals of Points

**Definition** (Notation block after Proposition 4.16):

- **Sip_{r,X}** := the set of saturated ideals of r distinct points
  in X having generic Hilbert function h_{r,X}. These are called "ips".

- **Slip_{r,X}** := closure of Sip_{r,X} inside the (reduced)
  multigraded Hilbert scheme Hilb^{h_{r,X}}_S.

Proposition 4.16 proves Sip_{r,X} lies in a **unique** irreducible
component of Hilb^{h_{r,X}}_S, and is dense in that component.
So Slip_{r,X} IS that irreducible component. Elements are "lips".

## Border Apolarity Theorem

**Theorem 4.18** (label: thm_nonsaturated_apolarity):

> Let X be a smooth toric projective variety embedded in P(H^0(L)*).
> Let F in S_L (a homogeneous element of degree L in the Cox ring dual).
> Then:
>
>     br_X(F) <= r   <==>   exists I in Slip_{r,X} such that I ⊆ Ann(F).

## Proof mechanism

The iff is proved via **Lemma 4.17** (label: lem_strong_nonsaturated_apolarity):

**(=>)** ("necessary" direction, border rank <= r implies lip exists):
1. Slip_{r,X} is **projective** by Haiman–Sturmfels [Cor. 1.2].
2. Define rho: Slip_{r,X} -> Gr (Grassmannian) sending I to (I_L)^perp.
3. The universal subbundle pullback U -> P(H^0(L)*) has **closed** image
   (because U is projective, being a closed subvariety of a product of
   projective varieties).
4. For very general lips (= r distinct points), the image is the union
   of linear spans = dense in sigma_r(X). Closed + dense = full.
5. So F in sigma_r(X) implies (I, [F]) in U for some lip I, giving
   I_L ⊆ (Ann F)_L, and Proposition 4.12 lifts this to I ⊆ Ann(F).

**(<=)** ("sufficient" direction): Pick a sequence I^k in Sip_{r,X}
converging to I (density of Sip in Slip). Then rho(I^k) -> rho(I),
and [F] in rho(I) = lim <p_1^k,...,p_r^k>, so F is a limit of
rank-<= r points.

**Key references for the necessary direction:**
- Projectivity of multigraded Hilbert scheme: Haiman–Sturmfels Cor. 1.2
- Density of Sip in Slip: Proposition 4.16
- Degree-L containment suffices: Proposition 4.12
