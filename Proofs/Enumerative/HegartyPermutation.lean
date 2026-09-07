import Mathlib

/-!
# OEIS A094870: Hegarty's greedy AP-avoiding permutation of the positive integers

**Status.** Archive file.  Everything is proved except one intended `sorry`, which carries
Hegarty's Conjecture 3.2 (the OEIS "Conjecture: lim_{n->infinity} a(n)/n = 1").

## Primary sources, pinned verbatim

### OEIS A094870, from `goof oeis show A094870` (re-pulled 2026-08-05)

*Name*:

> a(1)=1; for n > 1, a(n) is the minimal positive integer t not equal to a(1), ..., a(n-1)
> such that t - a(n-i) is not equal to a(n-i) - a(n-2i) for all 1 <= i < n/2.

*Comments* (all four, verbatim and in order):

> 3n/8 <= a(n) < 3n/2 (P. Hegarty).
>
> Conjecture: lim_{n->infinity} a(n)/n = 1 (P. Hegarty).
>
> The Hegarty paper shows that this is a permutation. - _Franklin T. Adams-Watters_,
> May 26 2014
>
> Graphically, the sequence {a(n)-n} resembles A293862 (see illustration in Links
> section). - _Rémy Sigrist_, Feb 06 2020

*Terms*:

> 1,2,4,3,5,6,8,7,10,9,13,12,14,11,17,16,22,15,23,18,21,20,25,24,26,19,28,27,29,36,32,31,
> 33,39,38,34,41,30,37,35,44,48,42,40,43,50,46,52,47,45,54,49,56,58,57,51,61,53,59,63,60,
> 68,64,62,70,55,65,67,73,69,83,76

*Example* (`%e`, from the raw OEIS text record):

> a(3)=4 because it can't be 1=a(1), 2=a(2) and 3=2*a(3-1)-a(3-2).

*Offset* (`%O`) is `1,2`; *keywords* (`%K`) are `easy,nonn`; the *link* (`%H`) naming
"the Hegarty paper" is

> Peter Hegarty, Permutations avoiding arithmetic patterns, The Electronic Journal of
> Combinatorics, 11 (2004), #R39.   [https://doi.org/10.37236/1792]

### Hegarty's paper, fetched to `References/doi-10-37236-1792/paper.txt`

The greedy algorithm (Section 3, p. 5), verbatim:

> (i) π(1) := 1,
> (ii) suppose π(1), ..., π(n − 1) have been chosen. Then choose π(n) to be the least
> positive integer t which has not already been chosen and such that, for each positive
> integer i < n/2,
>     t − π(n − i) ≠ π(n − i) − π(n − 2i).
>
> The first few terms in the sequence (π(n))n>0 are
> 1, 2, 4, 3, 5, 6, 8, 7, 10, 9, 13, ...

Theorem 3.1 and the bound proved inside its proof, verbatim:

> Theorem 3.1  The map π is surjective.
>
> Proof : First we prove that, for each n > 0,
>     π(n) < 3n/2.                                                                    (1)

Equation (4), Conjecture 3.2 and Theorem 3.3, verbatim (the pdftotext conversion
column-scrambles the two displayed fractions; the token sequences are transcribed here
in the order they appear in `paper.txt`, and the intended reading — confirmed by the
surrounding prose and by the OEIS comment — is given after each):

> The permutation of N just described will be denoted πg (g for ‘greedy'). The last proof
> implies that, for all n > 0,
> πg (n)
> 3
> 1
> ≤
> < .
> (4)
> 4
>
> n
>
> 2

i.e. `1/4 ≤ πg(n)/n < 3/2`.

> Conjecture 3.2
>
> πg (n)
> = 1.
> n→∞
> n
> lim
>
> We have no idea how one might prove this - our only real evidence is numerical.

i.e. `lim_{n→∞} πg(n)/n = 1`.

> The best improvement on (4) which we have managed is
> Theorem 3.3
>
> For all n > 0 we have
> πg (n)
> 3
> ≥ .
> n
> 8

i.e. `πg(n)/n ≥ 3/8`.

### Transcription note

`References/doi-10-37236-1792/paper.txt` is a `pdftotext` rendering of the published PDF,
and the quotations above repair — and only repair — the following mechanical conversion
damage.  Every mathematical token is otherwise as in `paper.txt`.

* `pdftotext` emits the `≠` glyph as the two characters `6=`; the greedy-algorithm display
  reads `t − π(n − i) 6= π(n − i) − π(n − 2i).` in `paper.txt` and is quoted above with
  `≠` restored.
* `pdftotext` maps the `fi`/`ff`/`ffi` ligatures to the control bytes `0x1C`/`0x1B`/`0x1E`
  (107 occurrences in all): `paper.txt` has `<0x1C>rst` for "first" (as in "The first few
  terms"), `de<0x1C>nition`, `<0x1C>nite`, `di<0x1B>erent`, `su<0x1E>cient`.  Restored.
* Long source lines are rewrapped, and the page-footer line "the electronic journal of
  combinatorics 11 (2004), #R39" plus the bare page number are dropped where they interrupt
  a display; in `paper.txt` the footer separates `π(n) < 3n/2.` from its equation tag `(1)`.
* The three displayed fractions — (4), Conjecture 3.2 and Theorem 3.3 — are column-scrambled
  by the conversion; those three are quoted **unrepaired**, exactly in `paper.txt` token
  order, with the intended reading stated separately after each.

## What the sources say, and what this file does

The two OEIS comments "3n/8 <= a(n) < 3n/2 (P. Hegarty)" and "Conjecture:
lim_{n->infinity} a(n)/n = 1 (P. Hegarty)" are formatted identically, but the paper
distinguishes them sharply:

* `a(n) < 3n/2` is **proved** — it is display (1), established in the first paragraph of
  the proof of Theorem 3.1 by a counting argument.  Formalized here as `two_mul_a_lt`.
* `3n/8 ≤ a(n)` is **proved** — it is Theorem 3.3, formalized in the companion
  module `Enumerative.HegartyThreeEighths`.
* `lim a(n)/n = 1` is **Conjecture 3.2**, explicitly open ("We have no idea how one might
  prove this").  This is the file's single intended `sorry` (`conj_3_2`).
* "The Hegarty paper shows that this is a permutation" is Theorem 3.1 (surjectivity;
  injectivity is immediate from the greedy rule).  Formalized here as `a_bijOn`.

**Separation of concerns.**  This file proves the weaker lower bound that Hegarty records
as the left half of his display (4), `n/4 ≤ πg(n)`, which falls out of the surjectivity
proof for free (`lt_four_mul_a`).  The companion module `Enumerative.HegartyThreeEighths`
formalizes the paper's full three-page parity/counting proof of Theorem 3.3 rather than
archiving that published theorem as a second `sorry` here.

## Indexing

Everything here is **0-indexed**: `a n = A094870(n+1) = πg(n+1)`.  So the OEIS/Hegarty
bounds `N/4 ≤ a(N) < 3N/2` read, with `N = n + 1` and cleared denominators,

* `n < 4 * a n`      (`lt_four_mul_a`), equivalently `N ≤ 4·a(N)`;
* `2 * a n < 3 * (n + 1)`  (`two_mul_a_lt`), equivalently `2·a(N) < 3·N`;

and Conjecture 3.2 reads `a n / (n + 1) → 1`.  `hegarty_bounds` restates both bounds over
`ℝ` in the OEIS shape.  The denominator `(n : ℝ) + 1` is never `0`, so no division guard is
needed.

## Structure

`IsCandList v t` is the OEIS admissibility test for a candidate value `t` against the
*reversed* prefix `v = [a(n-1), …, a 0]`; `nextTerm v` is the least admissible `t`
(`Nat.find`, total because `2·max v + 1` is always admissible); `pre n` is the reversed
prefix and `a n = nextTerm (pre n)`.  `isCandList_pre_iff` translates the list-level test
into the index-level predicate `IsCand n t`, after which nothing mentions lists.

The seed `a(1) = 1` is *derived*, not assumed: at `n = 0` both clauses of `IsCand` are
vacuous, so the least admissible value is `1` (`a_zero`).

Hegarty's proofs are followed literally:

* `two_mul_a_lt` — every `m` with `1 ≤ m < a n` is either an earlier term (`n` of them) or
  is `2·a(n-i) - a(n-2i)` for one of the `⌊n/2⌋` admissible `i`; hence `a n - 1 ≤ n + n/2`.
* `thm_3_1` — if `v` never occurs before position `4v`, then at each of the `≥ 3v+1`
  positions `m < 4v` carrying a value `> v` the greedy rule rejected `v`, exhibiting
  `blockIdx v m` with `v + a(m - 2s) = 2·a(m - s)`.  The map `m ↦ a(m - 2s)` is injective
  (the value determines `a(m-s)`, hence `m-s` and `m-2s`, hence `s` and `m`) and lands in
  the `3v` positive integers `≤ 6v` of the parity of `v` — the `≤ 6v` coming from
  `two_mul_a_lt`.  `3v + 1 ≤ 3v` is the contradiction.

No `native_decide`, no `axiom`, no `@[implemented_by]`/`@[extern]`/`@[csimp]`.  The ground
check `a_ground` against the OEIS `terms` field is kernel-checked by `decide`.
-/

set_option autoImplicit false

namespace A094870

/-! ## The greedy rule on reversed prefixes -/

/-- The OEIS admissibility test for a candidate value `t` against the **reversed** prefix
`v = [a(n-1), a(n-2), …, a 0]`: `t` is positive, `t` is none of the earlier terms, and for
every `j` with `2j + 2 ≤ n` — i.e. every `i = j + 1` with `1 ≤ i` and `2i ≤ n`, which is the
OEIS range `1 <= i < N/2` at OEIS index `N = n + 1` (there `i < N/2 ⟺ 2i < N ⟺ 2i ≤ n`) —
the triple `(a(n-2i), a(n-i), t) = (v[2j+1], v[j], t)` is not an arithmetic progression.

The outer bound `j < v.length` is redundant (`2j + 2 ≤ v.length` already forces it) and is
present only to make the quantifier decidable; `isCandList_pre_iff` proves the equivalence
with the *unbounded* `IsCand`, which is what pins down that no case is lost. -/
def IsCandList (v : List ℕ) (t : ℕ) : Prop :=
  1 ≤ t ∧ t ∉ v ∧ ∀ j < v.length, 2 * j + 2 ≤ v.length →
    t + v.getD (2 * j + 1) 0 ≠ 2 * v.getD j 0

/-- Decidability of `IsCandList` by structural unfolding. -/
instance instDecidableIsCandList (v : List ℕ) (t : ℕ) : Decidable (IsCandList v t) := by
  unfold IsCandList
  infer_instance

/-- The largest entry of a list of naturals (`0` on the empty list). -/
def listMax (v : List ℕ) : ℕ := v.foldr max 0

/-- Ground check for `listMax`. -/
example : listMax [3, 7, 2] = 7 := rfl

/-- Ground check for `listMax` at the boundary input. -/
example : listMax [] = 0 := rfl

/-- Defining equation of `listMax`. -/
theorem listMax_cons (b : ℕ) (w : List ℕ) : listMax (b :: w) = max b (listMax w) := rfl

/-- Every entry of a list is at most its `listMax`. -/
theorem le_listMax : ∀ {v : List ℕ} {x : ℕ}, x ∈ v → x ≤ listMax v := by
  intro v
  induction v with
  | nil => intro x hx; exact absurd hx List.not_mem_nil
  | cons b w ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · rw [listMax_cons]; exact le_max_left _ _
    · rw [listMax_cons]; exact (ih hx').trans (le_max_right _ _)

/-- `listMax` also bounds out-of-range lookups, which default to `0`. -/
theorem getD_le_listMax (v : List ℕ) (k : ℕ) : v.getD k 0 ≤ listMax v := by
  by_cases hk : k < v.length
  · rw [List.getD_eq_getElem _ _ hk]
    exact le_listMax (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

/-- **The greedy step never gets stuck**: `2 · listMax v + 1` is always admissible, since it
exceeds every entry of `v` and every value `2·v[j] - v[2j+1]` an arithmetic progression
could demand. -/
theorem exists_isCandList (v : List ℕ) : ∃ t, IsCandList v t := by
  refine ⟨2 * listMax v + 1, by omega, ?_, ?_⟩
  · intro hmem
    have h := le_listMax hmem
    omega
  · intro j _ _
    have h1 := getD_le_listMax v (2 * j + 1)
    have h2 := getD_le_listMax v j
    omega

/-- The least admissible continuation of the reversed prefix `v`. -/
def nextTerm (v : List ℕ) : ℕ := Nat.find (exists_isCandList v)

/-- Characterization of `nextTerm` by admissibility plus minimality. -/
theorem nextTerm_eq {v : List ℕ} {t : ℕ} (ht : IsCandList v t)
    (hmin : ∀ k < t, ¬ IsCandList v k) : nextTerm v = t :=
  (Nat.find_eq_iff _).mpr ⟨ht, hmin⟩

/-- The reversed prefix `pre n = [a(n-1), a(n-2), …, a 0]`. -/
def pre : ℕ → List ℕ
  | 0 => []
  | n + 1 => nextTerm (pre n) :: pre n

/-- **OEIS A094870**, 0-indexed: `a n = A094870(n+1)`.  `a n` is the least positive integer
different from `a 0, …, a (n-1)` such that no triple `(a(n-2i), a(n-i), a n)` with `1 ≤ i`
and `2i ≤ n` is an arithmetic progression.  Equivalently (Hegarty, Section 3) it is the
greedy AP-avoiding permutation `πg` of the positive integers, `a n = πg(n+1)`. -/
def a (n : ℕ) : ℕ := nextTerm (pre n)

/-- The reversed prefix grows by one term at the front. -/
theorem pre_succ (n : ℕ) : pre (n + 1) = a n :: pre n := rfl

/-- The reversed prefix at `0` is empty. -/
theorem pre_zero : pre 0 = ([] : List ℕ) := rfl

/-! ## Translating the list-level rule into an index-level rule -/

/-- `pre n` records exactly the first `n` terms. -/
theorem pre_length (n : ℕ) : (pre n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pre_succ, List.length_cons, ih]

/-- The reversed prefix reads the sequence backwards. -/
theorem pre_getD : ∀ n k : ℕ, k < n → (pre n).getD k 0 = a (n - 1 - k) := by
  intro n
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk
    match k with
    | 0 =>
      rw [pre_succ, List.getD_cons_zero]
      exact congrArg a (by omega)
    | j + 1 =>
      rw [pre_succ, List.getD_cons_succ, ih j (by omega)]
      congr 1
      omega

/-- Membership in the reversed prefix is membership among the first `n` terms. -/
theorem mem_pre_iff : ∀ n t : ℕ, t ∈ pre n ↔ ∃ m, m < n ∧ a m = t := by
  intro n
  induction n with
  | zero =>
    intro t
    constructor
    · intro h; exact absurd h List.not_mem_nil
    · rintro ⟨m, hm, -⟩; omega
  | succ n ih =>
    intro t
    rw [pre_succ, List.mem_cons, ih t]
    constructor
    · rintro (rfl | ⟨m, hm, rfl⟩)
      · exact ⟨n, by omega, rfl⟩
      · exact ⟨m, by omega, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      rcases Nat.lt_or_ge m n with h | h
      · exact Or.inr ⟨m, h, rfl⟩
      · have hmn : m = n := by omega
        subst hmn
        exact Or.inl rfl

/-- **The OEIS rule, index-level**: `t` is an admissible value at position `n` when `t` is
positive, differs from every earlier term, and completes no arithmetic progression
`(a(n-2i), a(n-i), t)` with `1 ≤ i` and `2i ≤ n`.  The index range `1 ≤ i ∧ 2i ≤ n` is the
OEIS `1 <= i < N/2` read at OEIS index `N = n + 1`: `i < N/2 ⟺ 2i < N ⟺ 2i ≤ n`, which is
exactly the range in which `n - 2i` is still a legitimate position. -/
def IsCand (n t : ℕ) : Prop :=
  1 ≤ t ∧ (∀ m < n, a m ≠ t) ∧
    ∀ i, 1 ≤ i → 2 * i ≤ n → t + a (n - 2 * i) ≠ 2 * a (n - i)

/-- The list-level and index-level rules agree. -/
theorem isCandList_pre_iff {n t : ℕ} : IsCandList (pre n) t ↔ IsCand n t := by
  have hlen : (pre n).length = n := pre_length n
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · intro m hm heq
      exact h2 ((mem_pre_iff n t).mpr ⟨m, hm, heq⟩)
    · intro i hi hin
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hkey := h3 j (by omega) (by omega)
      rw [pre_getD n (2 * j + 1) (by omega), pre_getD n j (by omega)] at hkey
      have e1 : n - 2 * (j + 1) = n - 1 - (2 * j + 1) := by omega
      have e2 : n - (j + 1) = n - 1 - j := by omega
      rw [e1, e2]
      exact hkey
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · intro hmem
      obtain ⟨m, hm, heq⟩ := (mem_pre_iff n t).mp hmem
      exact h2 m hm heq
    · intro j hj hj2
      rw [pre_getD n (2 * j + 1) (by omega), pre_getD n j (by omega)]
      have e1 : n - 1 - (2 * j + 1) = n - 2 * (j + 1) := by omega
      have e2 : n - 1 - j = n - (j + 1) := by omega
      rw [e1, e2]
      exact h3 (j + 1) (by omega) (by omega)

/-- The term at position `n` is admissible there. -/
theorem isCand_a (n : ℕ) : IsCand n (a n) :=
  isCandList_pre_iff.mp (Nat.find_spec (exists_isCandList (pre n)))

/-- The term at position `n` is at most any admissible value. -/
theorem a_le_of_isCand {n t : ℕ} (h : IsCand n t) : a n ≤ t :=
  Nat.find_min' _ (isCandList_pre_iff.mpr h)

/-- **Greediness, packaged**: `a n` is the least admissible value at position `n`. -/
theorem isLeast_a (n : ℕ) : IsLeast {t | IsCand n t} (a n) :=
  ⟨isCand_a n, fun _ h => a_le_of_isCand h⟩

/-- Anything below `a n` was rejected at position `n`. -/
theorem not_isCand_of_lt {n t : ℕ} (h : t < a n) : ¬ IsCand n t := by
  intro hc
  have := a_le_of_isCand hc
  omega

/-! ## Immediate consequences -/

/-- Every term is a positive integer. -/
theorem one_le_a (n : ℕ) : 1 ≤ a n := (isCand_a n).1

/-- **The seed is derived, not assumed**: at `n = 0` both clauses of `IsCand` are vacuous,
so the least admissible value is `1`.  This is the OEIS stipulation `a(1) = 1`. -/
theorem a_zero : a 0 = 1 := by
  refine le_antisymm (a_le_of_isCand ⟨le_refl 1, ?_, ?_⟩) (one_le_a 0)
  · intro m hm; omega
  · intro i hi hin; omega

/-- Distinct positions carry distinct terms. -/
theorem a_ne_of_lt {m n : ℕ} (h : m < n) : a m ≠ a n := (isCand_a n).2.1 m h

/-- **Injectivity**: the greedy rule never reuses a value. -/
theorem a_injective : Function.Injective a := by
  intro m n h
  rcases lt_trichotomy m n with hlt | heq | hgt
  · exact absurd h (a_ne_of_lt hlt)
  · exact heq
  · exact absurd h.symm (a_ne_of_lt hgt)

/-! ## AP-avoidance (Hegarty, Definition 2.1 with `k = 3`) -/

/-- **The defining property**: `a` avoids arithmetic progressions in Hegarty's sense — there
is no triple of positions `(x, y, z)`, not all equal, with `x + z = 2y` (the positions in
AP) and `a x + a z = 2 * a y` (the values in AP).  Under `x + z = 2y` the triple is "not all
equal" exactly when `x ≠ z`, which is the hypothesis used here. -/
theorem a_avoidsAP {x y z : ℕ} (hxz : x ≠ z) (hAP : x + z = 2 * y) :
    a x + a z ≠ 2 * a y := by
  rcases Nat.lt_or_ge x z with hlt | hge
  · have hkey := (isCand_a z).2.2 (z - y) (by omega) (by omega)
    have e1 : z - 2 * (z - y) = x := by omega
    have e2 : z - (z - y) = y := by omega
    rw [e1, e2] at hkey
    omega
  · have hkey := (isCand_a x).2.2 (x - y) (by omega) (by omega)
    have e1 : x - 2 * (x - y) = z := by omega
    have e2 : x - (x - y) = y := by omega
    rw [e1, e2] at hkey
    omega

/-- **The distinctness hypothesis of `a_avoidsAP` is load-bearing**: dropping `x ≠ z` makes
the statement false, since `x = y = z` is a degenerate AP in both positions and values. -/
theorem not_a_avoidsAP_without_ne :
    ¬ ∀ x y z : ℕ, x + z = 2 * y → a x + a z ≠ 2 * a y := by
  intro h
  exact h 0 0 0 (by omega) (by omega)

/-! ## Hegarty display (1): `a(N) < 3N/2` -/

/-- **Hegarty, display (1)** (0-indexed): `2 * a n < 3 * (n + 1)`, i.e. `a(N) < 3N/2` at
OEIS index `N = n + 1`.  Every `m` with `1 ≤ m < a n` was rejected at position `n`, so it is
either one of the `n` earlier terms or the value `2·a(n-i) - a(n-2i)` forced by one of the
`⌊n/2⌋` admissible indices `i`; hence `a n - 1 ≤ n + ⌊n/2⌋`. -/
theorem two_mul_a_lt (n : ℕ) : 2 * a n < 3 * (n + 1) := by
  have hsub : Finset.Ico 1 (a n) ⊆
      (Finset.range n).image a ∪
        (Finset.Icc 1 (n / 2)).image (fun i => 2 * a (n - i) - a (n - 2 * i)) := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    obtain ⟨hm1, hm2⟩ := hm
    by_cases hprev : ∃ k, k < n ∧ a k = m
    · obtain ⟨k, hk, hak⟩ := hprev
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, hak⟩)
    · have hprev' : ∀ k < n, a k ≠ m := fun k hk hak => hprev ⟨k, hk, hak⟩
      have hnc : ¬ IsCand n m := not_isCand_of_lt hm2
      have hfail : ∃ i, 1 ≤ i ∧ 2 * i ≤ n ∧ m + a (n - 2 * i) = 2 * a (n - i) := by
        by_contra hno
        exact hnc ⟨hm1, hprev', fun i hi hin heq => hno ⟨i, hi, hin, heq⟩⟩
      obtain ⟨i, hi1, hi2, hieq⟩ := hfail
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, ?_, ?_⟩)
      · rw [Finset.mem_Icc]; omega
      · omega
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hc
  have h1 : ((Finset.range n).image a).card ≤ n :=
    le_trans Finset.card_image_le (le_of_eq (Finset.card_range n))
  have h2 : ((Finset.Icc 1 (n / 2)).image
      (fun i => 2 * a (n - i) - a (n - 2 * i))).card ≤ n / 2 := by
    refine le_trans Finset.card_image_le (le_of_eq ?_)
    rw [Nat.card_Icc]
    omega
  have h3 := Finset.card_union_le ((Finset.range n).image a)
    ((Finset.Icc 1 (n / 2)).image (fun i => 2 * a (n - i) - a (n - 2 * i)))
  have h4 := one_le_a n
  omega

/-- Paper alias for `two_mul_a_lt`: display (1) inside the proof of Hegarty's Theorem 3.1. -/
theorem hegarty_eq_1 (n : ℕ) : 2 * a n < 3 * (n + 1) := two_mul_a_lt n

/-! ## Hegarty Theorem 3.1: surjectivity -/

/-- The blocking index witnessing that value `v` was rejected at position `m`: the least `i`
with `1 ≤ i`, `2i ≤ m` and `v + a(m - 2i) = 2·a(m - i)`.  Junk value `0` when no such `i`
exists; every use below is guarded by a nonemptiness proof. -/
noncomputable def blockIdx (v m : ℕ) : ℕ :=
  sInf {i | 1 ≤ i ∧ 2 * i ≤ m ∧ v + a (m - 2 * i) = 2 * a (m - i)}

/-- **Hegarty, Theorem 3.1** (0-indexed): every positive integer `v` already occurs among
the first `4v` terms.  Suppose not.  Of the `4v` positions `m < 4v`, at most `v - 1` carry a
value `≤ v`, so at least `3v + 1` carry a value `> v`; at each of those the greedy rule
rejected `v`, producing `s = blockIdx v m` with `v + a(m - 2s) = 2·a(m - s)`.  The value
`w = a(m - 2s)` determines `a(m - s) = (v + w)/2`, hence — by injectivity — both `m - s` and
`m - 2s`, hence `s` and `m`; so `m ↦ w` is injective.  Each such `w` is positive, has the
parity of `v`, and satisfies `w < 6v` by `two_mul_a_lt`, and there are only `3v` such
integers.  `3v + 1 ≤ 3v` is the contradiction. -/
theorem thm_3_1 {v : ℕ} (hv : 1 ≤ v) : ∃ n, n < 4 * v ∧ a n = v := by
  by_contra hcontra
  have hcon : ∀ n, n < 4 * v → a n ≠ v := fun n hn hav => hcontra ⟨n, hn, hav⟩
  set R : Finset ℕ := Finset.range (4 * v) with hRdef
  set X0 : Finset ℕ := R.filter (fun m => v < a m) with hX0def
  have hmemX0 : ∀ m ∈ X0, m < 4 * v ∧ v < a m := by
    intro m hm
    rw [hX0def, Finset.mem_filter, hRdef, Finset.mem_range] at hm
    exact hm
  -- (a) at every position of `X0` the greedy rule rejected `v`, so `blockIdx` is genuine.
  have hblock : ∀ m ∈ X0, 1 ≤ blockIdx v m ∧ 2 * blockIdx v m ≤ m ∧
      v + a (m - 2 * blockIdx v m) = 2 * a (m - blockIdx v m) := by
    intro m hm
    obtain ⟨hmR, hmv⟩ := hmemX0 m hm
    have hnc : ¬ IsCand m v := not_isCand_of_lt hmv
    have hne : ∀ k < m, a k ≠ v := fun k hk => hcon k (by omega)
    have hex : Set.Nonempty {i | 1 ≤ i ∧ 2 * i ≤ m ∧ v + a (m - 2 * i) = 2 * a (m - i)} := by
      by_contra hno
      rw [Set.not_nonempty_iff_eq_empty] at hno
      refine hnc ⟨hv, hne, ?_⟩
      intro i hi him heq
      have hmem : i ∈ {i | 1 ≤ i ∧ 2 * i ≤ m ∧ v + a (m - 2 * i) = 2 * a (m - i)} :=
        ⟨hi, him, heq⟩
      rw [hno] at hmem
      exact hmem
    exact Nat.sInf_mem hex
  -- (b) the blocked value is `< 6v`, by display (1).
  have hsmall : ∀ m ∈ X0, a (m - 2 * blockIdx v m) < 6 * v := by
    intro m hm
    obtain ⟨hmR, -⟩ := hmemX0 m hm
    have h := two_mul_a_lt (m - 2 * blockIdx v m)
    omega
  -- (c) `m ↦ (a(m - 2s) - 1)/2` maps `X0` into `range (3v)` …
  have hmaps : Set.MapsTo (fun m => (a (m - 2 * blockIdx v m) - 1) / 2) ↑X0
      ↑(Finset.range (3 * v)) := by
    intro m hm
    have hmX : m ∈ X0 := hm
    have h1 := one_le_a (m - 2 * blockIdx v m)
    have h2 := hsmall m hmX
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  -- (d) … injectively.
  have hinj : Set.InjOn (fun m => (a (m - 2 * blockIdx v m) - 1) / 2) ↑X0 := by
    intro m hm m' hm' heq
    obtain ⟨hs1, hs2, hs3⟩ := hblock m hm
    obtain ⟨hs1', hs2', hs3'⟩ := hblock m' hm'
    have p1 := one_le_a (m - 2 * blockIdx v m)
    have p2 := one_le_a (m' - 2 * blockIdx v m')
    simp only at heq
    have hw : a (m - 2 * blockIdx v m) = a (m' - 2 * blockIdx v m') := by omega
    have hk : m - 2 * blockIdx v m = m' - 2 * blockIdx v m' := a_injective hw
    have hmid : a (m - blockIdx v m) = a (m' - blockIdx v m') := by omega
    have hk2 : m - blockIdx v m = m' - blockIdx v m' := a_injective hmid
    omega
  have hX0le : X0.card ≤ 3 * v := by
    have h := Finset.card_le_card_of_injOn
      (fun m => (a (m - 2 * blockIdx v m) - 1) / 2) hmaps hinj
    rwa [Finset.card_range] at h
  -- (e) at most `v - 1` positions below `4v` carry a value `≤ v`.
  have hLle : (R.filter (fun m => ¬ (v < a m))).card ≤ (Finset.Ico 1 v).card := by
    refine Finset.card_le_card_of_injOn a ?_ a_injective.injOn
    intro m hm
    rw [Finset.mem_coe, Finset.mem_filter, hRdef, Finset.mem_range] at hm
    obtain ⟨hmR, hmv⟩ := hm
    have h1 := one_le_a m
    have h2 : a m ≠ v := hcon m hmR
    simp only [Finset.coe_Ico, Set.mem_Ico]
    omega
  rw [Nat.card_Ico] at hLle
  have hRcard : R.card = 4 * v := by rw [hRdef]; exact Finset.card_range _
  have hsum : X0.card + (R.filter (fun m => ¬ (v < a m))).card = R.card := by
    rw [hX0def]
    exact Finset.card_filter_add_card_filter_not _
  omega

/-- **Surjectivity onto the positive integers** (Hegarty, Theorem 3.1). -/
theorem a_surjective {v : ℕ} (hv : 1 ≤ v) : ∃ n, a n = v := by
  obtain ⟨n, -, hn⟩ := thm_3_1 hv
  exact ⟨n, hn⟩

/-- **"The Hegarty paper shows that this is a permutation"** (OEIS comment, Adams-Watters):
`a` is a bijection from the positions `ℕ` onto the positive integers. -/
theorem a_bijOn : Set.BijOn a Set.univ {v : ℕ | 1 ≤ v} := by
  refine ⟨fun n _ => one_le_a n, a_injective.injOn, ?_⟩
  intro v hv
  obtain ⟨n, hn⟩ := a_surjective hv
  exact ⟨n, Set.mem_univ n, hn⟩

/-! ## Hegarty display (4), lower half: `N/4 ≤ a(N)` -/

/-- **Hegarty, display (4), left half** (0-indexed): `n < 4 * a n`, i.e. `N ≤ 4·a(N)` and so
`a(N)/N ≥ 1/4` at OEIS index `N = n + 1`.  Immediate from Theorem 3.1: the value `a n`
already occurs at some position `< 4·a n`, and by injectivity that position is `n`. -/
theorem lt_four_mul_a (n : ℕ) : n < 4 * a n := by
  obtain ⟨m, hm, ham⟩ := thm_3_1 (one_le_a n)
  have hmn : m = n := a_injective ham
  omega

/-- **Hegarty's proved bounds in OEIS shape**, over `ℝ` and 0-indexed
(`a n = A094870(n+1)`, so `(n : ℝ) + 1` is the OEIS index `N`, never `0`):
`N/4 ≤ a(N) < 3N/2`.  The left bound is display (4); the companion module
`Enumerative.HegartyThreeEighths` formalizes Hegarty's Theorem 3.3 sharpening `1/4` to
`3/8`. -/
theorem hegarty_bounds (n : ℕ) :
    ((n : ℝ) + 1) / 4 ≤ (a n : ℝ) ∧ (a n : ℝ) < 3 * ((n : ℝ) + 1) / 2 := by
  constructor
  · have h : (n : ℝ) + 1 ≤ 4 * (a n : ℝ) := by
      have hn : n + 1 ≤ 4 * a n := lt_four_mul_a n
      exact_mod_cast hn
    linarith
  · have h : 2 * (a n : ℝ) < 3 * ((n : ℝ) + 1) := by
      have hn : 2 * a n < 3 * (n + 1) := two_mul_a_lt n
      exact_mod_cast hn
    linarith

/-! ## The archived conjecture (OPEN — the file's single intended `sorry`) -/

/-- **Hegarty, Conjecture 3.2** = the OEIS comment "Conjecture: lim_{n->infinity} a(n)/n = 1
(P. Hegarty)", 0-indexed: `a n / (n + 1) → 1`, where `a n = A094870(n+1)` so that `(n : ℝ) +
1` is the OEIS index.  Hegarty writes of it: "We have no idea how one might prove this - our
only real evidence is numerical."

**Status: open.**  This is the single intended `sorry` of the file.  It is not vacuous: by
`ratio_mem_Ico` the sequence `a n / (n + 1)` is confined to `[1/4, 3/2)` for every `n`, so
the assertion is that a bounded sequence bounded away from `0` converges to the specific
interior point `1`. -/
theorem conj_3_2 :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / ((n : ℝ) + 1)) Filter.atTop (nhds 1) := by
  -- intended sorry: open conjecture (Hegarty, Conjecture 3.2; OEIS A094870 comment 2).
  sorry

/-- **The conjectured limit is a statement about a genuinely bounded quantity** (`sorry`-free):
Hegarty's proved bounds confine `a n / (n + 1)` to `[1/4, 3/2)` at every `n`, and the
conjectured limit `1` is an interior point of that interval. -/
theorem ratio_mem_Ico (n : ℕ) :
    (a n : ℝ) / ((n : ℝ) + 1) ∈ Set.Ico (1 / 4 : ℝ) (3 / 2) := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  obtain ⟨h1, h2⟩ := hegarty_bounds n
  refine Set.mem_Ico.mpr ⟨?_, ?_⟩
  · rw [le_div_iff₀ hpos]
    linarith
  · rw [div_lt_iff₀ hpos]
    linarith

/-! ## Ground checks against the OEIS `terms` field

`decide` is kernel reduction throughout; `native_decide` is not used anywhere in this file.
Each step supplies admissibility and minimality of the next term against the concrete
reversed prefix, which is exactly the OEIS rule with no appeal to any of the theory above. -/

/-- Ground check: the reversed prefix after one step. -/
theorem pre_one : pre 1 = [1] := by
  show a 0 :: pre 0 = [1]
  rw [a_zero, pre_zero]

/-- Ground check: `A094870(2) = 2`. -/
theorem a_one : a 1 = 2 := by
  show nextTerm (pre 1) = 2
  rw [pre_one]
  exact nextTerm_eq (by decide) (by decide)

/-- Ground check: the reversed prefix after two steps. -/
theorem pre_two : pre 2 = [2, 1] := by
  show a 1 :: pre 1 = [2, 1]
  rw [a_one, pre_one]

/-- Ground check: `A094870(3) = 4`.  This is the OEIS `%e` line, "a(3)=4 because it can't be
1=a(1), 2=a(2) and 3=2*a(3-1)-a(3-2)". -/
theorem a_two : a 2 = 4 := by
  show nextTerm (pre 2) = 4
  rw [pre_two]
  exact nextTerm_eq (by decide) (by decide)

/-- **Ground check**: the reversed 20-term prefix, i.e. the first 20 terms of the OEIS
`terms` field read backwards. -/
theorem pre_ground :
    pre 20 = [18, 23, 15, 22, 16, 17, 11, 14, 12, 13, 9, 10, 7, 8, 6, 5, 3, 4, 2, 1] := by
  have h2 : a 2 = 4 := a_two
  have p2 : pre 2 = [2, 1] := pre_two
  have p3 : pre 3 = [4, 2, 1] := by
    show a 2 :: pre 2 = [4, 2, 1]
    rw [h2, p2]
  have h3 : a 3 = 3 := by
    show nextTerm (pre 3) = 3
    rw [p3]; exact nextTerm_eq (by decide) (by decide)
  have p4 : pre 4 = [3, 4, 2, 1] := by
    show a 3 :: pre 3 = [3, 4, 2, 1]
    rw [h3, p3]
  have h4 : a 4 = 5 := by
    show nextTerm (pre 4) = 5
    rw [p4]; exact nextTerm_eq (by decide) (by decide)
  have p5 : pre 5 = [5, 3, 4, 2, 1] := by
    show a 4 :: pre 4 = [5, 3, 4, 2, 1]
    rw [h4, p4]
  have h5 : a 5 = 6 := by
    show nextTerm (pre 5) = 6
    rw [p5]; exact nextTerm_eq (by decide) (by decide)
  have p6 : pre 6 = [6, 5, 3, 4, 2, 1] := by
    show a 5 :: pre 5 = [6, 5, 3, 4, 2, 1]
    rw [h5, p5]
  have h6 : a 6 = 8 := by
    show nextTerm (pre 6) = 8
    rw [p6]; exact nextTerm_eq (by decide) (by decide)
  have p7 : pre 7 = [8, 6, 5, 3, 4, 2, 1] := by
    show a 6 :: pre 6 = [8, 6, 5, 3, 4, 2, 1]
    rw [h6, p6]
  have h7 : a 7 = 7 := by
    show nextTerm (pre 7) = 7
    rw [p7]; exact nextTerm_eq (by decide) (by decide)
  have p8 : pre 8 = [7, 8, 6, 5, 3, 4, 2, 1] := by
    show a 7 :: pre 7 = [7, 8, 6, 5, 3, 4, 2, 1]
    rw [h7, p7]
  have h8 : a 8 = 10 := by
    show nextTerm (pre 8) = 10
    rw [p8]; exact nextTerm_eq (by decide) (by decide)
  have p9 : pre 9 = [10, 7, 8, 6, 5, 3, 4, 2, 1] := by
    show a 8 :: pre 8 = [10, 7, 8, 6, 5, 3, 4, 2, 1]
    rw [h8, p8]
  have h9 : a 9 = 9 := by
    show nextTerm (pre 9) = 9
    rw [p9]; exact nextTerm_eq (by decide) (by decide)
  have p10 : pre 10 = [9, 10, 7, 8, 6, 5, 3, 4, 2, 1] := by
    show a 9 :: pre 9 = [9, 10, 7, 8, 6, 5, 3, 4, 2, 1]
    rw [h9, p9]
  have h10 : a 10 = 13 := by
    show nextTerm (pre 10) = 13
    rw [p10]; exact nextTerm_eq (by decide) (by decide)
  have p11 : pre 11 = [13, 9, 10, 7, 8, 6, 5, 3, 4, 2, 1] := by
    show a 10 :: pre 10 = [13, 9, 10, 7, 8, 6, 5, 3, 4, 2, 1]
    rw [h10, p10]
  have h11 : a 11 = 12 := by
    show nextTerm (pre 11) = 12
    rw [p11]; exact nextTerm_eq (by decide) (by decide)
  have p12 : pre 12 = [12, 13, 9, 10, 7, 8, 6, 5, 3, 4, 2, 1] := by
    show a 11 :: pre 11 = [12, 13, 9, 10, 7, 8, 6, 5, 3, 4, 2, 1]
    rw [h11, p11]
  have h12 : a 12 = 14 := by
    show nextTerm (pre 12) = 14
    rw [p12]; exact nextTerm_eq (by decide) (by decide)
  have p13 : pre 13 = [14, 12, 13, 9, 10, 7, 8, 6, 5, 3, 4, 2, 1] := by
    show a 12 :: pre 12 = [14, 12, 13, 9, 10, 7, 8, 6, 5, 3, 4, 2, 1]
    rw [h12, p12]
  have h13 : a 13 = 11 := by
    show nextTerm (pre 13) = 11
    rw [p13]; exact nextTerm_eq (by decide) (by decide)
  have p14 : pre 14 = [11, 14, 12, 13, 9, 10, 7, 8, 6, 5, 3, 4, 2, 1] := by
    show a 13 :: pre 13 = [11, 14, 12, 13, 9, 10, 7, 8, 6, 5, 3, 4, 2, 1]
    rw [h13, p13]
  have h14 : a 14 = 17 := by
    show nextTerm (pre 14) = 17
    rw [p14]; exact nextTerm_eq (by decide) (by decide)
  have p15 : pre 15 = [17, 11, 14, 12, 13, 9, 10, 7, 8, 6, 5, 3, 4, 2, 1] := by
    show a 14 :: pre 14 = [17, 11, 14, 12, 13, 9, 10, 7, 8, 6, 5, 3, 4, 2, 1]
    rw [h14, p14]
  have h15 : a 15 = 16 := by
    show nextTerm (pre 15) = 16
    rw [p15]; exact nextTerm_eq (by decide) (by decide)
  have p16 : pre 16 = [16, 17, 11, 14, 12, 13, 9, 10, 7, 8, 6, 5, 3, 4, 2, 1] := by
    show a 15 :: pre 15 = [16, 17, 11, 14, 12, 13, 9, 10, 7, 8, 6, 5, 3, 4, 2, 1]
    rw [h15, p15]
  have h16 : a 16 = 22 := by
    show nextTerm (pre 16) = 22
    rw [p16]; exact nextTerm_eq (by decide) (by decide)
  have p17 : pre 17 = [22, 16, 17, 11, 14, 12, 13, 9, 10, 7, 8, 6, 5, 3, 4, 2, 1] := by
    show a 16 :: pre 16 = [22, 16, 17, 11, 14, 12, 13, 9, 10, 7, 8, 6, 5, 3, 4, 2, 1]
    rw [h16, p16]
  have h17 : a 17 = 15 := by
    show nextTerm (pre 17) = 15
    rw [p17]; exact nextTerm_eq (by decide) (by decide)
  have p18 : pre 18 = [15, 22, 16, 17, 11, 14, 12, 13, 9, 10, 7, 8, 6, 5, 3, 4, 2, 1] := by
    show a 17 :: pre 17 = [15, 22, 16, 17, 11, 14, 12, 13, 9, 10, 7, 8, 6, 5, 3, 4, 2, 1]
    rw [h17, p17]
  have h18 : a 18 = 23 := by
    show nextTerm (pre 18) = 23
    rw [p18]; exact nextTerm_eq (by decide) (by decide)
  have p19 : pre 19 =
      [23, 15, 22, 16, 17, 11, 14, 12, 13, 9, 10, 7, 8, 6, 5, 3, 4, 2, 1] := by
    show a 18 :: pre 18 = [23, 15, 22, 16, 17, 11, 14, 12, 13, 9, 10, 7, 8, 6, 5, 3, 4, 2, 1]
    rw [h18, p18]
  have h19 : a 19 = 18 := by
    show nextTerm (pre 19) = 18
    rw [p19]; exact nextTerm_eq (by decide) (by decide)
  show a 19 :: pre 19 = _
  rw [h19, p19]

/-- **Ground check, pointwise**: `a k` for `k < 20` is the `k`-th entry of the OEIS `terms`
field of A094870. -/
theorem a_eq_of_lt_twenty {k : ℕ} (hk : k < 20) :
    a k = [1, 2, 4, 3, 5, 6, 8, 7, 10, 9, 13, 12, 14, 11, 17, 16, 22, 15, 23, 18].getD k 0 := by
  have h : a k = (pre 20).getD (19 - k) 0 := by
    rw [pre_getD 20 (19 - k) (by omega), show 20 - 1 - (19 - k) = k from by omega]
  rw [h, pre_ground]
  interval_cases k <;> rfl

/-- **Ground check**: the first 20 terms of `a` are the first 20 entries of the OEIS `terms`
field of A094870, `1,2,4,3,5,6,8,7,10,9,13,12,14,11,17,16,22,15,23,18`. -/
theorem a_ground : (List.range 20).map a =
    [1, 2, 4, 3, 5, 6, 8, 7, 10, 9, 13, 12, 14, 11, 17, 16, 22, 15, 23, 18] := by
  have key : ∀ k ∈ List.range 20, a k =
      [1, 2, 4, 3, 5, 6, 8, 7, 10, 9, 13, 12, 14, 11, 17, 16, 22, 15, 23, 18].getD k 0 :=
    fun k hk => a_eq_of_lt_twenty (List.mem_range.mp hk)
  rw [List.map_congr_left key]
  decide

/- **Independent cross-check of the greedy definition.**  `a_ground` above is
kernel-checked, but it is proved step by step from the concrete prefixes.  The `#eval` below
instead *runs* the recursion — `Nat.find` over `IsCandList`, i.e. the literal OEIS rule —
and prints

  `[1, 2, 4, 3, 5, 6, 8, 7, 10, 9, 13, 12, 14, 11, 17, 16, 22, 15, 23, 18, 21, 20, 25, 24,
    26, 19, 28, 27, 29, 36]`,

the first 30 entries of the OEIS `terms` field.  This is a diagnostic, not a proof, and
contributes no axioms. -/
#eval (List.range 30).map a

/-! ## Satisfiability of the hypotheses

Each theorem above with hypotheses is instantiated jointly at a concrete point, so nothing
is vacuous. -/

/-- `IsCand` is genuinely satisfiable: `4` is admissible at position `2`.  This re-derives
`a 2 ≤ 4` from the index-level rule alone, independently of the `nextTerm`-level chain that
proves `a_two`. -/
theorem isCand_two_four : IsCand 2 4 := by
  refine ⟨by omega, ?_, ?_⟩
  · intro m hm
    interval_cases m
    · rw [a_zero]; omega
    · rw [a_one]; omega
  · intro i hi hin
    have hi1 : i = 1 := by omega
    subst hi1
    rw [show (2 : ℕ) - 2 * 1 = 0 from rfl, show (2 : ℕ) - 1 = 1 from rfl, a_zero, a_one]
    omega

/-- Joint instantiation of the hypotheses of `a_le_of_isCand` at `n = 2`, `t = 4`. -/
example : a 2 ≤ 4 := a_le_of_isCand isCand_two_four

/-- `IsCand` is not vacuously true of everything: `3` is *rejected* at position `2`, which is
the OEIS `%e` line "a(3)=4 because it can't be 1=a(1), 2=a(2) and 3=2*a(3-1)-a(3-2)". -/
theorem not_isCand_two_three : ¬ IsCand 2 3 :=
  not_isCand_of_lt (by rw [a_two]; omega)

/-- Joint instantiation of the hypotheses of `a_avoidsAP` at `(x, y, z) = (0, 1, 2)`:
`0 ≠ 2` and `0 + 2 = 2·1` both hold, and the conclusion fires. -/
example : a 0 + a 2 ≠ 2 * a 1 := a_avoidsAP (by omega) (by omega)

/-- Joint instantiation of the hypotheses of `thm_3_1` / `a_surjective` at `v = 3`. -/
example : ∃ n, n < 4 * 3 ∧ a n = 3 := thm_3_1 (by omega)

/-- Joint instantiation of the hypotheses of `a_ne_of_lt` at `(m, n) = (0, 1)`. -/
example : a 0 ≠ a 1 := a_ne_of_lt (by omega)

/-- The conclusion of `a_bijOn` is attained at a concrete point: `1` is hit, at position
`0`. -/
example : (1 : ℕ) ∈ a '' Set.univ := ⟨0, Set.mem_univ 0, a_zero⟩

/-- The bounds of `hegarty_bounds` are consistent and strict at a concrete point: at `n = 2`
they read `3/4 ≤ 4 < 9/2`. -/
example : ((2 : ℕ) : ℝ) + 1 ≤ 4 * (a 2 : ℝ) := by
  have h : (2 : ℕ) + 1 ≤ 4 * a 2 := lt_four_mul_a 2
  exact_mod_cast h

/-- Joint instantiation of the hypothesis of `a_eq_of_lt_twenty` at `k = 16`, giving the
OEIS `a(17) = 22`. -/
example : a 16 = 22 := a_eq_of_lt_twenty (by omega)

/-- Joint instantiation of the hypothesis of `pre_getD` at `n = 20`, `k = 0`. -/
example : (pre 20).getD 0 0 = a 19 := pre_getD 20 0 (by omega)

/-- Joint instantiation of the hypothesis of `le_listMax`, and evidence that it is not
vacuous: `2 ∈ [3, 7, 2]`. -/
example : (2 : ℕ) ≤ listMax [3, 7, 2] := le_listMax (by decide)

/-- `getD_le_listMax` fires both in range and out of range. -/
example : ([3, 7, 2] : List ℕ).getD 1 0 ≤ listMax [3, 7, 2] ∧
    ([3, 7, 2] : List ℕ).getD 9 0 ≤ listMax [3, 7, 2] :=
  ⟨getD_le_listMax _ 1, getD_le_listMax _ 9⟩

/-- Both directions of `isCandList_pre_iff` are instantiated at a point where they hold:
`4` is admissible at position `2` on either side. -/
example : IsCandList (pre 2) 4 := isCandList_pre_iff.mpr isCand_two_four

/-- `mem_pre_iff` is instantiated at a point where both sides hold. -/
example : (4 : ℕ) ∈ pre 3 := (mem_pre_iff 3 4).mpr ⟨2, by omega, a_two⟩

/-- `nextTerm_eq`'s two hypotheses are jointly satisfiable — witnessed by `a_one`, and here
again on the empty prefix, where the answer is the seed `1`. -/
example : nextTerm [] = 1 := nextTerm_eq (by decide) (by decide)

/-- `exists_isCandList`'s witness bound is not vacuous: on `[2, 1]` the bound `2·2+1 = 5` is
admissible, though the *least* admissible value is `4`. -/
example : IsCandList [2, 1] 5 ∧ IsCandList [2, 1] 4 ∧ ¬ IsCandList [2, 1] 3 := by decide

end A094870

/-! ## Axiom audit

`A094870.conj_3_2` carries the file's single intended `sorry` and reports `sorryAx` by
construction.  Every other declaration in the file — the full public surface is swept
below — must report a subset of `{propext, Classical.choice, Quot.sound}`. -/

#print axioms A094870.IsCandList
#print axioms A094870.instDecidableIsCandList
#print axioms A094870.listMax
#print axioms A094870.listMax_cons
#print axioms A094870.le_listMax
#print axioms A094870.getD_le_listMax
#print axioms A094870.exists_isCandList
#print axioms A094870.nextTerm
#print axioms A094870.nextTerm_eq
#print axioms A094870.pre
#print axioms A094870.a
#print axioms A094870.pre_succ
#print axioms A094870.pre_zero
#print axioms A094870.pre_length
#print axioms A094870.pre_getD
#print axioms A094870.mem_pre_iff
#print axioms A094870.IsCand
#print axioms A094870.isCandList_pre_iff
#print axioms A094870.isCand_a
#print axioms A094870.a_le_of_isCand
#print axioms A094870.not_isCand_of_lt
#print axioms A094870.a_ne_of_lt
#print axioms A094870.blockIdx
#print axioms A094870.pre_one
#print axioms A094870.a_one
#print axioms A094870.pre_two
#print axioms A094870.a_two
#print axioms A094870.a_eq_of_lt_twenty
#print axioms A094870.a_zero
#print axioms A094870.isLeast_a
#print axioms A094870.one_le_a
#print axioms A094870.a_injective
#print axioms A094870.a_avoidsAP
#print axioms A094870.not_a_avoidsAP_without_ne
#print axioms A094870.two_mul_a_lt
#print axioms A094870.hegarty_eq_1
#print axioms A094870.thm_3_1
#print axioms A094870.a_surjective
#print axioms A094870.a_bijOn
#print axioms A094870.lt_four_mul_a
#print axioms A094870.hegarty_bounds
#print axioms A094870.ratio_mem_Ico
#print axioms A094870.pre_ground
#print axioms A094870.a_ground
#print axioms A094870.isCand_two_four
#print axioms A094870.not_isCand_two_three
#print axioms A094870.conj_3_2
