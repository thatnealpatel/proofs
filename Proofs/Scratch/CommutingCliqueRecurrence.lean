/-
  Scratch/CommutingCliqueRecurrence — Barker's commuting-clique recurrences
  for symmetric and alternating groups (OEIS A135908, A135909).

  A135908(n) is the clique number of the commuting graph of `S_n`, A135909(n)
  the same for `A_n`.  Vertex-set convention: the literature carries three
  (all of `G`; `G ∖ Z(G)`, used by the entries' reference Iranmanesh &
  Jafarzadeh 2008; `G ∖ {1}`).  They agree for `S_n` (n ≥ 3) and `A_n`
  (n ≥ 4) and differ only at the two boundary terms — the entries' own
  boundary data is mixed (A135908(2) = 0 fits `G ∖ Z(G)`, A135909(3) = 2
  fits `G ∖ {1}`).  This file takes `G ∖ {1}`.
  Colin Barker (2013-07-26) conjectured the recurrence
  `a(n) = a(n-1) + 3·a(n-3) - 3·a(n-4)` for `n > 7` (A135908) and `n > 6`
  (A135909), with explicit rational generating functions.

  This file proves the recurrence for A135908 in the range `5 < n` on this
  file's `a135908` (which takes the value 1 at `n = 2`; on the entry's
  published terms, with a(2) = 0, the recurrence first holds at `n = 7`, so
  only Barker's claimed range `7 < n` transfers to the published data), by
  the chain

    clique number of commuting graph on nonidentity elements + 1
      = clique number of commuting graph on all elements       (universal `1`)
      = largest order of an abelian subgroup                   (bridge)
      = A000792(n)  for `S_n`                                  (Bercov–Moser),

  where A000792 satisfies `a(n+3) = 3·a(n)` for `n ≥ 2` and the linear
  recurrence follows mechanically.  The Bercov–Moser step is proved here in
  both directions: the upper bound by induction on orbits (for abelian `H`
  the stabilizer of a point fixes its whole orbit pointwise), the lower bound
  by an explicit direct product of cycle groups on disjoint blocks.

  Ground-truth deviations from the OEIS entries, disclosed:
  * A135908: the entry sets a(2) = 0 "by convention (or should it be 1?)";
    the graph-honest value on the one-vertex graph is 1, and this file's
    `a135908` takes the value 1 at `n = 2`.  All other terms agree.
  * A135909: Barker's claimed validity range `n > 6` is *false* against the
    entry's own data: at `n = 8` the recurrence predicts 14 while a(8) = 15,
    and at `n = 9` it predicts 27 while a(9) = 26.  This numerical refutation
    is unconditional; it is immediate from the published terms.  The Lean
    theorem about the actual alternating-group clique numbers is conditional
    on `AltStructure`, as is the positive recurrence for `n > 9`.  Barker's
    own generating function in the same formula clause already encodes
    `n > 9`: its numerator has degree 9 over a degree-4 denominator, and the
    nonzero numerator coefficients predict exactly the observed failure set —
    the stated range contradicts the g.f. beside it.  Repository issue #36
    is a correction report, not evidence that OEIS has accepted or applied
    the change.

  Novelty language is deliberately limited: no prior written proof of Barker's
  recurrence and no general published determination of the largest abelian
  subgroup order of `A_n` were found in the searched sources.  These are
  found-no-record statements, not priority claims.  `AltStructure` remains an
  open prospective result in this file.
-/
import Mathlib

set_option autoImplicit false

namespace CommutingClique

open Equiv (Perm)

/-! ### The Bercov–Moser sequence A000792 -/

/-- OEIS A000792: the largest product of a multiset of positive integers with
sum `n` (all parts `3` up to boundary corrections `2`, `4`).  By Bercov–Moser
(1965) it is also the largest order of an abelian subgroup of `S_n`, which is
proved below as `maxAbelianOrder_perm`.  It satisfies `a (n+3) = 3 * a n` for
`2 ≤ n`, packaged here as the structural recursion `a (n+5) = 3 * a (n+2)`. -/
def a000792 : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | n + 5 => 3 * a000792 (n + 2)

/-- Ground truth: the first thirteen terms match the OEIS A000792 entry. -/
example : (List.range 13).map a000792 = [1, 1, 2, 3, 4, 6, 9, 12, 18, 27, 36, 54, 81] := by
  rfl

/-- A000792 is positive. -/
theorem a000792_pos (n : ℕ) : 0 < a000792 n := by
  induction n using a000792.induct with
  | case1 => decide
  | case2 => decide
  | case3 => decide
  | case4 => decide
  | case5 => decide
  | case6 n ih => rw [a000792]; omega

/-- A000792 grows weakly at each step. -/
theorem a000792_le_succ (n : ℕ) : a000792 n ≤ a000792 (n + 1) := by
  induction n using a000792.induct with
  | case1 => decide
  | case2 => decide
  | case3 => decide
  | case4 => decide
  | case5 => decide
  | case6 n ih =>
    show a000792 (n + 5) ≤ a000792 (n + 1 + 5)
    rw [a000792, a000792]
    exact Nat.mul_le_mul_left 3 ih

/-- A000792 is monotone. -/
theorem a000792_monotone : Monotone a000792 :=
  monotone_nat_of_le_succ a000792_le_succ

/-- The defining three-step recursion of A000792 in its natural range. -/
theorem a000792_add_three {n : ℕ} (hn : 2 ≤ n) : a000792 (n + 3) = 3 * a000792 n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rfl

/-- Doubling bound: `2 * a n ≤ a (n + 2)`. -/
theorem two_mul_a000792_le (n : ℕ) : 2 * a000792 n ≤ a000792 (n + 2) := by
  induction n using a000792.induct with
  | case1 => decide
  | case2 => decide
  | case3 => decide
  | case4 => decide
  | case5 => decide
  | case6 n ih =>
    have h7 : a000792 (n + 5 + 2) = 3 * a000792 (n + 2 + 2) := a000792_add_three (by omega)
    rw [a000792, h7]
    omega

/-- Tripling bound: `3 * a n ≤ a (n + 3)`. -/
theorem three_mul_a000792_le (n : ℕ) : 3 * a000792 n ≤ a000792 (n + 3) := by
  match n with
  | 0 => decide
  | 1 => decide
  | n + 2 => exact (a000792_add_three (by omega)).ge

/-- Quadrupling bound: `4 * a n ≤ a (n + 4)`. -/
theorem four_mul_a000792_le (n : ℕ) : 4 * a000792 n ≤ a000792 (n + 4) := by
  induction n using a000792.induct with
  | case1 => decide
  | case2 => decide
  | case3 => decide
  | case4 => decide
  | case5 => decide
  | case6 n ih =>
    have h9 : a000792 (n + 5 + 4) = 3 * a000792 (n + 2 + 4) := a000792_add_three (by omega)
    rw [a000792, h9]
    omega

/-- The master superadditivity bound behind the orbit induction: a block of
size `k ≠ 0` contributes at least a factor `k`, `k * a m ≤ a (m + k)`. -/
theorem mul_a000792_le (k : ℕ) : ∀ m : ℕ, k ≠ 0 → k * a000792 m ≤ a000792 (m + k) := by
  induction k using a000792.induct with
  | case1 => intro m h0; exact absurd rfl h0
  | case2 => intro m _; simpa using a000792_le_succ m
  | case3 => intro m _; exact two_mul_a000792_le m
  | case4 => intro m _; exact three_mul_a000792_le m
  | case5 => intro m _; exact four_mul_a000792_le m
  | case6 k ih =>
    intro m _
    show (k + 5) * a000792 m ≤ a000792 (m + (k + 5))
    have h1 : (k + 5) * a000792 m ≤ (3 * (k + 2)) * a000792 m :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (3 * (k + 2)) * a000792 m = (k + 2) * (3 * a000792 m) := by ring
    have h3 : (k + 2) * (3 * a000792 m) ≤ (k + 2) * a000792 (m + 3) :=
      Nat.mul_le_mul_left _ (three_mul_a000792_le m)
    have h4 : (k + 2) * a000792 (m + 3) ≤ a000792 (m + 3 + (k + 2)) :=
      ih (m + 3) (by omega)
    rw [show m + 3 + (k + 2) = m + (k + 5) from by omega] at h4
    omega

/-- The shifted Barker recurrence for A000792 itself, in subtraction-free
form: `a (m+6) = a (m+5) + 3 * a (m+3) - 3 * a (m+2)` over `ℤ`. -/
theorem a000792_barker_shift (m : ℕ) :
    (a000792 (m + 6) : ℤ) =
      a000792 (m + 5) + 3 * a000792 (m + 3) - 3 * a000792 (m + 2) := by
  have h1 : a000792 (m + 3 + 3) = 3 * a000792 (m + 3) := a000792_add_three (by omega)
  have h2 : a000792 (m + 2 + 3) = 3 * a000792 (m + 2) := a000792_add_three (by omega)
  have e1 : m + 3 + 3 = m + 6 := by omega
  have e2 : m + 2 + 3 = m + 5 := by omega
  rw [e1] at h1
  rw [e2] at h2
  push_cast [h1, h2]
  ring

/-! ### The commuting graph -/

/-- The commuting graph of a multiplicative structure `G`: the vertices are
all elements of `G` and two distinct elements are adjacent exactly when they
commute.  (Standard object in the literature — the entries' reference
Iranmanesh & Jafarzadeh 2008 is devoted to it; new to this repo only because
Mathlib has no commuting graph as of this toolchain.) -/
def commutingGraph (G : Type*) [Mul G] : SimpleGraph G where
  Adj x y := x ≠ y ∧ Commute x y
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Adjacency in the commuting graph: distinct elements that commute. -/
@[simp]
theorem commutingGraph_adj {G : Type*} [Mul G] {x y : G} :
    (commutingGraph G).Adj x y ↔ x ≠ y ∧ Commute x y :=
  Iff.rfl

/-- Ground truth: distinct elements of an abelian group are adjacent. -/
example : (commutingGraph (ZMod 3)).Adj 0 1 :=
  ⟨by decide, show (0 * 1 : ZMod 3) = 1 * 0 by decide⟩

/-- Ground truth: the two transpositions `(0 1)` and `(0 2)` of `S_3` do not
commute, so they are not adjacent in the commuting graph. -/
example : ¬ (commutingGraph (Perm (Fin 3))).Adj (Equiv.swap 0 1) (Equiv.swap 0 2) := by
  rintro ⟨-, hc⟩
  have h0 := congrArg (fun σ : Perm (Fin 3) => σ 0) hc
  simp [Equiv.swap_apply_def, Equiv.Perm.mul_apply] at h0

/-! ### The largest abelian subgroup order -/

/-- The largest order of an abelian subgroup of the group `G`. -/
noncomputable def maxAbelianOrder (G : Type*) [Group G] : ℕ :=
  sSup {n | ∃ H : Subgroup G, IsMulCommutative H ∧ Nat.card H = n}

section MaxAbelianOrder

variable {G : Type*} [Group G]

/-- The trivial subgroup is abelian. -/
theorem isMulCommutative_bot : IsMulCommutative (⊥ : Subgroup G) := by
  refine .of_setLike_mul_comm fun a ha b hb => ?_
  rw [Subgroup.mem_bot] at ha hb
  rw [ha, hb]

/-- Any abelian subgroup order is at most `maxAbelianOrder`. -/
theorem le_maxAbelianOrder [Finite G] (H : Subgroup G) (hH : IsMulCommutative H) :
    Nat.card H ≤ maxAbelianOrder G := by
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨H, hH, rfl⟩
  rintro n ⟨K, -, rfl⟩
  exact Subgroup.card_le_card_group K

/-- To bound `maxAbelianOrder` it suffices to bound every abelian subgroup. -/
theorem maxAbelianOrder_le {m : ℕ}
    (h : ∀ H : Subgroup G, IsMulCommutative H → Nat.card H ≤ m) :
    maxAbelianOrder G ≤ m := by
  refine csSup_le ⟨1, ⊥, isMulCommutative_bot, Subgroup.card_bot⟩ ?_
  rintro n ⟨H, hH, rfl⟩
  exact h H hH

/-- For an abelian group the largest abelian subgroup is the whole group. -/
theorem maxAbelianOrder_eq_card [Finite G] (hG : IsMulCommutative G) :
    maxAbelianOrder G = Nat.card G := by
  haveI := hG
  refine le_antisymm (maxAbelianOrder_le fun H _ => Subgroup.card_le_card_group H) ?_
  have htop := le_maxAbelianOrder (⊤ : Subgroup G) inferInstance
  rwa [Subgroup.card_top] at htop

/-- Ground truth: the cyclic group of order 12. -/
example : maxAbelianOrder (Multiplicative (ZMod 12)) = 12 := by
  rw [maxAbelianOrder_eq_card ⟨⟨mul_comm⟩⟩, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

/-- `maxAbelianOrder` is monotone under passing to subgroups. -/
theorem maxAbelianOrder_subgroup_le [Finite G] (K : Subgroup G) :
    maxAbelianOrder K ≤ maxAbelianOrder G := by
  refine maxAbelianOrder_le fun H hH => ?_
  haveI := hH
  have hcard : Nat.card H = Nat.card (H.map K.subtype) :=
    Nat.card_congr (Subgroup.equivMapOfInjective H K.subtype K.subtype_injective).toEquiv
  rw [hcard]
  exact le_maxAbelianOrder (H.map K.subtype) inferInstance

/-- A direct product of abelian subgroups is abelian. -/
theorem isMulCommutative_prod {G₁ G₂ : Type*} [Group G₁] [Group G₂]
    (H₁ : Subgroup G₁) (H₂ : Subgroup G₂)
    (h₁ : IsMulCommutative H₁) (h₂ : IsMulCommutative H₂) :
    IsMulCommutative (H₁.prod H₂) := by
  haveI := h₁
  haveI := h₂
  refine .of_setLike_mul_comm fun a ha b hb => ?_
  rw [Subgroup.mem_prod] at ha hb
  exact Prod.ext (setLike_mul_comm ha.1 hb.1) (setLike_mul_comm ha.2 hb.2)

/-- The range of a homomorphism out of an abelian group is abelian. -/
theorem isMulCommutative_range {M N : Type*} [Group M] [Group N]
    (f : M →* N) (hM : IsMulCommutative M) : IsMulCommutative f.range := by
  haveI := hM
  refine .of_setLike_mul_comm fun a ha b hb => ?_
  rw [MonoidHom.mem_range] at ha hb
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  rw [← map_mul, ← map_mul, mul_comm' x y]

end MaxAbelianOrder

/-! ### Bridge: clique number equals largest abelian subgroup order -/

section Bridge

variable {G : Type*} [Group G] [Finite G]

/-- **Bridge** (cf. Arvind–Ma–Cameron–Maslova, *Aspects of the commuting
graph*, arXiv:2305.07301, whose maximal-clique ↔ maximal-abelian-subgroup
lemma this `cliqueNum` version is a corollary of).
The clique number of the commuting graph of a finite group is
the largest order of an abelian subgroup: a clique generates an abelian
subgroup containing it, and an abelian subgroup is a clique. -/
theorem cliqueNum_commutingGraph :
    (commutingGraph G).cliqueNum = maxAbelianOrder G := by
  classical
  refine le_antisymm ?_ (maxAbelianOrder_le fun H hH => ?_)
  · -- a maximum clique generates an abelian subgroup containing it
    obtain ⟨s, hs⟩ := (commutingGraph G).exists_isNClique_cliqueNum
    have hcomm : ∀ x ∈ (s : Set G), ∀ y ∈ (s : Set G), x * y = y * x := by
      intro x hx y hy
      rcases eq_or_ne x y with rfl | hne
      · rfl
      · exact (hs.isClique hx hy hne).2
    have habel : IsMulCommutative (Subgroup.closure (s : Set G)) :=
      Subgroup.isMulCommutative_closure hcomm
    have hsub : (s : Set G) ⊆ (Subgroup.closure (s : Set G) : Set G) :=
      Subgroup.subset_closure
    have hcards : Nat.card (s : Set G) = s.card := by
      rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    have hle : s.card ≤ Nat.card (Subgroup.closure (s : Set G)) := by
      rw [← hcards]
      exact Nat.card_le_card_of_injective (Set.inclusion hsub)
        (Set.inclusion_injective hsub)
    rw [← hs.card_eq]
    exact hle.trans (le_maxAbelianOrder _ habel)
  · -- an abelian subgroup is a clique
    haveI := hH
    have hfin : ((H : Set G)).Finite := Set.toFinite _
    have hclique : (commutingGraph G).IsClique (hfin.toFinset : Set G) := by
      rw [Set.Finite.coe_toFinset]
      intro x hx y hy hne
      exact ⟨hne, setLike_mul_comm hx hy⟩
    have hcards : hfin.toFinset.card = Nat.card H := by
      rw [← Set.ncard_eq_toFinset_card (H : Set G) hfin, ← Nat.card_coe_set_eq]
      rfl
    calc Nat.card H = hfin.toFinset.card := hcards.symm
      _ ≤ (commutingGraph G).cliqueNum := hclique.card_le_cliqueNum

/-- Removing the identity vertex drops the clique number of the commuting
graph by exactly one: the identity is adjacent to every other vertex. -/
theorem cliqueNum_induce_ne_one_add_one :
    ((commutingGraph G).induce {x : G | x ≠ 1}).cliqueNum + 1 =
      (commutingGraph G).cliqueNum := by
  classical
  refine le_antisymm ?_ ?_
  · -- push a maximum induced clique forward and adjoin the identity
    obtain ⟨t, ht⟩ :=
      ((commutingGraph G).induce {x : G | x ≠ 1}).exists_isNClique_cliqueNum
    rw [SimpleGraph.isNClique_induce_iff] at ht
    set t' : Finset G := t.map (Function.Embedding.subtype _) with ht'def
    have hone : (1 : G) ∉ t' := by
      simp only [ht'def, Finset.mem_map, Function.Embedding.coe_subtype]
      rintro ⟨⟨x, hx⟩, -, rfl⟩
      exact hx rfl
    have hclique : (commutingGraph G).IsClique ((insert (1 : G) t' : Finset G) : Set G) := by
      rw [Finset.coe_insert]
      exact ht.isClique.insert fun b _ hb1 => ⟨hb1, Commute.one_left b⟩
    have hcard : (insert (1 : G) t').card = t.card + 1 := by
      rw [Finset.card_insert_of_notMem hone, ht'def, Finset.card_map]
    calc ((commutingGraph G).induce {x : G | x ≠ 1}).cliqueNum + 1
        = t.card + 1 := by rw [← ht.card_eq, ht'def, Finset.card_map]
      _ = (insert (1 : G) t').card := hcard.symm
      _ ≤ (commutingGraph G).cliqueNum := hclique.card_le_cliqueNum
  · -- erase the identity from a maximum clique and pull it back
    obtain ⟨s, hs⟩ := (commutingGraph G).exists_isNClique_cliqueNum
    set t : Finset G := s.erase 1 with htdef
    have hclq : (commutingGraph G).IsClique (t : Set G) :=
      hs.isClique.subset (by rw [htdef, Finset.coe_subset]; exact Finset.erase_subset 1 s)
    set t₀ : Finset ↥{x : G | x ≠ 1} := t.subtype _ with ht₀def
    have hmap : t₀.map (Function.Embedding.subtype _) = t := by
      rw [ht₀def, Finset.subtype_map]
      refine Finset.filter_true_of_mem fun x hx => ?_
      rw [htdef] at hx
      exact Finset.ne_of_mem_erase hx
    have hnclique :
        ((commutingGraph G).induce {x : G | x ≠ 1}).IsNClique t.card t₀ := by
      rw [SimpleGraph.isNClique_induce_iff, hmap]
      exact ⟨hclq, rfl⟩
    have hle : t.card ≤ ((commutingGraph G).induce {x : G | x ≠ 1}).cliqueNum := by
      have h₀ := hnclique.isClique.card_le_cliqueNum
      rwa [hnclique.card_eq] at h₀
    have hcard : s.card ≤ t.card + 1 := by
      by_cases h1 : (1 : G) ∈ s
      · rw [htdef, Finset.card_erase_of_mem h1]
        omega
      · rw [htdef, Finset.erase_eq_of_notMem h1]
        omega
    rw [← hs.card_eq]
    omega

end Bridge

/-! ### Upper bound: abelian subgroups of finite permutation groups -/

/-- Induction-keyed form of the Bercov–Moser upper bound: strong induction
on the number of points of the permuted type.  For a point `a` with `H`-orbit
`O`, the stabilizer of `a` in abelian `H` fixes all of `O` pointwise, hence
embeds into the permutations of the complement of `O`; orbit–stabilizer then
gives `|H| = |O| * |stab|` and the arithmetic bound `k * a m ≤ a (m + k)`
closes the induction. -/
theorem card_le_a000792_aux :
    ∀ (n : ℕ) (α : Type*) [Finite α], Nat.card α = n →
      ∀ H : Subgroup (Perm α), IsMulCommutative H → Nat.card H ≤ a000792 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro α _ hcard H hH
    haveI := hH
    rcases isEmpty_or_nonempty α with hemp | hne
    · -- no points: the permutation group is trivial
      haveI : Subsingleton (Perm α) := ⟨fun f g => Equiv.ext fun x => (IsEmpty.false x).elim⟩
      haveI : Subsingleton H := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
      have h1 : Nat.card H = 1 := Nat.card_unique
      rw [h1]
      exact a000792_pos n
    · obtain ⟨a⟩ := hne
      set O : Set α := MulAction.orbit H a with hOdef
      set K : Subgroup H := MulAction.stabilizer H a with hKdef
      have hak : a ∈ O := MulAction.mem_orbit_self a
      haveI : Nonempty O := ⟨⟨a, hak⟩⟩
      set k : ℕ := Nat.card O with hkdef
      have hk1 : 1 ≤ k := Nat.card_pos
      have hkn : k ≤ n := by
        rw [← hcard, hkdef]
        exact Nat.card_le_card_of_injective _ Subtype.val_injective
      -- orbit–stabilizer: |H| = |O| * |K|
      have hsplit : Nat.card H = k * Nat.card K := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup K, hkdef]
        congr 1
        exact (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer H a)).symm
      -- commutativity: the stabilizer of `a` fixes the whole orbit pointwise
      have hfix : ∀ g : H, g ∈ K → ∀ x ∈ O, g • x = x := by
        intro g hg x hx
        obtain ⟨h, rfl⟩ := hx
        have hga : g • a = a := MulAction.mem_stabilizer_iff.mp hg
        calc g • h • a = (g * h) • a := (mul_smul g h a).symm
          _ = (h * g) • a := by rw [mul_comm' g h]
          _ = h • g • a := mul_smul h g a
          _ = h • a := by rw [hga]
      -- stabilizer elements also preserve the complement of the orbit
      have hnotmem : ∀ g : H, g ∈ K → ∀ x : α, x ∉ O → g • x ∉ O := by
        intro g hg x hx hmem
        have h1 : g⁻¹ • g • x = g • x := hfix g⁻¹ (inv_mem hg) (g • x) hmem
        rw [inv_smul_smul] at h1
        exact hx (h1 ▸ hmem)
      have hprop : ∀ g : K, ∀ x : α, ((g : H) : Perm α) x ∉ O ↔ x ∉ O := by
        intro g x
        constructor
        · intro hgx hxO
          have h1 : (g : H) • x = x := hfix g g.2 x hxO
          rw [Subgroup.smul_def, Equiv.Perm.smul_def] at h1
          exact hgx (by rw [h1]; exact hxO)
        · intro hx
          have h1 := hnotmem g g.2 x hx
          rwa [Subgroup.smul_def, Equiv.Perm.smul_def] at h1
      -- the stabilizer embeds into the permutations of the complement
      set ψ : K →* Perm {x : α // x ∉ O} :=
        { toFun := fun g => Equiv.Perm.subtypePerm ((g : H) : Perm α) (hprop g)
          map_one' := rfl
          map_mul' := fun _ _ => rfl } with hψdef
      have hinj : Function.Injective ψ := by
        intro g h hgh
        have happ : ∀ x : α, ((g : H) : Perm α) x = ((h : H) : Perm α) x := by
          intro x
          by_cases hx : x ∈ O
          · have h1 : (g : H) • x = x := hfix g g.2 x hx
            have h2 : (h : H) • x = x := hfix h h.2 x hx
            rw [Subgroup.smul_def, Equiv.Perm.smul_def] at h1 h2
            rw [h1, h2]
          · have hval := congrArg
              (fun σ : Perm {x : α // x ∉ O} => (σ ⟨x, hx⟩ : {x : α // x ∉ O}).val) hgh
            exact hval
        apply Subtype.ext
        apply Subtype.ext
        exact Equiv.ext happ
      -- cards on the complement
      have hOcompl : Nat.card {x : α // x ∉ O} = n - k := by
        have h1 : O.ncard + Oᶜ.ncard = Nat.card α := Set.ncard_add_ncard_compl O (Set.toFinite O)
        have h2 : Nat.card {x : α // x ∉ O} = Oᶜ.ncard := Nat.card_coe_set_eq _
        have h3 : k = O.ncard := by rw [hkdef, Nat.card_coe_set_eq]
        omega
      have hrange : IsMulCommutative ψ.range := isMulCommutative_range ψ inferInstance
      have hcardK : Nat.card K = Nat.card ψ.range :=
        Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
      have hIHapp : Nat.card ψ.range ≤ a000792 (n - k) := by
        have hlt : n - k < n := by omega
        exact IH (n - k) hlt {x : α // x ∉ O} hOcompl ψ.range hrange
      calc Nat.card H = k * Nat.card K := hsplit
        _ = k * Nat.card ψ.range := by rw [hcardK]
        _ ≤ k * a000792 (n - k) := Nat.mul_le_mul_left k hIHapp
        _ ≤ a000792 (n - k + k) := mul_a000792_le k (n - k) (by omega)
        _ = a000792 n := by rw [show n - k + k = n from by omega]

/-- **Bercov–Moser upper bound.** An abelian subgroup of the permutation
group of a finite type `α` has order at most `a000792 (Nat.card α)`. -/
theorem card_le_a000792_of_isMulCommutative {α : Type*} [Finite α]
    (H : Subgroup (Perm α)) (hH : IsMulCommutative H) :
    Nat.card H ≤ a000792 (Nat.card α) :=
  card_le_a000792_aux (Nat.card α) α rfl H hH

/-! ### Lower bound: direct products of cycle groups on disjoint blocks -/

/-- **Bercov–Moser lower bound.** `Perm (Fin n)` contains an abelian subgroup
of order exactly `a000792 n`: a product of cyclic groups generated by
disjoint 3-cycles, with a single 1-, 2- or 4-cycle boundary block. -/
theorem exists_isMulCommutative_card_a000792 (n : ℕ) :
    ∃ H : Subgroup (Perm (Fin n)), IsMulCommutative H ∧ Nat.card H = a000792 n := by
  induction n using a000792.induct with
  | case1 => exact ⟨⊥, isMulCommutative_bot, Subgroup.card_bot⟩
  | case2 => exact ⟨⊥, isMulCommutative_bot, Subgroup.card_bot⟩
  | case3 =>
    refine ⟨Subgroup.zpowers (finRotate 2), inferInstance, ?_⟩
    rw [Nat.card_zpowers, (isCycle_finRotate (n := 0)).orderOf,
      support_finRotate (n := 0), Finset.card_univ, Fintype.card_fin]
    rfl
  | case4 =>
    refine ⟨Subgroup.zpowers (finRotate 3), inferInstance, ?_⟩
    rw [Nat.card_zpowers, (isCycle_finRotate (n := 1)).orderOf,
      support_finRotate (n := 1), Finset.card_univ, Fintype.card_fin]
    rfl
  | case5 =>
    refine ⟨Subgroup.zpowers (finRotate 4), inferInstance, ?_⟩
    rw [Nat.card_zpowers, (isCycle_finRotate (n := 2)).orderOf,
      support_finRotate (n := 2), Finset.card_univ, Fintype.card_fin]
    rfl
  | case6 n ih =>
    obtain ⟨H, hH, hcard⟩ := ih
    haveI := hH
    have hCcard : Nat.card (Subgroup.zpowers (finRotate 3)) = 3 := by
      rw [Nat.card_zpowers, (isCycle_finRotate (n := 1)).orderOf,
        support_finRotate (n := 1), Finset.card_univ, Fintype.card_fin]
    haveI : IsMulCommutative (H.prod (Subgroup.zpowers (finRotate 3))) :=
      isMulCommutative_prod _ _ hH inferInstance
    set e : Perm (Fin (n + 2) ⊕ Fin 3) ≃* Perm (Fin (n + 5)) :=
      Equiv.permCongrHom finSumFinEquiv with hedef
    set Q : Subgroup (Perm (Fin (n + 2) ⊕ Fin 3)) :=
      (H.prod (Subgroup.zpowers (finRotate 3))).map
        (Equiv.Perm.sumCongrHom (Fin (n + 2)) (Fin 3)) with hQdef
    refine ⟨Q.map e.toMonoidHom, inferInstance, ?_⟩
    have h1 : Nat.card (Q.map e.toMonoidHom) = Nat.card Q :=
      (Nat.card_congr (Subgroup.equivMapOfInjective Q e.toMonoidHom
        e.injective).toEquiv).symm
    have h2 : Nat.card Q = Nat.card (H.prod (Subgroup.zpowers (finRotate 3))) := by
      rw [hQdef]
      exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _
        Equiv.Perm.sumCongrHom_injective).toEquiv).symm
    have h3 : Nat.card (H.prod (Subgroup.zpowers (finRotate 3)))
        = Nat.card H * Nat.card (Subgroup.zpowers (finRotate 3)) := by
      rw [Nat.card_congr (Subgroup.prodEquiv H _).toEquiv, Nat.card_prod]
    have hrec : a000792 (n + 5) = 3 * a000792 (n + 2) := by
      have h := a000792_add_three (n := n + 2) (by omega)
      rwa [show n + 2 + 3 = n + 5 from rfl] at h
    rw [h1, h2, h3, hcard, hCcard, hrec]
    ring

/-! ### The structure theorem for symmetric groups -/

/-- **Structure theorem (Bercov–Moser 1965).** The largest order of an
abelian subgroup of the permutation group of a finite type on `n` points is
`a000792 n`. -/
theorem maxAbelianOrder_perm {α : Type*} [Finite α] :
    maxAbelianOrder (Perm α) = a000792 (Nat.card α) := by
  refine le_antisymm (maxAbelianOrder_le fun H hH => card_le_a000792_of_isMulCommutative H hH) ?_
  cases nonempty_fintype α
  obtain ⟨H, hH, hcard⟩ := exists_isMulCommutative_card_a000792 (Fintype.card α)
  haveI := hH
  set e : Perm (Fin (Fintype.card α)) ≃* Perm α :=
    Equiv.permCongrHom (Fintype.equivFin α).symm with he
  have hmap : Nat.card (H.map e.toMonoidHom) = a000792 (Fintype.card α) := by
    rw [← hcard]
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective H e.toMonoidHom e.injective).toEquiv).symm
  have hle := le_maxAbelianOrder (H.map e.toMonoidHom) inferInstance
  rw [hmap] at hle
  rwa [Nat.card_eq_fintype_card]

/-- The structure theorem for `S_n` on `Fin n`. -/
theorem maxAbelianOrder_perm_fin (n : ℕ) :
    maxAbelianOrder (Perm (Fin n)) = a000792 n := by
  have h := maxAbelianOrder_perm (α := Fin n)
  rwa [Nat.card_fin] at h

/-- The clique number of the commuting graph of `S_n` on all `n!` vertices. -/
theorem cliqueNum_commutingGraph_perm_fin (n : ℕ) :
    (commutingGraph (Perm (Fin n))).cliqueNum = a000792 n := by
  rw [cliqueNum_commutingGraph, maxAbelianOrder_perm_fin]

/-! ### OEIS A135908 -/

/-- OEIS A135908: the clique number of the commuting graph of `S_n` with the
*nonidentity* permutations as vertices (one of three literature conventions;
see the module header — the companion A135909's value 2 at `n = 3` is the
data point fitting `G ∖ {1}`).  Deviation disclosed: the entry sets a(2) = 0 "by
convention (or should it be 1?)"; this definition takes the graph-honest
value `a135908 2 = 1`.  All other listed terms agree. -/
noncomputable def a135908 (n : ℕ) : ℕ :=
  ((commutingGraph (Perm (Fin n))).induce {σ : Perm (Fin n) | σ ≠ 1}).cliqueNum

/-- The clique number of the nonidentity commuting graph of `S_n` is
`a000792 n - 1`, in subtraction-free form. -/
theorem a135908_add_one (n : ℕ) : a135908 n + 1 = a000792 n := by
  rw [a135908, cliqueNum_induce_ne_one_add_one, cliqueNum_commutingGraph_perm_fin]

/-- **Barker's recurrence for A135908** (conjectured 2013-07-26, proved here),
in the range `5 < n` — valid for this file's `a135908` (value 1 at `n = 2`);
on the entry's published terms (a(2) = 0) the recurrence first holds at
`n = 7`, so only the claimed range `7 < n` transfers to the published data. -/
theorem a135908_recurrence {n : ℕ} (hn : 5 < n) :
    (a135908 n : ℤ) =
      a135908 (n - 1) + 3 * a135908 (n - 3) - 3 * a135908 (n - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have e : ∀ k : ℕ, (a135908 k : ℤ) = (a000792 k : ℤ) - 1 := fun k => by
    have h := a135908_add_one k
    push_cast [← h]
    ring
  have h1 : m + 6 - 1 = m + 5 := by omega
  have h3 : m + 6 - 3 = m + 3 := by omega
  have h4 : m + 6 - 4 = m + 2 := by omega
  rw [h1, h3, h4, e, e, e, e, a000792_barker_shift]
  ring

/-- Barker's recurrence for A135908 in exactly the range `7 < n` claimed in
the OEIS entry. -/
theorem a135908_recurrence_oeis {n : ℕ} (hn : 7 < n) :
    (a135908 n : ℤ) =
      a135908 (n - 1) + 3 * a135908 (n - 3) - 3 * a135908 (n - 4) :=
  a135908_recurrence (by omega)

/-- Ground truth: terms of A135908 for `3 ≤ n ≤ 12` against the entry data
`2, 3, 5, 8, 11, 17, 26, 35, 53, 80`. -/
example :
    (List.range 10).map (fun i => a135908 (i + 3) + 1) =
      [3, 4, 6, 9, 12, 18, 27, 36, 54, 81] := by
  simp only [a135908_add_one]
  decide

/-! ### OEIS A135909: alternating groups -/

/-- The conjectured largest abelian subgroup order of the alternating group
`A_n`: `1, 1, 1, 3, 4, 5, 9, 12, 16` for `n ≤ 8`, then `gAlt (n+3) = 3 * gAlt n`.
Verified by exhaustive enumeration of abelian subgroup orders for `n ≤ 8`.
At `n = 8`: 16 is witnessed by an elementary abelian `V₄ × V₄` on `4 + 4`
points; anything larger is ≤ 18 by the `S_8` bound `a000792 8 = 18`
(`maxAbelianOrder_alternating_le`); 17 is excluded by Lagrange
(`17 ∤ |A_8|`); and both abelian order-18 shapes fail — `C₁₈` needs an
element of order 9, absent in `S_8`, and `C₃ × C₃ × C₂` needs an even
involution centralizing a `C₃ × C₃` on 8 points, whose only candidate is an
odd transposition.  The full structure theorem is open in this file:
theorems below that need it take `AltStructure` as a hypothesis. -/
def gAlt : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 9
  | 7 => 12
  | 8 => 16
  | n + 9 => 3 * gAlt (n + 6)

/-- Ground truth: `gAlt n - 1` matches the OEIS A135909 data
`0,0,0,2,3,4,8,11,15,26,35,47,80,107,143` at every listed offset. -/
example : (List.range 15).map gAlt = [1, 1, 1, 3, 4, 5, 9, 12, 16, 27, 36, 48, 81, 108, 144] := by
  rfl

/-- The three-step recursion of `gAlt` in its natural range. -/
theorem gAlt_add_three {n : ℕ} (hn : 6 ≤ n) : gAlt (n + 3) = 3 * gAlt n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rfl

/-- OEIS A135909: the clique number of the commuting graph of `A_n` on the
nonidentity elements.  Unlike `a135908`, this matches every listed term of
the entry, including the `n ≤ 2` boundary. -/
noncomputable def a135909 (n : ℕ) : ℕ :=
  ((commutingGraph ↥(alternatingGroup (Fin n))).induce
    {σ : ↥(alternatingGroup (Fin n)) | σ ≠ 1}).cliqueNum

/-- The A135909 bridge: `a135909 n + 1` is the largest abelian subgroup order
of the alternating group.  Unconditional. -/
theorem a135909_add_one (n : ℕ) :
    a135909 n + 1 = maxAbelianOrder ↥(alternatingGroup (Fin n)) := by
  rw [a135909, cliqueNum_induce_ne_one_add_one, cliqueNum_commutingGraph]

/-- Unconditional upper bound: abelian subgroups of `A_n` obey the symmetric
group bound `a000792 n`. -/
theorem maxAbelianOrder_alternating_le (n : ℕ) :
    maxAbelianOrder ↥(alternatingGroup (Fin n)) ≤ a000792 n := by
  have h := maxAbelianOrder_subgroup_le (alternatingGroup (Fin n))
  rwa [maxAbelianOrder_perm_fin] at h

/-- The open alternating-group structure statement: the largest abelian
subgroup order of `A_n` is `gAlt n`.  Known for `n = 3` in this file
(`altStructure_three` below) and exhaustively verified for `n ≤ 8` by
computer search.  No published determination of the general `A_n` case was
found (the Bercov–Moser paper cited for `S_n` does not treat alternating
groups); its Lean proof is left open. -/
def AltStructure : Prop :=
  ∀ n : ℕ, maxAbelianOrder ↥(alternatingGroup (Fin n)) = gAlt n

/-- Partial satisfiability witness for `AltStructure`: the `n = 3` instance.
`A_3 ≅ C_3` is cyclic of prime order 3, hence abelian, so its largest abelian
subgroup is the whole group and `maxAbelianOrder A_3 = 3 = gAlt 3`. -/
theorem altStructure_three : maxAbelianOrder ↥(alternatingGroup (Fin 3)) = gAlt 3 := by
  have hcard : Nat.card ↥(alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card]; decide
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : IsCyclic ↥(alternatingGroup (Fin 3)) := isCyclic_of_prime_card hcard
  haveI : IsMulCommutative ↥(alternatingGroup (Fin 3)) :=
    ⟨⟨(IsCyclic.commGroup (α := ↥(alternatingGroup (Fin 3)))).mul_comm⟩⟩
  rw [maxAbelianOrder_eq_card inferInstance, hcard]
  rfl

/-- Ground truth for `a135909`: the clique number of the commuting graph of
`A_3` on nonidentity elements is 2 (the two 3-cycles commute). -/
example : a135909 3 = 2 := by
  have h := a135909_add_one 3
  rw [altStructure_three, show gAlt 3 = 3 from rfl] at h
  omega

/-- **Barker's recurrence for A135909**, conditional on the alternating
structure statement, in the range `9 < n` — the largest range in which it is
true at all (see `a135909_claimed_range_false`). -/
theorem a135909_recurrence (h : AltStructure) {n : ℕ} (hn : 9 < n) :
    (a135909 n : ℤ) =
      a135909 (n - 1) + 3 * a135909 (n - 3) - 3 * a135909 (n - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
  have e : ∀ k : ℕ, (a135909 k : ℤ) = (gAlt k : ℤ) - 1 := fun k => by
    have hk := a135909_add_one k
    rw [h k] at hk
    push_cast [← hk]
    ring
  have h1 : m + 10 - 1 = m + 9 := by omega
  have h3 : m + 10 - 3 = m + 7 := by omega
  have h4 : m + 10 - 4 = m + 6 := by omega
  have g1 : gAlt (m + 7 + 3) = 3 * gAlt (m + 7) := gAlt_add_three (by omega)
  have g2 : gAlt (m + 6 + 3) = 3 * gAlt (m + 6) := gAlt_add_three (by omega)
  have e1 : m + 7 + 3 = m + 10 := by omega
  have e2 : m + 6 + 3 = m + 9 := by omega
  rw [e1] at g1
  rw [e2] at g2
  rw [h1, h3, h4, e, e, e, e]
  push_cast [g1, g2]
  ring

/-- **Refutation of the claimed range.** The OEIS entry claims the recurrence
for all `n > 6`; conditional on the alternating structure statement this is
false — it already fails at `n = 8`, where the recurrence predicts 14 but
`a135909 8 = 15`. -/
theorem a135909_claimed_range_false (h : AltStructure) :
    ¬ ∀ n : ℕ, 6 < n →
      (a135909 n : ℤ) =
        a135909 (n - 1) + 3 * a135909 (n - 3) - 3 * a135909 (n - 4) := by
  intro hall
  have h8 := hall 8 (by omega)
  have e : ∀ k : ℕ, (a135909 k : ℤ) = (gAlt k : ℤ) - 1 := fun k => by
    have hk := a135909_add_one k
    rw [h k] at hk
    push_cast [← hk]
    ring
  rw [show (8 : ℕ) - 1 = 7 from rfl, show (8 : ℕ) - 3 = 5 from rfl,
    show (8 : ℕ) - 4 = 4 from rfl, e, e, e, e] at h8
  norm_num [show gAlt 8 = 16 from rfl, show gAlt 7 = 12 from rfl,
    show gAlt 5 = 5 from rfl, show gAlt 4 = 4 from rfl] at h8

end CommutingClique
