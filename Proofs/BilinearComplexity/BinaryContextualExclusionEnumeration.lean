import BilinearComplexity.BinaryAmbientContextFiniteExclusion

/-!
# Finite exclusion enumeration completeness

This module proves two reusable facts about the finite raw checker. First, the
explicit `splits5` table contains every two-versus-three partition of a
five-element duplicate-free list. Second, the `thirdFlip4ABC` disjunction is
invariant under every permutation of its four term-and-occupancy arguments.
The latter result is lifted to a fixed coordinate orientation and to the full
six-orientation search.

The proofs are structural: the split proof classifies the ten possible
positions of the selected pair, while permutation invariance follows from the
three adjacent transpositions rather than from 24 individual cases.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace BilinearComplexity.BinaryContextualExclusionEnumeration

open BinaryAmbientContextFiniteExclusion

/-- A four-argument function invariant under adjacent transpositions has the
same value on permutation-equivalent four-element lists. -/
theorem fourary_eq_of_perm {α β : Type*} (F : α → α → α → α → β)
    (h12 : ∀ a b c d, F a b c d = F b a c d)
    (h23 : ∀ a b c d, F a b c d = F a c b d)
    (h34 : ∀ a b c d, F a b c d = F a b d c)
    {a b c d a' b' c' d' : α}
    (hperm : [a, b, c, d].Perm [a', b', c', d']) :
    F a b c d = F a' b' c' d' := by
  let eval : List α → Option β := fun values =>
    match values with
    | [w, x, y, z] => some (F w x y z)
    | _ => none
  have hswap (pre suffix : List α) (x y : α) :
      eval (pre ++ y :: x :: suffix) =
        eval (pre ++ x :: y :: suffix) := by
    cases pre with
    | nil =>
        cases suffix with
        | nil => rfl
        | cons q suffix =>
            cases suffix with
            | nil => rfl
            | cons r suffix =>
                cases suffix with
                | nil => simpa [eval] using (h12 x y q r).symm
                | cons s suffix => simp [eval]
    | cons p pre =>
        cases pre with
        | nil =>
            cases suffix with
            | nil => rfl
            | cons r suffix =>
                cases suffix with
                | nil => simpa [eval] using (h23 p x y r).symm
                | cons s suffix => simp [eval]
        | cons q pre =>
            cases pre with
            | nil =>
                cases suffix with
                | nil => simpa [eval] using (h34 p q x y).symm
                | cons s suffix => simp [eval]
            | cons r pre =>
                cases pre with
                | nil => rfl
                | cons s pre => cases pre <;> rfl
  have hcontext {l₁ l₂ : List α} (h : l₁.Perm l₂) :
      ∀ pre : List α, eval (pre ++ l₁) = eval (pre ++ l₂) := by
    induction h with
    | nil => intro pre; rfl
    | cons x h ih =>
        intro pre
        simpa [List.append_assoc] using ih (pre ++ [x])
    | swap x y l =>
        intro pre
        exact hswap pre l x y
    | trans h₁ h₂ ih₁ ih₂ =>
        intro pre
        exact (ih₁ pre).trans (ih₂ pre)
  have heval := hcontext hperm []
  simpa [eval] using heval

/-- Swapping the two displayed target terms does not change an ordered raw
third-flip pair test. -/
theorem thirdFlipPairABC_swap_targets (osl osr ox oy : Bool)
    (sl sr x y : TermCode) :
    thirdFlipPairABC osl osr ox oy sl sr x y =
      thirdFlipPairABC osl osr oy ox sl sr y x := by
  simp only [thirdFlipPairABC]
  ac_rfl

/-- The raw four-term ABC flip enumeration is invariant under permutation of
its four term-and-occupancy arguments. -/
theorem thirdFlip4ABC_eq_of_perm (occupied : TermCode → Bool)
    {a b c d a' b' c' d' : TermCode}
    (hperm : [a, b, c, d].Perm [a', b', c', d']) :
    thirdFlip4ABC (occupied a) (occupied b) (occupied c) (occupied d)
        a b c d =
      thirdFlip4ABC (occupied a') (occupied b') (occupied c') (occupied d')
        a' b' c' d' := by
  let F := fun w x y z =>
    thirdFlip4ABC (occupied w) (occupied x) (occupied y) (occupied z) w x y z
  apply fourary_eq_of_perm F
  · intro w x y z
    simp only [F, thirdFlip4ABC, thirdFlipPairABC_swap_targets]
    ac_rfl
  · intro w x y z
    simp only [F, thirdFlip4ABC, thirdFlipPairABC_swap_targets]
    ac_rfl
  · intro w x y z
    simp only [F, thirdFlip4ABC, thirdFlipPairABC_swap_targets]
    ac_rfl
  · exact hperm

/-- An ordered raw ABC third-flip witness with complementary two-versus-two
occupancy is found by `thirdFlip4ABC` in every permutation of its support. -/
theorem thirdFlip4ABC_of_perm (occupied : TermCode → Bool)
    {sl sr tl tr a b c d : TermCode}
    (hwitness : thirdFlipWitnessABC sl sr tl tr = true)
    (hoccupancy :
      ((occupied sl && occupied sr && !occupied tl && !occupied tr) ||
        (!occupied sl && !occupied sr && occupied tl && occupied tr)) = true)
    (hperm : [sl, sr, tl, tr].Perm [a, b, c, d]) :
    thirdFlip4ABC (occupied a) (occupied b) (occupied c) (occupied d)
      a b c d = true := by
  rw [← thirdFlip4ABC_eq_of_perm occupied hperm]
  simp [thirdFlip4ABC, thirdFlipPairABC, hoccupancy, hwitness]

/-- The source-present and target-absent occupancy form of
`thirdFlip4ABC_of_perm`. -/
theorem thirdFlip4ABC_of_perm_source_occupied (occupied : TermCode → Bool)
    {sl sr tl tr a b c d : TermCode}
    (hwitness : thirdFlipWitnessABC sl sr tl tr = true)
    (hsl : occupied sl = true) (hsr : occupied sr = true)
    (htl : occupied tl = false) (htr : occupied tr = false)
    (hperm : [sl, sr, tl, tr].Perm [a, b, c, d]) :
    thirdFlip4ABC (occupied a) (occupied b) (occupied c) (occupied d)
      a b c d = true := by
  apply thirdFlip4ABC_of_perm occupied hwitness
  · simp [hsl, hsr, htl, htr]
  · exact hperm

/-- The source-absent and target-present occupancy form of
`thirdFlip4ABC_of_perm`. -/
theorem thirdFlip4ABC_of_perm_target_occupied (occupied : TermCode → Bool)
    {sl sr tl tr a b c d : TermCode}
    (hwitness : thirdFlipWitnessABC sl sr tl tr = true)
    (hsl : occupied sl = false) (hsr : occupied sr = false)
    (htl : occupied tl = true) (htr : occupied tr = true)
    (hperm : [sl, sr, tl, tr].Perm [a, b, c, d]) :
    thirdFlip4ABC (occupied a) (occupied b) (occupied c) (occupied d)
      a b c d = true := by
  apply thirdFlip4ABC_of_perm occupied hwitness
  · simp [hsl, hsr, htl, htr]
  · exact hperm

/-- One successful orientation is sufficient for the six-orientation raw
third-flip search. -/
theorem thirdFlip4_of_orientation (o : Scheme.Action.Orientation)
    (occupied : TermCode → Bool) (a b c d : TermCode)
    (hsuccess : thirdFlip4Orientation o occupied a b c d = true) :
    thirdFlip4 occupied a b c d = true := by
  cases o <;> simp [thirdFlip4, hsuccess]

/-- A fixed oriented raw four-term test is invariant under permutation of its
four support terms. -/
theorem thirdFlip4Orientation_eq_of_perm (o : Scheme.Action.Orientation)
    (occupied : TermCode → Bool) {a b c d a' b' c' d' : TermCode}
    (hperm : [a, b, c, d].Perm [a', b', c', d']) :
    thirdFlip4Orientation o occupied a b c d =
      thirdFlip4Orientation o occupied a' b' c' d' := by
  let F := fun w x y z => thirdFlip4Orientation o occupied w x y z
  apply fourary_eq_of_perm F
  · intro w x y z
    simp only [F, thirdFlip4Orientation, thirdFlip4ABC,
      thirdFlipPairABC_swap_targets]
    ac_rfl
  · intro w x y z
    simp only [F, thirdFlip4Orientation, thirdFlip4ABC,
      thirdFlipPairABC_swap_targets]
    ac_rfl
  · intro w x y z
    simp only [F, thirdFlip4Orientation, thirdFlip4ABC,
      thirdFlipPairABC_swap_targets]
    ac_rfl
  · exact hperm

/-- An ordered witness in one coordinate orientation is found in every
permutation of its four raw support terms. -/
theorem thirdFlip4Orientation_of_perm (o : Scheme.Action.Orientation)
    (occupied : TermCode → Bool) {sl sr tl tr a b c d : TermCode}
    (hwitness : thirdFlipWitnessABC (inverseCode o sl) (inverseCode o sr)
      (inverseCode o tl) (inverseCode o tr) = true)
    (hoccupancy :
      ((occupied sl && occupied sr && !occupied tl && !occupied tr) ||
        (!occupied sl && !occupied sr && occupied tl && occupied tr)) = true)
    (hperm : [sl, sr, tl, tr].Perm [a, b, c, d]) :
    thirdFlip4Orientation o occupied a b c d = true := by
  rw [← thirdFlip4Orientation_eq_of_perm o occupied hperm]
  simp [thirdFlip4Orientation, thirdFlip4ABC, thirdFlipPairABC,
    hoccupancy, hwitness]

/-- An oriented ordered witness with complementary occupancy is found by the
full six-orientation raw four-term search in every support permutation. -/
theorem thirdFlip4_of_perm (o : Scheme.Action.Orientation)
    (occupied : TermCode → Bool) {sl sr tl tr a b c d : TermCode}
    (hwitness : thirdFlipWitnessABC (inverseCode o sl) (inverseCode o sr)
      (inverseCode o tl) (inverseCode o tr) = true)
    (hoccupancy :
      ((occupied sl && occupied sr && !occupied tl && !occupied tr) ||
        (!occupied sl && !occupied sr && occupied tl && occupied tr)) = true)
    (hperm : [sl, sr, tl, tr].Perm [a, b, c, d]) :
    thirdFlip4 occupied a b c d = true := by
  apply thirdFlip4_of_orientation o occupied a b c d
  exact thirdFlip4Orientation_of_perm o occupied hwitness hoccupancy hperm

/-- The explicit ten-way split enumeration contains the two-element filter
of a duplicate-free five-element list and its complementary filter. -/
theorem exists_mem_splits5_filters_of_card_eq_two {α : Type*} [DecidableEq α]
    (Z : List α) (hZLength : Z.length = 5) (hZNodup : Z.Nodup)
    (S : Finset α) (hSCard : S.card = 2) (hSSubset : S ⊆ Z.toFinset) :
    ∃ x y u v w,
      ((x, y), (u, v, w)) ∈ splits5 Z ∧
      [x, y] = Z.filter (· ∈ S) ∧
      [u, v, w] = Z.filter (· ∉ S) := by
  obtain ⟨a, Z, rfl⟩ := List.exists_of_length_succ Z hZLength
  have hZLength₁ : Z.length = 4 := by simpa using hZLength
  obtain ⟨b, Z, rfl⟩ := List.exists_of_length_succ Z hZLength₁
  have hZLength₂ : Z.length = 3 := by simpa using hZLength₁
  obtain ⟨c, Z, rfl⟩ := List.exists_of_length_succ Z hZLength₂
  have hZLength₃ : Z.length = 2 := by simpa using hZLength₂
  obtain ⟨d, Z, rfl⟩ := List.exists_of_length_succ Z hZLength₃
  have hZLength₄ : Z.length = 1 := by simpa using hZLength₃
  obtain ⟨e, Z, rfl⟩ := List.exists_of_length_succ Z hZLength₄
  have hZLength₅ : Z.length = 0 := by simpa using hZLength₄
  have hZNil : Z = [] := List.eq_nil_of_length_eq_zero hZLength₅
  subst Z
  have hSCases :
      S = {a, b} ∨ S = {a, c} ∨ S = {a, d} ∨ S = {a, e} ∨
      S = {b, c} ∨ S = {b, d} ∨ S = {b, e} ∨
      S = {c, d} ∨ S = {c, e} ∨ S = {d, e} := by
    rcases Finset.card_eq_two.mp hSCard with ⟨x, y, hxy, hS⟩
    have hx : x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e := by
      have hxS : x ∈ S := hS.symm ▸ Finset.mem_insert_self x {y}
      simpa using hSSubset hxS
    have hy : y = a ∨ y = b ∨ y = c ∨ y = d ∨ y = e := by
      have hyS : y ∈ S := hS.symm ▸
        Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
      simpa using hSSubset hyS
    rcases hx with rfl | rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl | rfl <;>
      simp_all [Finset.pair_comm]
  rcases hSCases with hS | hS | hS | hS | hS | hS | hS | hS | hS | hS
  · subst S
    exact ⟨a, b, c, d, e, by simp_all [splits5, ne_comm]⟩
  · subst S
    exact ⟨a, c, b, d, e, by simp_all [splits5, ne_comm]⟩
  · subst S
    exact ⟨a, d, b, c, e, by simp_all [splits5, ne_comm]⟩
  · subst S
    exact ⟨a, e, b, c, d, by simp_all [splits5, ne_comm]⟩
  · subst S
    exact ⟨b, c, a, d, e, by simp_all [splits5, ne_comm]⟩
  · subst S
    exact ⟨b, d, a, c, e, by simp_all [splits5, ne_comm]⟩
  · subst S
    exact ⟨b, e, a, c, d, by simp_all [splits5, ne_comm]⟩
  · subst S
    exact ⟨c, d, a, b, e, by simp_all [splits5, ne_comm]⟩
  · subst S
    exact ⟨c, e, a, b, d, by simp_all [splits5, ne_comm]⟩
  · subst S
    exact ⟨d, e, a, b, c, by simp_all [splits5, ne_comm]⟩

/-- Every two-element subset of a duplicate-free five-element list occurs in
`splits5`, with the remaining triple, concatenation permutation, and
pairwise-distinctness exposed to downstream semantic proofs. -/
theorem exists_mem_splits5_of_card_eq_two {α : Type*} [DecidableEq α]
    (Z : List α) (hZLength : Z.length = 5) (hZNodup : Z.Nodup)
    (S : Finset α) (hSCard : S.card = 2) (hSSubset : S ⊆ Z.toFinset) :
    ∃ x y u v w,
      ((x, y), (u, v, w)) ∈ splits5 Z ∧
      ({x, y} : Finset α) = S ∧
      ({u, v, w} : Finset α) = Z.toFinset \ S ∧
      [x, y, u, v, w].Perm Z ∧
      [x, y, u, v, w].Nodup := by
  obtain ⟨x, y, u, v, w, hmem, hpairFilter, htripleFilter⟩ :=
    exists_mem_splits5_filters_of_card_eq_two Z hZLength hZNodup
      S hSCard hSSubset
  have hpair : ({x, y} : Finset α) = S := by
    ext q
    calc
      q ∈ ({x, y} : Finset α) ↔ q ∈ [x, y] := by simp
      _ ↔ q ∈ Z.filter (· ∈ S) := by rw [hpairFilter]
      _ ↔ q ∈ Z ∧ q ∈ S := by simp
      _ ↔ q ∈ S := by
        constructor
        · exact And.right
        · intro hqS
          exact ⟨List.mem_toFinset.mp (hSSubset hqS), hqS⟩
  have htriple : ({u, v, w} : Finset α) = Z.toFinset \ S := by
    ext q
    calc
      q ∈ ({u, v, w} : Finset α) ↔ q ∈ [u, v, w] := by simp
      _ ↔ q ∈ Z.filter (· ∉ S) := by rw [htripleFilter]
      _ ↔ q ∈ Z ∧ q ∉ S := by simp
      _ ↔ q ∈ Z.toFinset \ S := by simp
  have hperm : [x, y, u, v, w].Perm Z := by
    rw [show [x, y, u, v, w] = [x, y] ++ [u, v, w] by rfl,
      hpairFilter, htripleFilter]
    simpa using List.filter_append_perm (fun q => q ∈ S) Z
  have hnodup : [x, y, u, v, w].Nodup :=
    hperm.nodup_iff.mpr hZNodup
  exact ⟨x, y, u, v, w, hmem, hpair, htriple, hperm, hnodup⟩

example : ((0, 2), (1, 3, 4)) ∈ splits5 [0, 1, 2, 3, 4] := by
  decide

example :
    let t : TermCode :=
      ⟨[true, true, false], [true, false], [true]⟩
    let u : TermCode :=
      ⟨[false, false, true], [false, true], [true]⟩
    let v : TermCode :=
      ⟨[true, true, true], [true, false], [true]⟩
    let w : TermCode :=
      ⟨[false, false, true], [true, true], [true]⟩
    let occupied := fun q => q == t || q == u
    thirdFlip4ABC (occupied v) (occupied t) (occupied w) (occupied u)
      v t w u = true := by
  decide

#check @fourary_eq_of_perm
#check @thirdFlip4ABC_eq_of_perm
#check @thirdFlip4ABC_of_perm
#check @thirdFlip4Orientation_of_perm
#check @thirdFlip4_of_perm
#check @exists_mem_splits5_filters_of_card_eq_two
#check @exists_mem_splits5_of_card_eq_two

#print axioms fourary_eq_of_perm
#print axioms thirdFlip4ABC_of_perm
#print axioms thirdFlip4_of_perm
#print axioms exists_mem_splits5_of_card_eq_two

end BilinearComplexity.BinaryContextualExclusionEnumeration
