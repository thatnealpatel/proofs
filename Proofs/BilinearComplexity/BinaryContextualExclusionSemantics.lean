import BilinearComplexity.BinaryAmbientContextFiniteExclusion
import BilinearComplexity.BinaryAmbientContextOptimality

/-!
# Semantic ingredients for normalized contextual exclusions

This module supplies a partial bridge from intrinsic all-mode moves on normalized
coordinate carriers to the raw Boolean checker in
`BinaryAmbientContextFiniteExclusion`: injective encodings, line and Flip equation
compatibility, native three-support line reflection, and production-row encoding
identities. Native four-support occupancy reflection and the implication from a
native contextual two-edge path to the complete checker are not yet established
here. Ambient coordinate extraction and orbit transport are separate layers.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

namespace BilinearComplexity.BinaryContextualExclusionSemantics

open scoped symmDiff
open BinaryCircuit
open BinaryAmbientCarrier
open BinaryAmbientMoves
open BinaryAmbientMoveSupport
open BinaryAmbientContextOptimality
open NormalizedBinaryCarrier
open NormalizedBinaryFiveCircuitRows
open Scheme.Action

namespace Raw

open BinaryAmbientContextFiniteExclusion

/-- Encode a scalar of `F2` as its Boolean coordinate bit. -/
def f2Code (x : F2) : Bool := decide (x = 1)

example : f2Code 0 = false := by decide
example : f2Code 1 = true := by decide

/-- Boolean encoding of `F2` is injective. -/
theorem f2Code_injective : Function.Injective f2Code := by
  intro x y hxy
  have hrecover (z : F2) : (if f2Code z then 1 else 0) = z := by
    fin_cases z <;> rfl
  rw [← hrecover x, ← hrecover y, hxy]

/-- Boolean encoding carries addition in `F2` to XOR. -/
theorem f2Code_add (x y : F2) :
    f2Code (x + y) = xor (f2Code x) (f2Code y) := by
  fin_cases x <;> fin_cases y <;> decide

/-- Boolean encoding carries subtraction in `F2` to XOR. -/
theorem f2Code_sub (x y : F2) :
    f2Code (x - y) = xor (f2Code x) (f2Code y) := by
  fin_cases x <;> fin_cases y <;> decide

/-- Encode a normalized coordinate vector as a dimension-preserving bit list. -/
def encodeVector {d : ℕ} (x : CoordinateVector d) :
    BinaryAmbientContextFiniteExclusion.VectorCode :=
  List.ofFn (fun i => f2Code (x i))

example : encodeVector (fun _ : Fin 0 => (0 : F2)) = [] := rfl
example : encodeVector (fun _ : Fin 1 => (1 : F2)) = [true] := by decide

/-- Coordinate-vector encoding is injective. -/
theorem encodeVector_injective {d : ℕ} : Function.Injective (@encodeVector d) := by
  intro x y hxy
  have hbits : (fun i => f2Code (x i)) = (fun i => f2Code (y i)) :=
    List.ofFn_injective hxy
  funext i
  exact f2Code_injective (congrFun hbits i)

/-- Coordinate-vector encoding carries addition to the checker's pointwise
XOR on equal-dimensional lists. -/
theorem encodeVector_add {d : ℕ} (x y : CoordinateVector d) :
    encodeVector (x + y) =
      BinaryAmbientContextFiniteExclusion.vectorAdd (encodeVector x) (encodeVector y) := by
  apply List.ext_get
  · simp [encodeVector, BinaryAmbientContextFiniteExclusion.vectorAdd]
  · intro n hn hn'
    simp [encodeVector, BinaryAmbientContextFiniteExclusion.vectorAdd]
    exact f2Code_add _ _

/-- Coordinate-vector encoding carries subtraction to the checker's pointwise
XOR on equal-dimensional lists. -/
theorem encodeVector_sub {d : ℕ} (x y : CoordinateVector d) :
    encodeVector (x - y) =
      BinaryAmbientContextFiniteExclusion.vectorAdd (encodeVector x) (encodeVector y) := by
  apply List.ext_get
  · simp [encodeVector, BinaryAmbientContextFiniteExclusion.vectorAdd]
  · intro n hn hn'
    simp [encodeVector, BinaryAmbientContextFiniteExclusion.vectorAdd]
    exact f2Code_sub _ _

/-- Encode one admissible normalized carrier term by encoding its three
underlying factor vectors. -/
def encodeTerm {p : Profile} (t : NormalizedBinaryCarrier.Carrier p) :
    BinaryAmbientContextFiniteExclusion.TermCode :=
  ⟨encodeVector t.1.1, encodeVector t.2.1.1, encodeVector t.2.2.1⟩

example :
    encodeTerm (carrierOfMasks profile222 1 1 1
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) =
      ⟨[true, false], [true, false], [true, false]⟩ := by decide

/-- Encoding normalized carrier terms is injective. -/
theorem encodeTerm_injective {p : Profile} : Function.Injective (@encodeTerm p) := by
  intro x y hxy
  rcases x with ⟨⟨x₁, hx₁⟩, ⟨⟨x₂, hx₂⟩, ⟨x₃, hx₃⟩⟩⟩
  rcases y with ⟨⟨y₁, hy₁⟩, ⟨⟨y₂, hy₂⟩, ⟨y₃, hy₃⟩⟩⟩
  simp only [encodeTerm, BinaryAmbientContextFiniteExclusion.TermCode.mk.injEq] at hxy
  have h₁ : x₁ = y₁ := encodeVector_injective hxy.1
  have h₂ : x₂ = y₂ := encodeVector_injective hxy.2.1
  have h₃ : x₃ = y₃ := encodeVector_injective hxy.2.2
  subst y₁
  subst y₂
  subst y₃
  rfl

/-- Pulling a normalized term back through an orientation commutes with raw
encoding. -/
theorem encodeTerm_inversePermuteTerm {p : Profile} (o : Orientation)
    (t : NormalizedBinaryCarrier.Carrier p) :
    encodeTerm (NormalizedBinaryAllModeMoveData.inversePermuteTerm o t) =
      BinaryAmbientContextFiniteExclusion.inverseCode o (encodeTerm t) := by
  cases o <;> rcases p with ⟨a, b, c⟩ <;>
    rcases t with ⟨t₁, t₂, t₃⟩ <;> rfl

/-- Pushing a normalized term through an orientation commutes with raw
encoding. -/
theorem encodeTerm_permuteTerm {p : Profile} (o : Orientation)
    (t : NormalizedBinaryCarrier.Carrier p) :
    encodeTerm (NormalizedBinaryModePermutation.permuteTerm o t) =
      BinaryAmbientContextFiniteExclusion.forwardCode o (encodeTerm t) := by
  cases o <;> rcases p with ⟨a, b, c⟩ <;>
    rcases t with ⟨t₁, t₂, t₃⟩ <;> rfl

/-- Exact raw line-candidate reflection for three normalized terms in ABC
order. -/
theorem lineCandidateABC_encode {p : Profile}
    (x y t : NormalizedBinaryCarrier.Carrier p)
    (hfirst : t.1.1 = x.1.1 + y.1.1)
    (hsecondXY : x.2.1.1 = y.2.1.1)
    (hsecondT : t.2.1.1 = x.2.1.1)
    (hthirdXY : x.2.2.1 = y.2.2.1)
    (hthirdT : t.2.2.1 = x.2.2.1)
    (hfirstNe : x.1.1 ≠ y.1.1) :
    BinaryAmbientContextFiniteExclusion.lineCandidateABC
        (encodeTerm x) (encodeTerm y) = some (encodeTerm t) := by
  rw [BinaryAmbientContextFiniteExclusion.lineCandidateABC, if_pos]
  · apply congrArg some
    congr 1
    · exact (encodeVector_add x.1.1 y.1.1).symm.trans
        (congrArg encodeVector hfirst.symm)
    · exact congrArg encodeVector hsecondT.symm
    · exact congrArg encodeVector hthirdT.symm
  · refine ⟨congrArg encodeVector hsecondXY,
      congrArg encodeVector hthirdXY, ?_⟩
    exact fun h => hfirstNe (encodeVector_injective h)

/-- The equations carried by an intrinsic ABC Flip make the corresponding
ordered raw Flip witness evaluate to true. -/
theorem thirdFlipWitnessABC_encode {p : Profile} {D E : State p}
    {sl sr tl tr : NormalizedBinaryCarrier.Carrier p}
    (h : SourceThirdFlip sl sr tl tr D E) :
    BinaryAmbientContextFiniteExclusion.thirdFlipWitnessABC
      (encodeTerm sl) (encodeTerm sr) (encodeTerm tl) (encodeTerm tr) = true := by
  rcases h with ⟨hsl, hsr, hslr, htlFresh, htrFresh, htltr,
    hthird, htlFirst, htlSecond, htlThird, htrFirst, htrSecond,
    htrThird, hE⟩
  simp only [BinaryAmbientContextFiniteExclusion.thirdFlipWitnessABC,
    encodeTerm]
  rw [congrArg encodeVector hthird, congrArg encodeVector htlFirst,
    encodeVector_add, congrArg encodeVector htlSecond,
    congrArg encodeVector htlThird, congrArg encodeVector htrFirst,
    congrArg encodeVector htrSecond, encodeVector_sub,
    congrArg encodeVector htrThird]
  simp

end Raw

/-! ## Native three-support line reflection -/

private theorem term_eq_of_factors_eq {p : Profile}
    {x y : NormalizedBinaryCarrier.Carrier p}
    (h1 : x.1.1 = y.1.1) (h2 : x.2.1.1 = y.2.1.1)
    (h3 : x.2.2.1 = y.2.2.1) : x = y := by
  rcases x with ⟨⟨x1, hx1⟩, ⟨⟨x2, hx2⟩, ⟨x3, hx3⟩⟩⟩
  rcases y with ⟨⟨y1, hy1⟩, ⟨⟨y2, hy2⟩, ⟨y3, hy3⟩⟩⟩
  simp only at h1 h2 h3
  subst y1
  subst y2
  subst y3
  rfl

private theorem eq_add_of_add_add_eq_zero {d : ℕ} {a b c : CoordinateVector d}
    (h : a + b + c = 0) : c = a + b := by
  have hc : c + c = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (c i)
  calc
    c = 0 + c := (zero_add c).symm
    _ = (a + b + c) + c := congrArg (fun q => q + c) h.symm
    _ = a + b + (c + c) := add_assoc (a + b) c c
    _ = a + b + 0 := congrArg (fun q => a + b + q) hc
    _ = a + b := add_zero (a + b)

private theorem lineTriple_lineCandidateABC {p : Profile}
    {s l r x y t : NormalizedBinaryCarrier.Carrier p}
    (hsum : s.1.1 = l.1.1 + r.1.1)
    (hl2 : l.2.1.1 = s.2.1.1) (hr2 : r.2.1.1 = s.2.1.1)
    (hl3 : l.2.2.1 = s.2.2.1) (hr3 : r.2.2.1 = s.2.2.1)
    (hset : ({x, y, t} : Finset _) = {s, l, r})
    (hxy : x ≠ y) (hxt : x ≠ t) (hyt : y ≠ t) :
    BinaryAmbientContextFiniteExclusion.lineCandidateABC
      (Raw.encodeTerm x) (Raw.encodeTerm y) = some (Raw.encodeTerm t) := by
  have hxmem : x = s ∨ x = l ∨ x = r := by
    have hm : x ∈ ({s, l, r} : Finset _) := by rw [← hset]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hymem : y = s ∨ y = l ∨ y = r := by
    have hm : y ∈ ({s, l, r} : Finset _) := by rw [← hset]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have htmem : t = s ∨ t = l ∨ t = r := by
    have hm : t ∈ ({s, l, r} : Finset _) := by rw [← hset]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have htotal : s.1.1 + l.1.1 + r.1.1 = 0 := by
    funext i
    change (s.1.1 i + l.1.1 i) + r.1.1 i = 0
    rw [congrFun hsum i]
    simp only [Pi.add_apply]
    ring_nf
    have htwo : (2 : F2) = 0 := by decide
    simp only [htwo, mul_zero, add_zero]
  have hfirst : t.1.1 = x.1.1 + y.1.1 := by
    apply eq_add_of_add_add_eq_zero
    rcases hxmem with rfl | rfl | rfl <;>
      rcases hymem with rfl | rfl | rfl <;>
        rcases htmem with rfl | rfl | rfl
    all_goals try { exact False.elim (hxy rfl) }
    all_goals try { exact False.elim (hxt rfl) }
    all_goals try { exact False.elim (hyt rfl) }
    all_goals simpa only [add_comm, add_left_comm, add_assoc] using htotal
  have hx2 : x.2.1.1 = s.2.1.1 := by
    rcases hxmem with rfl | rfl | rfl
    · rfl
    · exact hl2
    · exact hr2
  have hy2 : y.2.1.1 = s.2.1.1 := by
    rcases hymem with rfl | rfl | rfl
    · rfl
    · exact hl2
    · exact hr2
  have ht2 : t.2.1.1 = s.2.1.1 := by
    rcases htmem with rfl | rfl | rfl
    · rfl
    · exact hl2
    · exact hr2
  have hx3 : x.2.2.1 = s.2.2.1 := by
    rcases hxmem with rfl | rfl | rfl
    · rfl
    · exact hl3
    · exact hr3
  have hy3 : y.2.2.1 = s.2.2.1 := by
    rcases hymem with rfl | rfl | rfl
    · rfl
    · exact hl3
    · exact hr3
  have ht3 : t.2.2.1 = s.2.2.1 := by
    rcases htmem with rfl | rfl | rfl
    · rfl
    · exact hl3
    · exact hr3
  have hsecondXY : x.2.1.1 = y.2.1.1 := hx2.trans hy2.symm
  have hsecondT : t.2.1.1 = x.2.1.1 := ht2.trans hx2.symm
  have hthirdXY : x.2.2.1 = y.2.2.1 := hx3.trans hy3.symm
  have hthirdT : t.2.2.1 = x.2.2.1 := ht3.trans hx3.symm
  apply Raw.lineCandidateABC_encode x y t hfirst hsecondXY hsecondT hthirdXY hthirdT
  intro hfirstEq
  exact hxy (term_eq_of_factors_eq hfirstEq hsecondXY hthirdXY)

private theorem generatedFirstSplit_lineCandidateABC {p : Profile}
    {D E : State p} {s l r x y t : NormalizedBinaryCarrier.Carrier p}
    (h : GeneratedFirstSplit s l r D E)
    (hset : ({x, y, t} : Finset _) = {s, l, r})
    (hxy : x ≠ y) (hxt : x ≠ t) (hyt : y ≠ t) :
    BinaryAmbientContextFiniteExclusion.lineCandidateABC
      (Raw.encodeTerm x) (Raw.encodeTerm y) = some (Raw.encodeTerm t) := by
  rcases h with ⟨hsD, hlr, hlFresh, hrFresh, hsum, hl2, hr2, hl3, hr3, hE⟩
  exact lineTriple_lineCandidateABC hsum hl2 hr2 hl3 hr3 hset hxy hxt hyt

private theorem directedReduction_lineCandidateABC {p : Profile}
    {D E : State p} {l r s x y t : NormalizedBinaryCarrier.Carrier p}
    (h : DirectedNarrowPairReduction l r s D E)
    (hset : ({x, y, t} : Finset _) = {l, r, s})
    (hxy : x ≠ y) (hxt : x ≠ t) (hyt : y ≠ t) :
    BinaryAmbientContextFiniteExclusion.lineCandidateABC
      (Raw.encodeTerm x) (Raw.encodeTerm y) = some (Raw.encodeTerm t) := by
  rcases h with ⟨hlD, hrD, hlr, hsFresh, hr2, hr3, hsum, hs2, hs3, hE⟩
  apply lineTriple_lineCandidateABC hsum
      hs2.symm (hr2.trans hs2.symm) hs3.symm (hr3.trans hs3.symm)
      ?_ hxy hxt hyt
  simpa only [Finset.ext_iff, Finset.mem_insert, Finset.mem_singleton,
    or_comm, or_left_comm, or_assoc] using hset

private theorem inverseCode_encode_permuteTerm {p : Profile} (o : Orientation)
    (t : NormalizedBinaryCarrier.Carrier p) :
    BinaryAmbientContextFiniteExclusion.inverseCode o
      (Raw.encodeTerm (NormalizedBinaryModePermutation.permuteTerm o t)) =
        Raw.encodeTerm t := by
  cases o <;> rcases p with ⟨a, b, c⟩ <;>
    rcases t with ⟨t1, t2, t3⟩ <;> rfl

private theorem lineCandidate_permute_encode {p : Profile} (o : Orientation)
    (x y t : NormalizedBinaryCarrier.Carrier p)
    (h : BinaryAmbientContextFiniteExclusion.lineCandidateABC
      (Raw.encodeTerm x) (Raw.encodeTerm y) = some (Raw.encodeTerm t)) :
    BinaryAmbientContextFiniteExclusion.lineCandidate o
      (Raw.encodeTerm (NormalizedBinaryModePermutation.permuteTerm o x))
      (Raw.encodeTerm (NormalizedBinaryModePermutation.permuteTerm o y)) =
        some (Raw.encodeTerm (NormalizedBinaryModePermutation.permuteTerm o t)) := by
  simp only [BinaryAmbientContextFiniteExclusion.lineCandidate]
  rw [inverseCode_encode_permuteTerm, inverseCode_encode_permuteTerm, h]
  exact congrArg some (Raw.encodeTerm_permuteTerm o t).symm

private theorem orientedLinePrimitiveCandidate_encode {p : Profile} (o : Orientation)
    {D E : State p}
    {S : Finset (NormalizedBinaryCarrier.Carrier
      (NormalizedBinaryModePermutation.permProfile o p))}
    {x y t : NormalizedBinaryCarrier.Carrier
      (NormalizedBinaryModePermutation.permProfile o p)}
    (hline :
      (∃ s l r, GeneratedFirstSplit s l r D E ∧ D ∆ E = {s, l, r}) ∨
        ∃ l r s, DirectedNarrowPairReduction l r s D E ∧ D ∆ E = {l, r, s})
    (himage : S = Finset.image
      (NormalizedBinaryModePermutation.permuteTerm o) (D ∆ E))
    (hset : S = {x, y, t})
    (hxy : x ≠ y) (hxt : x ≠ t) (hyt : y ≠ t) :
    BinaryAmbientContextFiniteExclusion.lineCandidate o
      (Raw.encodeTerm x) (Raw.encodeTerm y) = some (Raw.encodeTerm t) := by
  have hxS : x ∈ S := by rw [hset]; simp
  have hyS : y ∈ S := by rw [hset]; simp
  have htS : t ∈ S := by rw [hset]; simp
  rw [himage] at hxS hyS htS
  rcases Finset.mem_image.mp hxS with ⟨x₀, hx₀, hxeq⟩
  rcases Finset.mem_image.mp hyS with ⟨y₀, hy₀, hyeq⟩
  rcases Finset.mem_image.mp htS with ⟨t₀, ht₀, hteq⟩
  subst x
  subst y
  subst t
  have hxy₀ : x₀ ≠ y₀ := fun h => hxy (congrArg _ h)
  have hxt₀ : x₀ ≠ t₀ := fun h => hxt (congrArg _ h)
  have hyt₀ : y₀ ≠ t₀ := fun h => hyt (congrArg _ h)
  have hsmall : ({x₀, y₀, t₀} : Finset _).card = 3 := by
    simp [hxy₀, hxt₀, hyt₀]
  rcases hline with ⟨s, l, r, hprimitive, hsupport⟩ |
      ⟨l, r, s, hprimitive, hsupport⟩
  · have hsubset : ({x₀, y₀, t₀} : Finset _) ⊆ D ∆ E := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact hx₀
      · exact hy₀
      · exact ht₀
    have htriple : ({x₀, y₀, t₀} : Finset _) = {s, l, r} := by
      apply Eq.trans (Finset.eq_of_subset_of_card_le hsubset ?_) hsupport
      rw [hsmall, hsupport]
      exact Finset.card_le_three
    exact lineCandidate_permute_encode o x₀ y₀ t₀
      (generatedFirstSplit_lineCandidateABC hprimitive htriple hxy₀ hxt₀ hyt₀)
  · have hsubset : ({x₀, y₀, t₀} : Finset _) ⊆ D ∆ E := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact hx₀
      · exact hy₀
      · exact ht₀
    have htriple : ({x₀, y₀, t₀} : Finset _) = {l, r, s} := by
      apply Eq.trans (Finset.eq_of_subset_of_card_le hsubset ?_) hsupport
      rw [hsmall, hsupport]
      exact Finset.card_le_three
    exact lineCandidate_permute_encode o x₀ y₀ t₀
      (directedReduction_lineCandidateABC hprimitive htriple hxy₀ hxt₀ hyt₀)

/-- A native three-support all-mode move is reflected by one of the raw
line-candidate orientations. -/
theorem allModeLineCandidate_encode {p : Profile} {D E : State p}
    (hmove : AllModeMove D E) (hcard : (D ∆ E).card = 3)
    {x y t : NormalizedBinaryCarrier.Carrier p}
    (hset : D ∆ E = {x, y, t})
    (hxy : x ≠ y) (hxt : x ≠ t) (hyt : y ≠ t) :
    ∃ o ∈ BinaryAmbientContextFiniteExclusion.orientations,
      BinaryAmbientContextFiniteExclusion.lineCandidate o
        (Raw.encodeTerm x) (Raw.encodeTerm y) = some (Raw.encodeTerm t) := by
  rcases AllModeMove.support_three_factor_line hmove hcard with
    hline | ⟨D₀, E₀, hline, himage⟩ |
      ⟨D₀, E₀, hline, himage⟩ |
        ⟨D₀, E₀, hline, himage⟩ |
          ⟨D₀, E₀, hline, himage⟩ |
            ⟨D₀, E₀, hline, himage⟩
  · refine ⟨.abc, by decide, ?_⟩
    apply orientedLinePrimitiveCandidate_encode (p := p) (o := .abc)
      (S := D ∆ E) (x := x) (y := y) (t := t) hline ?_ hset hxy hxt hyt
    have hfun : NormalizedBinaryModePermutation.permuteTerm .abc =
        (id : NormalizedBinaryCarrier.Carrier p → _) := by
      funext q
      rcases p with ⟨a, b, c⟩
      rcases q with ⟨q1, q2, q3⟩
      rfl
    rw [hfun]
    exact (@Finset.image_id _ (D ∆ E) _).symm
  · refine ⟨.bca, by decide, ?_⟩
    exact orientedLinePrimitiveCandidate_encode
      (p := ⟨p.third, p.first, p.second⟩) (o := .bca)
      (S := D ∆ E) (x := x) (y := y) (t := t)
      hline himage hset hxy hxt hyt
  · refine ⟨.cab, by decide, ?_⟩
    exact orientedLinePrimitiveCandidate_encode
      (p := ⟨p.second, p.third, p.first⟩) (o := .cab)
      (S := D ∆ E) (x := x) (y := y) (t := t)
      hline himage hset hxy hxt hyt
  · refine ⟨.acb, by decide, ?_⟩
    exact orientedLinePrimitiveCandidate_encode
      (p := ⟨p.first, p.third, p.second⟩) (o := .acb)
      (S := D ∆ E) (x := x) (y := y) (t := t)
      hline himage hset hxy hxt hyt
  · refine ⟨.cba, by decide, ?_⟩
    exact orientedLinePrimitiveCandidate_encode
      (p := ⟨p.third, p.second, p.first⟩) (o := .cba)
      (S := D ∆ E) (x := x) (y := y) (t := t)
      hline himage hset hxy hxt hyt
  · refine ⟨.bac, by decide, ?_⟩
    exact orientedLinePrimitiveCandidate_encode
      (p := ⟨p.second, p.first, p.third⟩) (o := .bac)
      (S := D ∆ E) (x := x) (y := y) (t := t)
      hline himage hset hxy hxt hyt


/-! ## Production-row encoding identities -/

/-- Encoding the production `411-01` start state gives its raw checker table. -/
theorem row41101Start_encode :
    row41101Start.image Raw.encodeTerm =
      BinaryAmbientContextFiniteExclusion.row41101A.toFinset := by
  decide

/-- Encoding the production `411-01` finish state gives its raw checker table. -/
theorem row41101Finish_encode :
    row41101Finish.image Raw.encodeTerm =
      BinaryAmbientContextFiniteExclusion.row41101B.toFinset := by
  decide

/-- Encoding the production `321-01` start state gives its raw checker table. -/
theorem row32101Start_encode :
    row32101Start.image Raw.encodeTerm =
      BinaryAmbientContextFiniteExclusion.row32101A.toFinset := by
  decide

/-- Encoding the production `321-01` finish state gives its raw checker table. -/
theorem row32101Finish_encode :
    row32101Finish.image Raw.encodeTerm =
      BinaryAmbientContextFiniteExclusion.row32101B.toFinset := by
  decide

/-- Encoding the production `321-02` start state gives its raw checker table. -/
theorem row32102Start_encode :
    row32102Start.image Raw.encodeTerm =
      BinaryAmbientContextFiniteExclusion.row32102A.toFinset := by
  decide

/-- Encoding the production `321-02` finish state gives its raw checker table. -/
theorem row32102Finish_encode :
    row32102Finish.image Raw.encodeTerm =
      BinaryAmbientContextFiniteExclusion.row32102B.toFinset := by
  decide

/-- Encoding the production `321-03` start state gives its raw checker table. -/
theorem row32103Start_encode :
    row32103Start.image Raw.encodeTerm =
      BinaryAmbientContextFiniteExclusion.row32103A.toFinset := by
  decide

/-- Encoding the production `321-03` finish state gives its raw checker table. -/
theorem row32103Finish_encode :
    row32103Finish.image Raw.encodeTerm =
      BinaryAmbientContextFiniteExclusion.row32103B.toFinset := by
  decide

/-- Encoding the production `222-01` start state gives its raw checker table. -/
theorem row22201Start_encode :
    row22201Start.image Raw.encodeTerm =
      BinaryAmbientContextFiniteExclusion.row22201A.toFinset := by
  decide

/-- Encoding the production `222-01` finish state gives its raw checker table. -/
theorem row22201Finish_encode :
    row22201Finish.image Raw.encodeTerm =
      BinaryAmbientContextFiniteExclusion.row22201B.toFinset := by
  decide

end BilinearComplexity.BinaryContextualExclusionSemantics
