import BilinearComplexity.NormalizedBinaryFiveCircuitRows

/-!
# Kernel evaluations of a raw contextual support-candidate checker

This module defines a proof-free Boolean checker on raw triples of Boolean
lists. Its line auxiliary is computed from one of ten displayed endpoint pairs
and six coordinate orientations, rather than scanned over a carrier. The five
closed theorems below state only that this raw checker evaluates to `false` on
five explicitly encoded tables, using kernel reduction.

`VectorCode` and `TermCode` deliberately carry no dimension, equal-length, or
nonzero invariant. In particular, `vectorAdd` truncates unequal lists and a
line candidate may contain a zero or otherwise malformed factor code. No
result in this module identifies the tables with production normalized rows,
reflects native moves into the checker, or proves an ambient path exclusion;
those semantic bridges are supplied separately by
`BinaryContextualExclusionSemantics`, `BinaryContextualFlipReflection`, and
`BinaryContextualNativeExclusion`, with ambient optimality in
`BinaryContextualFiveCircuitOptimality`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

namespace BilinearComplexity.BinaryAmbientContextFiniteExclusion

open NormalizedBinaryCarrier
open NormalizedBinaryReplay221
open NormalizedBinaryModePermutation
open NormalizedBinaryFiveCircuitRows
open Scheme.Action

/-- A raw factor code: an arbitrary finite Boolean list with no attached
dimension or nonzero invariant. -/
abbrev VectorCode := List Bool

/-- A raw triple of factor codes. No field is required to be nonempty,
nonzero, or dimension-compatible with another term. -/
structure TermCode where
  first : VectorCode
  second : VectorCode
  third : VectorCode
  deriving DecidableEq, Repr

/-- Pointwise Boolean XOR, with the exact truncating semantics of
`List.zipWith` when the two raw codes have unequal lengths. -/
def vectorAdd (x y : VectorCode) : VectorCode :=
  List.zipWith xor x y

/-- The six coordinate orientations. -/
def orientations : List Orientation :=
  [.abc, .bca, .cab, .acb, .cba, .bac]

/-- Pull a target-coordinate code back through an orientation. -/
def inverseCode (o : Orientation) (t : TermCode) : TermCode :=
  match o with
  | .abc => t
  | .bca => ⟨t.third, t.first, t.second⟩
  | .cab => ⟨t.second, t.third, t.first⟩
  | .acb => ⟨t.first, t.third, t.second⟩
  | .cba => ⟨t.third, t.second, t.first⟩
  | .bac => ⟨t.second, t.first, t.third⟩

/-- Push a source-coordinate code forward through an orientation. -/
def forwardCode (o : Orientation) (t : TermCode) : TermCode :=
  match o with
  | .abc => t
  | .bca => ⟨t.second, t.third, t.first⟩
  | .cab => ⟨t.third, t.first, t.second⟩
  | .acb => ⟨t.first, t.third, t.second⟩
  | .cba => ⟨t.third, t.second, t.first⟩
  | .bac => ⟨t.second, t.first, t.third⟩

/-- Compute a raw first-coordinate line candidate when the other raw
coordinates agree and the first lists differ. The output is not checked for
nonzeroness or dimensional validity. -/
def lineCandidateABC (x y : TermCode) : Option TermCode :=
  if x.second = y.second ∧ x.third = y.third ∧ x.first ≠ y.first then
    some ⟨vectorAdd x.first y.first, x.second, x.third⟩
  else none

/-- Compute a raw line candidate in target coordinate order for one of the
six list-coordinate orientations. -/
def lineCandidate (o : Orientation) (x y : TermCode) : Option TermCode :=
  (lineCandidateABC (inverseCode o x) (inverseCode o y)).map (forwardCode o)

/-- Test the displayed raw list equalities for one ordered ABC Flip
candidate. This does not assert native move legality. -/
def thirdFlipWitnessABC (sl sr tl tr : TermCode) : Bool :=
  sr.third == sl.third &&
  tl.first == vectorAdd sl.first sr.first &&
  tl.second == sl.second && tl.third == sl.third &&
  tr.first == sr.first &&
  tr.second == vectorAdd sr.second sl.second &&
  tr.third == sl.third

/-- Test complementary two-versus-two occupancy and either ordering of
the two remaining raw terms for one ordered source pair. -/
def thirdFlipPairABC (osl osr ox oy : Bool)
    (sl sr x y : TermCode) : Bool :=
  let occupancy := (osl && osr && !ox && !oy) || (!osl && !osr && ox && oy)
  occupancy &&
    ((thirdFlipWitnessABC sl sr x y) || (thirdFlipWitnessABC sl sr y x))

/-- Test the twelve ordered source pairs among four raw terms in the ABC
coordinate order. -/
def thirdFlip4ABC (oa ob oc od : Bool)
    (a b c d : TermCode) : Bool :=
  thirdFlipPairABC oa ob oc od a b c d ||
  thirdFlipPairABC ob oa oc od b a c d ||
  thirdFlipPairABC oa oc ob od a c b d ||
  thirdFlipPairABC oc oa ob od c a b d ||
  thirdFlipPairABC oa od ob oc a d b c ||
  thirdFlipPairABC od oa ob oc d a b c ||
  thirdFlipPairABC ob oc oa od b c a d ||
  thirdFlipPairABC oc ob oa od c b a d ||
  thirdFlipPairABC ob od oa oc b d a c ||
  thirdFlipPairABC od ob oa oc d b a c ||
  thirdFlipPairABC oc od oa ob c d a b ||
  thirdFlipPairABC od oc oa ob d c a b

/-- Test one raw coordinate orientation of a four-term Flip candidate. -/
def thirdFlip4Orientation (o : Orientation) (occupied : TermCode → Bool)
    (a b c d : TermCode) : Bool :=
  thirdFlip4ABC (occupied a) (occupied b) (occupied c) (occupied d)
    (inverseCode o a) (inverseCode o b) (inverseCode o c) (inverseCode o d)

/-- Test all six coordinate orientations for a raw four-term Flip
candidate. -/
def thirdFlip4 (occupied : TermCode → Bool)
    (a b c d : TermCode) : Bool :=
  thirdFlip4Orientation .abc occupied a b c d ||
  thirdFlip4Orientation .bca occupied a b c d ||
  thirdFlip4Orientation .cab occupied a b c d ||
  thirdFlip4Orientation .acb occupied a b c d ||
  thirdFlip4Orientation .cba occupied a b c d ||
  thirdFlip4Orientation .bac occupied a b c d

/-- Raw Boolean equality-membership in a displayed three-term list. -/
def support3Contains (x y z q : TermCode) : Bool :=
  q == x || q == y || q == z

/-- Test whether exactly one or exactly two of three displayed raw terms
are occupied. Duplicate displayed terms are not rejected. -/
def lineOccupancy (occupied : TermCode → Bool)
    (x y z : TermCode) : Bool :=
  let n := [occupied x, occupied y, occupied z].count true
  n == 1 || n == 2

/-- For a list of length exactly five, return the ten positional 2/3
partitions. Return the empty list at every other length. -/
def splits5 {α : Type*} (z : List α) : List ((α × α) × (α × α × α)) :=
  match z with
  | [a, b, c, d, e] =>
      [((a,b),(c,d,e)), ((a,c),(b,d,e)), ((a,d),(b,c,e)),
       ((a,e),(b,c,d)), ((b,c),(a,d,e)), ((b,d),(a,c,e)),
       ((b,e),(a,c,d)), ((c,d),(a,b,e)), ((c,e),(a,b,d)),
       ((d,e),(a,b,c))]
  | _ => []

/-- Check one raw orientation-computed auxiliary for both edge orders and
both possible initial auxiliary bits. This function assumes no distinctness,
dimension, or native-legality invariant beyond its explicit Boolean tests. -/
def checkCandidate (A Z : List TermCode)
    (x y u v w t : TermCode) : Bool :=
  !Z.contains t &&
  [false, true].any fun auxiliaryOccupied =>
    let startOccupied := fun q =>
      (auxiliaryOccupied && q == t) || A.contains q
    let afterLine := fun q =>
      xor (startOccupied q) (support3Contains t x y q)
    let afterFlip := fun q =>
      xor (startOccupied q) (q == t || q == u || q == v || q == w)
    (lineOccupancy startOccupied t x y && thirdFlip4 afterLine t u v w) ||
      (thirdFlip4 startOccupied t u v w && lineOccupancy afterFlip t x y)

/-- Search the ten positional partitions and six orientations for a raw
support-and-occupancy candidate. This is not by itself a native contextual path
predicate. -/
def hasContextualTwoEdgePath (A B : List TermCode) : Bool :=
  let Z := A ++ B
  (splits5 Z).any fun split =>
    let x := split.1.1
    let y := split.1.2
    let u := split.2.1
    let v := split.2.2.1
    let w := split.2.2.2
    orientations.any fun o =>
      match lineCandidate o x y with
      | none => false
      | some t => checkCandidate A Z x y u v w t


/-! ## Ground-truth audits for the raw checker -/

example : ([true, false] : VectorCode).length = 2 := rfl

example : (⟨[], [], []⟩ : TermCode).first = [] := rfl

example : vectorAdd [true, false] [true] = [false] := rfl

example : orientations = [.abc, .bca, .cab, .acb, .cba, .bac] := rfl

example :
    inverseCode .bca ⟨[true], [false], [true, false]⟩ =
      ⟨[true, false], [true], [false]⟩ := rfl

example (o : Orientation) (t : TermCode) :
    forwardCode o (inverseCode o t) = t := by
  cases o <;> rfl

example :
    lineCandidateABC ⟨[true], [true], [true]⟩
        ⟨[false], [true], [true]⟩ =
      some ⟨[true], [true], [true]⟩ := by
  decide

example :
    lineCandidateABC ⟨[true], [true], [true]⟩
        ⟨[false], [false], [true]⟩ = none := by
  decide

/-- Unequal raw dimensions are truncated, so this malformed pair produces a
zero first-factor list. This is raw checker behavior, not a native line. -/
example :
    lineCandidateABC ⟨[true], [true], [true]⟩
        ⟨[true, false], [true], [true]⟩ =
      some ⟨[false], [true], [true]⟩ := by
  decide

example :
    lineCandidate .bca ⟨[true], [true], [true, false]⟩
        ⟨[true], [true], [false, true]⟩ =
      some ⟨[true], [true], [true, true]⟩ := by
  decide

private def testX : TermCode :=
  ⟨[true, false, false], [true, false], [true]⟩
private def testY : TermCode :=
  ⟨[false, true, false], [true, false], [true]⟩
private def testT : TermCode :=
  ⟨[true, true, false], [true, false], [true]⟩
private def testU : TermCode :=
  ⟨[false, false, true], [false, true], [true]⟩
private def testV : TermCode :=
  ⟨[true, true, true], [true, false], [true]⟩
private def testW : TermCode :=
  ⟨[false, false, true], [true, true], [true]⟩

example : thirdFlipWitnessABC testT testU testV testW = true := by decide

example :
    thirdFlipPairABC true true false false testT testU testV testW = true := by
  decide

example :
    thirdFlip4ABC true true false false testT testU testV testW = true := by
  decide

example :
    thirdFlip4Orientation .abc
        (fun q => q == testT || q == testU) testT testU testV testW = true := by
  decide

example :
    thirdFlip4 (fun q => q == testT || q == testU)
      testT testU testV testW = true := by
  decide

example :
    support3Contains testT testX testY testX = true ∧
      support3Contains testT testX testY testU = false := by
  decide

example :
    lineOccupancy (fun q => q == testX) testT testX testY = true ∧
      lineOccupancy (fun _ => true) testT testX testY = false := by
  decide

example :
    (splits5 [0, 1, 2, 3, 4]).length = 10 ∧
      splits5 [0, 1] = [] := by
  decide

example :
    checkCandidate [testX, testU] [testX, testU, testY, testV, testW]
      testX testY testU testV testW testT = true := by
  decide

example :
    hasContextualTwoEdgePath [testX, testU] [testY, testV, testW] = true := by
  decide

private def one : Bool := true
private def zero : Bool := false

private def v1 : VectorCode := [one]
private def v2m1 : VectorCode := [one, zero]
private def v2m2 : VectorCode := [zero, one]
private def v2m3 : VectorCode := [one, one]
private def v3m1 : VectorCode := [one, zero, zero]
private def v3m2 : VectorCode := [zero, one, zero]
private def v3m3 : VectorCode := [one, one, zero]
private def v3m4 : VectorCode := [zero, zero, one]
private def v3m7 : VectorCode := [one, one, one]
private def v4m1 : VectorCode := [one, zero, zero, zero]
private def v4m2 : VectorCode := [zero, one, zero, zero]
private def v4m4 : VectorCode := [zero, zero, one, zero]
private def v4m8 : VectorCode := [zero, zero, zero, one]
private def v4m15 : VectorCode := [one, one, one, one]

private def code (a b c : VectorCode) : TermCode := ⟨a, b, c⟩

/-- Raw two-entry Boolean-code table used by the closed `41101`-named
calculation; no production-row encoding identity is asserted here. -/
def row41101A : List TermCode := [code v4m1 v1 v1, code v4m2 v1 v1]
/-- Raw three-entry Boolean-code table used by the closed `41101`-named
calculation; no production-row encoding identity is asserted here. -/
def row41101B : List TermCode :=
  [code v4m4 v1 v1, code v4m8 v1 v1, code v4m15 v1 v1]

/-- Raw two-entry Boolean-code table used by the closed `32101`-named
calculation; no production-row encoding identity is asserted here. -/
def row32101A : List TermCode := [code v3m1 v2m1 v1, code v3m1 v2m2 v1]
/-- Raw three-entry Boolean-code table used by the closed `32101`-named
calculation; no production-row encoding identity is asserted here. -/
def row32101B : List TermCode :=
  [code v3m2 v2m3 v1, code v3m4 v2m3 v1, code v3m7 v2m3 v1]

/-- Raw two-entry Boolean-code table used by the closed `32102`-named
calculation; no production-row encoding identity is asserted here. -/
def row32102A : List TermCode := [code v3m2 v2m3 v1, code v3m4 v2m3 v1]
/-- Raw three-entry Boolean-code table used by the closed `32102`-named
calculation; no production-row encoding identity is asserted here. -/
def row32102B : List TermCode :=
  [code v3m1 v2m1 v1, code v3m1 v2m2 v1, code v3m7 v2m3 v1]

/-- Raw two-entry Boolean-code table used by the closed `32103`-named
calculation; no production-row encoding identity is asserted here. -/
def row32103A : List TermCode := [code v3m1 v2m1 v1, code v3m2 v2m1 v1]
/-- Raw three-entry Boolean-code table used by the closed `32103`-named
calculation; no production-row encoding identity is asserted here. -/
def row32103B : List TermCode :=
  [code v3m3 v2m2 v1, code v3m4 v2m3 v1, code v3m7 v2m3 v1]

/-- Raw two-entry Boolean-code table used by the closed `22201`-named
calculation; no production-row encoding identity is asserted here. -/
def row22201A : List TermCode := [code v2m1 v2m1 v2m1, code v2m1 v2m1 v2m2]
/-- Raw three-entry Boolean-code table used by the closed `22201`-named
calculation; no production-row encoding identity is asserted here. -/
def row22201B : List TermCode :=
  [code v2m1 v2m2 v2m3, code v2m2 v2m3 v2m3, code v2m3 v2m3 v2m3]


example : row41101A.length = 2 ∧ row41101B.length = 3 := by decide
example : row32101A.length = 2 ∧ row32101B.length = 3 := by decide
example : row32102A.length = 2 ∧ row32102B.length = 3 := by decide
example : row32103A.length = 2 ∧ row32103B.length = 3 := by decide
example : row22201A.length = 2 ∧ row22201B.length = 3 := by decide

/-- Kernel evaluation says the raw support-candidate checker is false on
the two `41101`-named tables. This alone is not a native path exclusion. -/
theorem row41101_no_two_edge :
    hasContextualTwoEdgePath row41101A row41101B = false := by decide

/-- Kernel evaluation says the raw support-candidate checker is false on
the two `32101`-named tables. This alone is not a native path exclusion. -/
theorem row32101_no_two_edge :
    hasContextualTwoEdgePath row32101A row32101B = false := by decide

/-- Kernel evaluation says the raw support-candidate checker is false on
the two `32102`-named tables. This alone is not a native path exclusion. -/
theorem row32102_no_two_edge :
    hasContextualTwoEdgePath row32102A row32102B = false := by decide

/-- Kernel evaluation says the raw support-candidate checker is false on
the two `32103`-named tables. This alone is not a native path exclusion. -/
theorem row32103_no_two_edge :
    hasContextualTwoEdgePath row32103A row32103B = false := by decide

/-- Kernel evaluation says the raw support-candidate checker is false on
the two `22201`-named tables. This alone is not a native path exclusion. -/
theorem row22201_no_two_edge :
    hasContextualTwoEdgePath row22201A row22201B = false := by decide

end BilinearComplexity.BinaryAmbientContextFiniteExclusion
