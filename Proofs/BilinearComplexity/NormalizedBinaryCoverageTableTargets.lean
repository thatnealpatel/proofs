import BilinearComplexity.NormalizedBinaryCoverageTables

set_option autoImplicit false

namespace BilinearComplexity.NormalizedBinaryCoverageData.RawCoverageAction

open BilinearComplexity.NormalizedBinaryCarrier
open BilinearComplexity.NormalizedBinaryCoverageData
open BilinearComplexity.NormalizedBinaryFiniteAction

/-- A target occurs in the decoded target list exactly when some raw action in the
input list decodes to that target. -/
theorem mem_decodedTargets_iff {p : Profile} {ι : Type*}
    (target : RelationEndpoints p) (raws : List (RawCoverageAction p ι)) :
    target ∈ decodedTargets raws ↔
      ∃ raw ∈ raws, raw.decodedTarget? = some target := by
  induction raws with
  | nil =>
      simp [decodedTargets]
  | cons raw raws ih =>
      rw [decodedTargets.eq_def]
      cases hdecode : raw.decodedTarget? with
      | none =>
          simp [hdecode, ih]
      | some decoded =>
          simp [hdecode, ih, eq_comm]

/-- Membership in a decoded target finset is exactly witnessed by an input raw
action whose literal target decodes to that member. -/
theorem mem_decodedTargetSet_iff {p : Profile} {ι : Type*}
    (target : RelationEndpoints p) (raws : List (RawCoverageAction p ι)) :
    target ∈ decodedTargetSet raws ↔
      ∃ raw ∈ raws, raw.decodedTarget? = some target := by
  rw [decodedTargetSet, List.mem_toFinset, mem_decodedTargets_iff]

end BilinearComplexity.NormalizedBinaryCoverageData.RawCoverageAction

namespace BilinearComplexity.NormalizedBinaryCoverageTables

open BilinearComplexity.NormalizedBinaryCarrier
open BilinearComplexity.NormalizedBinaryCoverageData
open BilinearComplexity.NormalizedBinaryFiniteAction

/-- Membership in shard 000's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard000.mem_literalTargetSet_iff
    (target : RelationEndpoints profile221) :
    target ∈ Shard000.literalTargetSet ↔
      ∃ raw ∈ Shard000.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard000.rawActions

/-- Membership in shard 001's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard001.mem_literalTargetSet_iff
    (target : RelationEndpoints profile411) :
    target ∈ Shard001.literalTargetSet ↔
      ∃ raw ∈ Shard001.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard001.rawActions

/-- Membership in shard 002's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard002.mem_literalTargetSet_iff
    (target : RelationEndpoints profile411) :
    target ∈ Shard002.literalTargetSet ↔
      ∃ raw ∈ Shard002.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard002.rawActions

/-- Membership in shard 003's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard003.mem_literalTargetSet_iff
    (target : RelationEndpoints profile411) :
    target ∈ Shard003.literalTargetSet ↔
      ∃ raw ∈ Shard003.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard003.rawActions

/-- Membership in shard 004's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard004.mem_literalTargetSet_iff
    (target : RelationEndpoints profile411) :
    target ∈ Shard004.literalTargetSet ↔
      ∃ raw ∈ Shard004.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard004.rawActions

/-- Membership in shard 005's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard005.mem_literalTargetSet_iff
    (target : RelationEndpoints profile411) :
    target ∈ Shard005.literalTargetSet ↔
      ∃ raw ∈ Shard005.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard005.rawActions

/-- Membership in shard 006's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard006.mem_literalTargetSet_iff
    (target : RelationEndpoints profile411) :
    target ∈ Shard006.literalTargetSet ↔
      ∃ raw ∈ Shard006.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard006.rawActions

/-- Membership in shard 007's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard007.mem_literalTargetSet_iff
    (target : RelationEndpoints profile411) :
    target ∈ Shard007.literalTargetSet ↔
      ∃ raw ∈ Shard007.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard007.rawActions

/-- Membership in shard 008's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard008.mem_literalTargetSet_iff
    (target : RelationEndpoints profile411) :
    target ∈ Shard008.literalTargetSet ↔
      ∃ raw ∈ Shard008.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard008.rawActions

/-- Membership in shard 009's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard009.mem_literalTargetSet_iff
    (target : RelationEndpoints profile411) :
    target ∈ Shard009.literalTargetSet ↔
      ∃ raw ∈ Shard009.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard009.rawActions

/-- Membership in shard 010's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard010.mem_literalTargetSet_iff
    (target : RelationEndpoints profile411) :
    target ∈ Shard010.literalTargetSet ↔
      ∃ raw ∈ Shard010.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard010.rawActions

/-- Membership in shard 011's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard011.mem_literalTargetSet_iff
    (target : RelationEndpoints profile411) :
    target ∈ Shard011.literalTargetSet ↔
      ∃ raw ∈ Shard011.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard011.rawActions

/-- Membership in shard 012's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard012.mem_literalTargetSet_iff
    (target : RelationEndpoints profile411) :
    target ∈ Shard012.literalTargetSet ↔
      ∃ raw ∈ Shard012.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard012.rawActions

/-- Membership in shard 013's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard013.mem_literalTargetSet_iff
    (target : RelationEndpoints profile411) :
    target ∈ Shard013.literalTargetSet ↔
      ∃ raw ∈ Shard013.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard013.rawActions

/-- Membership in shard 014's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard014.mem_literalTargetSet_iff
    (target : RelationEndpoints profile411) :
    target ∈ Shard014.literalTargetSet ↔
      ∃ raw ∈ Shard014.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard014.rawActions

/-- Membership in shard 015's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard015.mem_literalTargetSet_iff
    (target : RelationEndpoints profile321) :
    target ∈ Shard015.literalTargetSet ↔
      ∃ raw ∈ Shard015.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard015.rawActions

/-- Membership in shard 016's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard016.mem_literalTargetSet_iff
    (target : RelationEndpoints profile321) :
    target ∈ Shard016.literalTargetSet ↔
      ∃ raw ∈ Shard016.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard016.rawActions

/-- Membership in shard 017's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard017.mem_literalTargetSet_iff
    (target : RelationEndpoints profile321) :
    target ∈ Shard017.literalTargetSet ↔
      ∃ raw ∈ Shard017.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard017.rawActions

/-- Membership in shard 018's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard018.mem_literalTargetSet_iff
    (target : RelationEndpoints profile321) :
    target ∈ Shard018.literalTargetSet ↔
      ∃ raw ∈ Shard018.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard018.rawActions

/-- Membership in shard 019's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard019.mem_literalTargetSet_iff
    (target : RelationEndpoints profile321) :
    target ∈ Shard019.literalTargetSet ↔
      ∃ raw ∈ Shard019.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard019.rawActions

/-- Membership in shard 020's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard020.mem_literalTargetSet_iff
    (target : RelationEndpoints profile321) :
    target ∈ Shard020.literalTargetSet ↔
      ∃ raw ∈ Shard020.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard020.rawActions

/-- Membership in shard 021's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard021.mem_literalTargetSet_iff
    (target : RelationEndpoints profile321) :
    target ∈ Shard021.literalTargetSet ↔
      ∃ raw ∈ Shard021.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard021.rawActions

/-- Membership in shard 022's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard022.mem_literalTargetSet_iff
    (target : RelationEndpoints profile321) :
    target ∈ Shard022.literalTargetSet ↔
      ∃ raw ∈ Shard022.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard022.rawActions

/-- Membership in shard 023's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard023.mem_literalTargetSet_iff
    (target : RelationEndpoints profile321) :
    target ∈ Shard023.literalTargetSet ↔
      ∃ raw ∈ Shard023.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard023.rawActions

/-- Membership in shard 024's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard024.mem_literalTargetSet_iff
    (target : RelationEndpoints profile321) :
    target ∈ Shard024.literalTargetSet ↔
      ∃ raw ∈ Shard024.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard024.rawActions

/-- Membership in shard 025's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard025.mem_literalTargetSet_iff
    (target : RelationEndpoints profile321) :
    target ∈ Shard025.literalTargetSet ↔
      ∃ raw ∈ Shard025.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard025.rawActions

/-- Membership in shard 026's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard026.mem_literalTargetSet_iff
    (target : RelationEndpoints profile321) :
    target ∈ Shard026.literalTargetSet ↔
      ∃ raw ∈ Shard026.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard026.rawActions

/-- Membership in shard 027's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard027.mem_literalTargetSet_iff
    (target : RelationEndpoints profile321) :
    target ∈ Shard027.literalTargetSet ↔
      ∃ raw ∈ Shard027.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard027.rawActions

/-- Membership in shard 028's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard028.mem_literalTargetSet_iff
    (target : RelationEndpoints profile321) :
    target ∈ Shard028.literalTargetSet ↔
      ∃ raw ∈ Shard028.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard028.rawActions

/-- Membership in shard 029's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard029.mem_literalTargetSet_iff
    (target : RelationEndpoints profile321) :
    target ∈ Shard029.literalTargetSet ↔
      ∃ raw ∈ Shard029.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard029.rawActions

/-- Membership in shard 030's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard030.mem_literalTargetSet_iff
    (target : RelationEndpoints profile321) :
    target ∈ Shard030.literalTargetSet ↔
      ∃ raw ∈ Shard030.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard030.rawActions

/-- Membership in shard 031's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard031.mem_literalTargetSet_iff
    (target : RelationEndpoints profile321) :
    target ∈ Shard031.literalTargetSet ↔
      ∃ raw ∈ Shard031.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard031.rawActions

/-- Membership in shard 032's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard032.mem_literalTargetSet_iff
    (target : RelationEndpoints profile222) :
    target ∈ Shard032.literalTargetSet ↔
      ∃ raw ∈ Shard032.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard032.rawActions

/-- Membership in shard 033's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard033.mem_literalTargetSet_iff
    (target : RelationEndpoints profile222) :
    target ∈ Shard033.literalTargetSet ↔
      ∃ raw ∈ Shard033.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard033.rawActions

/-- Membership in shard 034's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard034.mem_literalTargetSet_iff
    (target : RelationEndpoints profile222) :
    target ∈ Shard034.literalTargetSet ↔
      ∃ raw ∈ Shard034.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard034.rawActions

/-- Membership in shard 035's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard035.mem_literalTargetSet_iff
    (target : RelationEndpoints profile222) :
    target ∈ Shard035.literalTargetSet ↔
      ∃ raw ∈ Shard035.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard035.rawActions

/-- Membership in shard 036's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard036.mem_literalTargetSet_iff
    (target : RelationEndpoints profile222) :
    target ∈ Shard036.literalTargetSet ↔
      ∃ raw ∈ Shard036.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard036.rawActions

/-- Membership in shard 037's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard037.mem_literalTargetSet_iff
    (target : RelationEndpoints profile222) :
    target ∈ Shard037.literalTargetSet ↔
      ∃ raw ∈ Shard037.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard037.rawActions

/-- Membership in shard 038's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard038.mem_literalTargetSet_iff
    (target : RelationEndpoints profile222) :
    target ∈ Shard038.literalTargetSet ↔
      ∃ raw ∈ Shard038.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard038.rawActions

/-- Membership in shard 039's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard039.mem_literalTargetSet_iff
    (target : RelationEndpoints profile222) :
    target ∈ Shard039.literalTargetSet ↔
      ∃ raw ∈ Shard039.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard039.rawActions

/-- Membership in shard 040's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard040.mem_literalTargetSet_iff
    (target : RelationEndpoints profile222) :
    target ∈ Shard040.literalTargetSet ↔
      ∃ raw ∈ Shard040.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard040.rawActions

/-- Membership in shard 041's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard041.mem_literalTargetSet_iff
    (target : RelationEndpoints profile222) :
    target ∈ Shard041.literalTargetSet ↔
      ∃ raw ∈ Shard041.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard041.rawActions

/-- Membership in shard 042's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard042.mem_literalTargetSet_iff
    (target : RelationEndpoints profile222) :
    target ∈ Shard042.literalTargetSet ↔
      ∃ raw ∈ Shard042.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard042.rawActions

/-- Membership in shard 043's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard043.mem_literalTargetSet_iff
    (target : RelationEndpoints profile222) :
    target ∈ Shard043.literalTargetSet ↔
      ∃ raw ∈ Shard043.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard043.rawActions

/-- Membership in shard 044's literal target set is witnessed exactly by one of
that shard's raw actions decoding to the target. -/
theorem Shard044.mem_literalTargetSet_iff
    (target : RelationEndpoints profile222) :
    target ∈ Shard044.literalTargetSet ↔
      ∃ raw ∈ Shard044.rawActions, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target Shard044.rawActions

/-- Membership in the aggregate profile-221 literal target set is witnessed
exactly by one of the aggregate raw actions decoding to the target. -/
theorem mem_literalTargetSet221_iff
    (target : RelationEndpoints profile221) :
    target ∈ literalTargetSet221 ↔
      ∃ raw ∈ rawActions221, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target rawActions221

/-- Membership in the aggregate profile-411 literal target set is witnessed
exactly by one of the aggregate raw actions decoding to the target. -/
theorem mem_literalTargetSet411_iff
    (target : RelationEndpoints profile411) :
    target ∈ literalTargetSet411 ↔
      ∃ raw ∈ rawActions411, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target rawActions411

/-- Membership in the aggregate profile-321 literal target set is witnessed
exactly by one of the aggregate raw actions decoding to the target. -/
theorem mem_literalTargetSet321_iff
    (target : RelationEndpoints profile321) :
    target ∈ literalTargetSet321 ↔
      ∃ raw ∈ rawActions321, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target rawActions321

/-- Membership in the aggregate profile-222 literal target set is witnessed
exactly by one of the aggregate raw actions decoding to the target. -/
theorem mem_literalTargetSet222_iff
    (target : RelationEndpoints profile222) :
    target ∈ literalTargetSet222 ↔
      ∃ raw ∈ rawActions222, raw.decodedTarget? = some target := by
  exact RawCoverageAction.mem_decodedTargetSet_iff target rawActions222

example :
    ∀ target : RelationEndpoints profile221,
      target ∉ RawCoverageAction.decodedTargets
        ([] : List (RawCoverageAction profile221 (Fin 3))) := by
  intro target
  simp [RawCoverageAction.decodedTargets]

#check @RawCoverageAction.mem_decodedTargets_iff
#check @RawCoverageAction.mem_decodedTargetSet_iff
#check @Shard000.mem_literalTargetSet_iff
#check @Shard022.mem_literalTargetSet_iff
#check @mem_literalTargetSet411_iff

#print axioms RawCoverageAction.mem_decodedTargets_iff
#print axioms RawCoverageAction.mem_decodedTargetSet_iff
#print axioms Shard000.mem_literalTargetSet_iff
#print axioms Shard022.mem_literalTargetSet_iff
#print axioms mem_literalTargetSet411_iff

end BilinearComplexity.NormalizedBinaryCoverageTables
