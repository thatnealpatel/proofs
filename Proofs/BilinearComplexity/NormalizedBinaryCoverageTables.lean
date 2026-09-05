import BilinearComplexity.NormalizedBinaryCoverageTables.Shard000
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard001
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard002
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard003
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard004
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard005
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard006
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard007
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard008
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard009
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard010
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard011
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard012
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard013
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard014
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard015
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard016
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard017
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard018
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard019
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard020
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard021
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard022
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard023
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard024
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard025
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard026
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard027
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard028
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard029
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard030
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard031
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard032
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard033
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard034
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard035
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard036
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard037
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard038
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard039
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard040
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard041
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard042
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard043
import BilinearComplexity.NormalizedBinaryCoverageTables.Shard044

set_option autoImplicit false

namespace BilinearComplexity.NormalizedBinaryCoverageTables

open BilinearComplexity.NormalizedBinaryCarrier
open BilinearComplexity.NormalizedBinaryCoverageData
open BilinearComplexity.NormalizedBinaryFiniteAction

/-- SHA-256 of the JSON artifact from which all table literals were generated. -/
def sourceSHA256 : String := "bdb8a983a8cad61c375811e21a5cdb831dac77ceb70e4b9eb832d26df727f0bf"

/-- All generated raw coverage actions for profile 221. -/
def rawActions221 : List (RawCoverageAction profile221 (Fin 3)) := Shard000.rawActions

/-- All kernel-checked coverage entries for profile 221. -/
def coverageEntries221 : List (RawCoverageAction.Entry selectedRowSources221) := Shard000.entries

/-- Projecting the profile-221 entries recovers its raw action list. -/
theorem coverageEntries221_raws : coverageEntries221.map RawCoverageAction.Entry.raw = rawActions221 := by
  simp only [coverageEntries221, rawActions221, Shard000.entries_rawActions]

/-- All literal decoded targets for profile 221, without checker reduction. -/
def literalTargetSet221 : Finset (RelationEndpoints profile221) :=
  RawCoverageAction.decodedTargetSet rawActions221

/-- All generated raw coverage actions for profile 411. -/
def rawActions411 : List (RawCoverageAction profile411 (Fin 1)) := Shard001.rawActions ++ Shard002.rawActions ++ Shard003.rawActions ++ Shard004.rawActions ++ Shard005.rawActions ++ Shard006.rawActions ++ Shard007.rawActions ++ Shard008.rawActions ++ Shard009.rawActions ++ Shard010.rawActions ++ Shard011.rawActions ++ Shard012.rawActions ++ Shard013.rawActions ++ Shard014.rawActions

/-- All kernel-checked coverage entries for profile 411. -/
def coverageEntries411 : List (RawCoverageAction.Entry selectedRowSources411) := Shard001.entries ++ Shard002.entries ++ Shard003.entries ++ Shard004.entries ++ Shard005.entries ++ Shard006.entries ++ Shard007.entries ++ Shard008.entries ++ Shard009.entries ++ Shard010.entries ++ Shard011.entries ++ Shard012.entries ++ Shard013.entries ++ Shard014.entries

/-- Projecting the profile-411 entries recovers its raw action list. -/
theorem coverageEntries411_raws : coverageEntries411.map RawCoverageAction.Entry.raw = rawActions411 := by
  simp only [coverageEntries411, rawActions411, List.map_append, Shard001.entries_rawActions, Shard002.entries_rawActions, Shard003.entries_rawActions, Shard004.entries_rawActions, Shard005.entries_rawActions, Shard006.entries_rawActions, Shard007.entries_rawActions, Shard008.entries_rawActions, Shard009.entries_rawActions, Shard010.entries_rawActions, Shard011.entries_rawActions, Shard012.entries_rawActions, Shard013.entries_rawActions, Shard014.entries_rawActions]

/-- All literal decoded targets for profile 411, without checker reduction. -/
def literalTargetSet411 : Finset (RelationEndpoints profile411) :=
  RawCoverageAction.decodedTargetSet rawActions411

/-- All generated raw coverage actions for profile 321. -/
def rawActions321 : List (RawCoverageAction profile321 (Fin 6)) := Shard015.rawActions ++ Shard016.rawActions ++ Shard017.rawActions ++ Shard018.rawActions ++ Shard019.rawActions ++ Shard020.rawActions ++ Shard021.rawActions ++ Shard022.rawActions ++ Shard023.rawActions ++ Shard024.rawActions ++ Shard025.rawActions ++ Shard026.rawActions ++ Shard027.rawActions ++ Shard028.rawActions ++ Shard029.rawActions ++ Shard030.rawActions ++ Shard031.rawActions

/-- All kernel-checked coverage entries for profile 321. -/
def coverageEntries321 : List (RawCoverageAction.Entry selectedRowSources321) := Shard015.entries ++ Shard016.entries ++ Shard017.entries ++ Shard018.entries ++ Shard019.entries ++ Shard020.entries ++ Shard021.entries ++ Shard022.entries ++ Shard023.entries ++ Shard024.entries ++ Shard025.entries ++ Shard026.entries ++ Shard027.entries ++ Shard028.entries ++ Shard029.entries ++ Shard030.entries ++ Shard031.entries

/-- Projecting the profile-321 entries recovers its raw action list. -/
theorem coverageEntries321_raws : coverageEntries321.map RawCoverageAction.Entry.raw = rawActions321 := by
  simp only [coverageEntries321, rawActions321, List.map_append, Shard015.entries_rawActions, Shard016.entries_rawActions, Shard017.entries_rawActions, Shard018.entries_rawActions, Shard019.entries_rawActions, Shard020.entries_rawActions, Shard021.entries_rawActions, Shard022.entries_rawActions, Shard023.entries_rawActions, Shard024.entries_rawActions, Shard025.entries_rawActions, Shard026.entries_rawActions, Shard027.entries_rawActions, Shard028.entries_rawActions, Shard029.entries_rawActions, Shard030.entries_rawActions, Shard031.entries_rawActions]

/-- All literal decoded targets for profile 321, without checker reduction. -/
def literalTargetSet321 : Finset (RelationEndpoints profile321) :=
  RawCoverageAction.decodedTargetSet rawActions321

/-- All generated raw coverage actions for profile 222. -/
def rawActions222 : List (RawCoverageAction profile222 (Fin 3)) := Shard032.rawActions ++ Shard033.rawActions ++ Shard034.rawActions ++ Shard035.rawActions ++ Shard036.rawActions ++ Shard037.rawActions ++ Shard038.rawActions ++ Shard039.rawActions ++ Shard040.rawActions ++ Shard041.rawActions ++ Shard042.rawActions ++ Shard043.rawActions ++ Shard044.rawActions

/-- All kernel-checked coverage entries for profile 222. -/
def coverageEntries222 : List (RawCoverageAction.Entry selectedRowSources222) := Shard032.entries ++ Shard033.entries ++ Shard034.entries ++ Shard035.entries ++ Shard036.entries ++ Shard037.entries ++ Shard038.entries ++ Shard039.entries ++ Shard040.entries ++ Shard041.entries ++ Shard042.entries ++ Shard043.entries ++ Shard044.entries

/-- Projecting the profile-222 entries recovers its raw action list. -/
theorem coverageEntries222_raws : coverageEntries222.map RawCoverageAction.Entry.raw = rawActions222 := by
  simp only [coverageEntries222, rawActions222, List.map_append, Shard032.entries_rawActions, Shard033.entries_rawActions, Shard034.entries_rawActions, Shard035.entries_rawActions, Shard036.entries_rawActions, Shard037.entries_rawActions, Shard038.entries_rawActions, Shard039.entries_rawActions, Shard040.entries_rawActions, Shard041.entries_rawActions, Shard042.entries_rawActions, Shard043.entries_rawActions, Shard044.entries_rawActions]

/-- All literal decoded targets for profile 222, without checker reduction. -/
def literalTargetSet222 : Finset (RelationEndpoints profile222) :=
  RawCoverageAction.decodedTargetSet rawActions222

#print axioms coverageEntries221_raws
#print axioms coverageEntries411_raws
#print axioms coverageEntries321_raws
#print axioms coverageEntries222_raws

example : sourceSHA256 = "bdb8a983a8cad61c375811e21a5cdb831dac77ceb70e4b9eb832d26df727f0bf" := rfl

end BilinearComplexity.NormalizedBinaryCoverageTables
