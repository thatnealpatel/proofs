import BilinearComplexity.NormalizedBinaryCoverageConcrete
import BilinearComplexity.NormalizedBinaryOrbitInvariants

set_option autoImplicit false

/-!
# Classification of exact normalized binary relations into thirteen orbits

The orbit-membership predicate in this module is semantic: it asks for a
profile orientation and an arbitrary checked action witness from a selected
replay row to the oriented requested relation.  It does not mention generated
coverage entries or compiler labels.  Coverage supplies existence, while the
profile key and semantic pair-agreement counts supply uniqueness.
-/

namespace BilinearComplexity.NormalizedBinaryOrbitClassification

open BinaryCircuit
open NormalizedBinaryAllModeMove
open NormalizedBinaryCarrier
open NormalizedBinaryCoverage
open NormalizedBinaryCoverageData
open NormalizedBinaryFiniteAction
open NormalizedBinaryFiveCircuitCertificate
open NormalizedBinaryFiveCircuitRows
open NormalizedBinaryModePermutation
open NormalizedBinaryOrbitInvariants
open NormalizedBinaryProfileOrientation
open NormalizedBinaryRelationEnumeration
open Scheme.Action

/-- The unordered profile key used to distinguish the four canonical
families: total dimension together with the largest factor dimension. -/
def profileKey (p : Profile) : ℕ × ℕ :=
  (p.first + p.second + p.third, max p.first (max p.second p.third))

example : profileKey profile221 = (5, 2) := rfl
example : profileKey profile411 = (6, 4) := rfl
example : profileKey profile321 = (6, 3) := rfl
example : profileKey profile222 = (6, 2) := rfl

/-- Every permutation of the three factor modes preserves the unordered
profile key. -/
theorem profileKey_perm (o : Orientation) (p : Profile) :
    profileKey (permProfile o p) = profileKey p := by
  cases o <;> cases p <;> apply Prod.ext <;>
    simp only [profileKey, Orientation.firstDim,
      Orientation.secondDim, Orientation.thirdDim]
  all_goals first | rfl | ac_rfl

/-- The profile key attached to a canonical family. -/
def familyProfileKey (family : CanonicalProfileFamily) : ℕ × ℕ :=
  profileKey family.profile

example : familyProfileKey .family221 = (5, 2) := rfl
example : familyProfileKey .family411 = (6, 4) := rfl
example : familyProfileKey .family321 = (6, 3) := rfl
example : familyProfileKey .family222 = (6, 2) := rfl

/-- The `(sum,max)` keys are injective on the four supported canonical
families. -/
theorem familyProfileKey_injective : Function.Injective familyProfileKey := by
  intro family family' hkey
  cases family <;> cases family'
  all_goals first | rfl | (exfalso; revert hkey; decide)

/-- Two orientations of the same ordered profile into supported canonical
profiles necessarily select the same family. -/
theorem profileOrientation_family_unique {p : Profile}
    (first second : ProfileOrientation p) : first.family = second.family := by
  apply familyProfileKey_injective
  have hfirst : familyProfileKey first.family = profileKey p := by
    rw [familyProfileKey, ← first.profile_eq, profileKey_perm]
  have hsecond : familyProfileKey second.family = profileKey p := by
    rw [familyProfileKey, ← second.profile_eq, profileKey_perm]
  exact hfirst.trans hsecond.symm

/-- The four canonical profile families form a finite type with no additional
cases. -/
instance canonicalProfileFamilyFintype : Fintype CanonicalProfileFamily where
  elems := {.family221, .family411, .family321, .family222}
  complete family := by
    cases family <;> simp

/-- Every family-specific selected-row index type carries its evident finite
enumeration. -/
@[instance_reducible] def familyRowIndexFintype :
    (family : CanonicalProfileFamily) → Fintype (FamilyRowIndex family)
  | .family221 => inferInstanceAs (Fintype (Fin 3))
  | .family411 => inferInstanceAs (Fintype (Fin 1))
  | .family321 => inferInstanceAs (Fintype (Fin 6))
  | .family222 => inferInstanceAs (Fintype (Fin 3))

attribute [instance] familyRowIndexFintype

/-- Every family-specific selected-row index type has decidable equality. -/
@[instance_reducible] def familyRowIndexDecidableEq :
    (family : CanonicalProfileFamily) → DecidableEq (FamilyRowIndex family)
  | .family221 => inferInstanceAs (DecidableEq (Fin 3))
  | .family411 => inferInstanceAs (DecidableEq (Fin 1))
  | .family321 => inferInstanceAs (DecidableEq (Fin 6))
  | .family222 => inferInstanceAs (DecidableEq (Fin 3))

attribute [instance] familyRowIndexDecidableEq

/-- A normalized orbit label is a canonical family together with one of that
family's selected replay-row indices. -/
def OrbitLabel : Type := Sigma FamilyRowIndex

/-- Orbit labels form a finite type by summing the selected rows over the four
canonical families. -/
instance orbitLabelFintype : Fintype OrbitLabel := by
  unfold OrbitLabel
  infer_instance

/-- Equality of orbit labels is constructively decidable from family and
row-index equality. -/
instance orbitLabelDecidableEq : DecidableEq OrbitLabel := by
  unfold OrbitLabel
  infer_instance

example : Nonempty OrbitLabel := ⟨⟨.family221, (0 : Fin 3)⟩⟩

/-- There are exactly thirteen public normalized orbit labels. -/
theorem orbitLabel_card : Fintype.card OrbitLabel = 13 := by
  decide

/-- The selected ordered endpoint relation denoted by an orbit label. -/
def OrbitLabel.selectedEndpoints (label : OrbitLabel) :
    RelationEndpoints label.1.profile :=
  (familyRowSources label.1 label.2).endpoints

example :
    (OrbitLabel.selectedEndpoints
      (⟨.family221, (0 : Fin 3)⟩ : OrbitLabel)).left =
      NormalizedBinaryFiveCircuitRows.row22101Start := rfl

/-- Every selected replay-row endpoint pair satisfies the semantic exactness
predicate used by the classifier. -/
theorem selectedEndpoints_isExactRelation (label : OrbitLabel) :
    IsExactRelation label.selectedEndpoints := by
  rcases label with ⟨family, index⟩
  cases family with
  | family221 =>
      fin_cases index
      · exact ⟨certified22101.card_start, certified22101.card_finish,
          certified22101.disjoint,
          (allModeMovePath_preserves_evaluation
            certified22101.certificate.forward).symm,
          certified22101.exact_profile⟩
      · exact ⟨certified22102.card_start, certified22102.card_finish,
          certified22102.disjoint,
          (allModeMovePath_preserves_evaluation
            certified22102.certificate.forward).symm,
          certified22102.exact_profile⟩
      · exact ⟨certified22103.card_start, certified22103.card_finish,
          certified22103.disjoint,
          (allModeMovePath_preserves_evaluation
            certified22103.certificate.forward).symm,
          certified22103.exact_profile⟩
  | family411 =>
      fin_cases index
      exact ⟨certified41101.card_start, certified41101.card_finish,
        certified41101.disjoint,
        (allModeMovePath_preserves_evaluation
          certified41101.certificate.forward).symm,
        certified41101.exact_profile⟩
  | family321 =>
      fin_cases index
      · exact ⟨certified32101.card_start, certified32101.card_finish,
          certified32101.disjoint,
          (allModeMovePath_preserves_evaluation
            certified32101.certificate.forward).symm,
          certified32101.exact_profile⟩
      · exact ⟨certified32102.card_start, certified32102.card_finish,
          certified32102.disjoint,
          (allModeMovePath_preserves_evaluation
            certified32102.certificate.forward).symm,
          certified32102.exact_profile⟩
      · exact ⟨certified32103.card_start, certified32103.card_finish,
          certified32103.disjoint,
          (allModeMovePath_preserves_evaluation
            certified32103.certificate.forward).symm,
          certified32103.exact_profile⟩
      · exact ⟨certified32104.card_start, certified32104.card_finish,
          certified32104.disjoint,
          (allModeMovePath_preserves_evaluation
            certified32104.certificate.forward).symm,
          certified32104.exact_profile⟩
      · exact ⟨certified32105.card_start, certified32105.card_finish,
          certified32105.disjoint,
          (allModeMovePath_preserves_evaluation
            certified32105.certificate.forward).symm,
          certified32105.exact_profile⟩
      · exact ⟨certified32106.card_start, certified32106.card_finish,
          certified32106.disjoint,
          (allModeMovePath_preserves_evaluation
            certified32106.certificate.forward).symm,
          certified32106.exact_profile⟩
  | family222 =>
      fin_cases index
      · exact ⟨certified22201.card_start, certified22201.card_finish,
          certified22201.disjoint,
          (allModeMovePath_preserves_evaluation
            certified22201.certificate.forward).symm,
          certified22201.exact_profile⟩
      · exact ⟨certified22202.card_start, certified22202.card_finish,
          certified22202.disjoint,
          (allModeMovePath_preserves_evaluation
            certified22202.certificate.forward).symm,
          certified22202.exact_profile⟩
      · exact ⟨certified22203.card_start, certified22203.card_finish,
          certified22203.disjoint,
          (allModeMovePath_preserves_evaluation
            certified22203.certificate.forward).symm,
          certified22203.exact_profile⟩

/-- The selected replay-row endpoints, packaged as a semantic exact relation. -/
def OrbitLabel.selectedExactRelation (label : OrbitLabel) :
    ExactRelation label.1.profile :=
  ⟨label.selectedEndpoints, selectedEndpoints_isExactRelation label⟩

example :
    (OrbitLabel.selectedExactRelation
      (⟨.family221, (0 : Fin 3)⟩ : OrbitLabel)).1 =
        OrbitLabel.selectedEndpoints
          (⟨.family221, (0 : Fin 3)⟩ : OrbitLabel) := rfl

/-- Semantic membership in a selected-row orbit.  A witness consists of an
arbitrary orientation of the input profile to the label's canonical family
and an arbitrary checked factorwise-GL/mode-permutation action taking that
selected row to the oriented ordered endpoints. -/
def InOrbit (label : OrbitLabel) {p : Profile}
    (target : RelationEndpoints p) : Prop :=
  ∃ (choice : ProfileOrientation p), ∃ hfamily : label.1 = choice.family,
    Nonempty (ActionWitness
      (cast (congrArg (fun family => RelationEndpoints family.profile) hfamily)
        (OrbitLabel.selectedEndpoints label))
      (⟨choice.orientState target.left, choice.orientState target.right⟩ :
        RelationEndpoints choice.family.profile))

/-- Casting both endpoint slots through a profile equality leaves the relation
pair-count invariant unchanged. -/
theorem relationInvariant_castEndpoints {p q : Profile} (h : p = q)
    (R : RelationEndpoints p) :
    relationInvariant (cast (congrArg RelationEndpoints h) R) =
      relationInvariant R := by
  subst q
  rfl

/-- Semantic orbit membership forces the input invariant to equal the
invariant computed directly from the selected replay row. -/
theorem selectedInvariant_eq_of_inOrbit (label : OrbitLabel) {p : Profile}
    (target : RelationEndpoints p) (hmembership : InOrbit label target) :
    relationInvariant (OrbitLabel.selectedEndpoints label) =
      relationInvariant target := by
  rcases hmembership with ⟨choice, hfamily, ⟨witness⟩⟩
  have hprofile : label.1.profile = choice.family.profile :=
    congrArg CanonicalProfileFamily.profile hfamily
  have hcast : relationInvariant
      (cast (congrArg RelationEndpoints hprofile)
        (OrbitLabel.selectedEndpoints label)) =
        relationInvariant (OrbitLabel.selectedEndpoints label) :=
    relationInvariant_castEndpoints hprofile (OrbitLabel.selectedEndpoints label)
  have hwitness : relationInvariant
      (cast (congrArg RelationEndpoints hprofile)
        (OrbitLabel.selectedEndpoints label)) =
        relationInvariant
          (⟨choice.orientState target.left, choice.orientState target.right⟩ :
            RelationEndpoints choice.family.profile) :=
    relationInvariant_actionWitness witness
  have horient : relationInvariant
      (⟨choice.orientState target.left, choice.orientState target.right⟩ :
        RelationEndpoints choice.family.profile) = relationInvariant target :=
    relationInvariant_orient choice target
  exact hcast.symm.trans (hwitness.trans horient)

/-- Memberships of the same relation in two selected-row orbits have the same
canonical family, independently of which valid orientations were chosen. -/
theorem family_eq_of_inOrbit {first second : OrbitLabel} {p : Profile}
    {target : RelationEndpoints p} (hfirst : InOrbit first target)
    (hsecond : InOrbit second target) : first.1 = second.1 := by
  rcases hfirst with ⟨firstChoice, hfirstFamily, _⟩
  rcases hsecond with ⟨secondChoice, hsecondFamily, _⟩
  exact hfirstFamily.trans
    ((profileOrientation_family_unique firstChoice secondChoice).trans
      hsecondFamily.symm)

/-- A semantic exact normalized relation belongs to at least one of the
thirteen selected-row orbits.  Existence is extracted from the closed coverage
compiler, while the resulting proposition mentions only semantic witnesses. -/
theorem exists_orbitLabel {p : Profile} (target : ExactRelation p) :
    ∃ label : OrbitLabel, InOrbit label target.1 := by
  let compiled := compileNormalized target
  let label : OrbitLabel :=
    ⟨compiled.choice.family, compiled.selectedRowIndex⟩
  refine ⟨label, compiled.choice, rfl, ⟨?_⟩⟩
  exact compiled.witness

/-- A semantic exact normalized relation cannot belong to two different
selected-row orbit labels.  Cross-family equality follows from the exact
profile orientation; within a family, the kernel-checked pair counts separate
all selected rows. -/
theorem orbitLabel_unique {p : Profile} (target : ExactRelation p)
    {first second : OrbitLabel} (hfirst : InOrbit first target.1)
    (hsecond : InOrbit second target.1) : first = second := by
  rcases first with ⟨firstFamily, firstIndex⟩
  rcases second with ⟨secondFamily, secondIndex⟩
  have hfamily : firstFamily = secondFamily :=
    family_eq_of_inOrbit hfirst hsecond
  subst secondFamily
  have hfirstInvariant :=
    selectedInvariant_eq_of_inOrbit ⟨firstFamily, firstIndex⟩ target.1 hfirst
  have hsecondInvariant :=
    selectedInvariant_eq_of_inOrbit ⟨firstFamily, secondIndex⟩ target.1 hsecond
  have hindex : firstIndex = secondIndex :=
    selectedRowInvariant_injective firstFamily
      (hfirstInvariant.trans hsecondInvariant.symm)
  subst secondIndex
  rfl

/-- Every semantic exact normalized binary relation has exactly one of the
thirteen semantic orbit labels. -/
theorem everyExactRelation_has_unique_orbitLabel {p : Profile}
    (target : ExactRelation p) :
    ∃! label : OrbitLabel, InOrbit label target.1 := by
  obtain ⟨label, hlabel⟩ := exists_orbitLabel target
  refine ⟨label, hlabel, ?_⟩
  intro other hother
  exact orbitLabel_unique target hother hlabel

/-- The label selected by the closed compiler, retained only as Type-valued
family and replay-row data. -/
def compiledOrbitLabel {p : Profile} {target : ExactRelation p}
    (compiled : CompilationResult target) : OrbitLabel :=
  ⟨compiled.choice.family, compiled.selectedRowIndex⟩

example {p : Profile} {target : ExactRelation p}
    (compiled : CompilationResult target) :
    (compiledOrbitLabel compiled).1 = compiled.choice.family := rfl

/-- Enhanced proof-producing compilation: the existing compilation (including
both concrete paths) together with semantic orbit membership and a proof that
no other one of the thirteen labels can contain the input. -/
structure ClassifiedCompilation {p : Profile} (target : ExactRelation p) : Type where
  /-- The closed compiler output, retaining its action witness and certificate. -/
  compilation : CompilationResult target
  /-- Semantic membership in the orbit named by the compilation's row data. -/
  membership : InOrbit (compiledOrbitLabel compilation) target.1
  /-- Any semantic selected-row orbit membership has the same label. -/
  unique : ∀ label : OrbitLabel, InOrbit label target.1 →
    label = compiledOrbitLabel compilation

/-- The unique semantic label returned by an enhanced compilation. -/
def ClassifiedCompilation.label {p : Profile} {target : ExactRelation p}
    (compiled : ClassifiedCompilation target) : OrbitLabel :=
  compiledOrbitLabel compiled.compilation

/-- The existing transported five-circuit certificate, containing both bounded
all-mode paths, is retained by the enhanced compilation. -/
def ClassifiedCompilation.certificate {p : Profile} {target : ExactRelation p}
    (compiled : ClassifiedCompilation target) :
    FiveCircuitCertificate p target.1.left target.1.right :=
  compiled.compilation.certificate

/-- Compile an exact normalized relation and attach its unique semantic label
certificate without changing either existing path. -/
def compileClassified {p : Profile} (target : ExactRelation p) :
    ClassifiedCompilation target := by
  let compilation := compileNormalized target
  have hmembership : InOrbit (compiledOrbitLabel compilation) target.1 := by
    refine ⟨compilation.choice, rfl, ⟨?_⟩⟩
    exact compilation.witness
  exact {
    compilation := compilation
    membership := hmembership
    unique := fun label hlabel => orbitLabel_unique target hlabel hmembership
  }

/-- Compiling the exact representative attached to a label recovers that
label.  Thus compiler labels are not merely an upper bound on the semantic
classes. -/
theorem compileClassified_selectedExactRelation_label (label : OrbitLabel) :
    (compileClassified label.selectedExactRelation).label = label := by
  rcases label with ⟨family, index⟩
  cases family with
  | family221 =>
      let target := OrbitLabel.selectedExactRelation
        (⟨.family221, index⟩ : OrbitLabel)
      let classified := compileClassified target
      have hinvariant := selectedInvariant_eq_of_inOrbit classified.label
        target.1 classified.membership
      have hindex : classified.label.2 = index :=
        selectedRowInvariant_injective .family221 hinvariant
      apply Sigma.ext
      · rfl
      · exact heq_of_eq hindex
  | family411 =>
      let target := OrbitLabel.selectedExactRelation
        (⟨.family411, index⟩ : OrbitLabel)
      let classified := compileClassified target
      have hinvariant := selectedInvariant_eq_of_inOrbit classified.label
        target.1 classified.membership
      have hindex : classified.label.2 = index :=
        selectedRowInvariant_injective .family411 hinvariant
      apply Sigma.ext
      · rfl
      · exact heq_of_eq hindex
  | family321 =>
      let target := OrbitLabel.selectedExactRelation
        (⟨.family321, index⟩ : OrbitLabel)
      let classified := compileClassified target
      have hinvariant := selectedInvariant_eq_of_inOrbit classified.label
        target.1 classified.membership
      have hindex : classified.label.2 = index :=
        selectedRowInvariant_injective .family321 hinvariant
      apply Sigma.ext
      · rfl
      · exact heq_of_eq hindex
  | family222 =>
      let target := OrbitLabel.selectedExactRelation
        (⟨.family222, index⟩ : OrbitLabel)
      let classified := compileClassified target
      have hinvariant := selectedInvariant_eq_of_inOrbit classified.label
        target.1 classified.membership
      have hindex : classified.label.2 = index :=
        selectedRowInvariant_injective .family222 hinvariant
      apply Sigma.ext
      · rfl
      · exact heq_of_eq hindex

/-- Every one of the thirteen labels is inhabited by its selected exact
replay-row relation. -/
theorem selectedExactRelation_inOrbit (label : OrbitLabel) :
    InOrbit label label.selectedExactRelation.1 := by
  have hlabel := compileClassified_selectedExactRelation_label label
  exact Eq.mp
    (congrArg (fun candidate : OrbitLabel =>
      InOrbit candidate label.selectedExactRelation.1) hlabel)
    (compileClassified label.selectedExactRelation).membership


/-- Every public orbit label is realized by a semantic exact relation of its
canonical profile. -/
theorem everyOrbitLabel_realized (label : OrbitLabel) :
    ∃ target : ExactRelation label.1.profile, InOrbit label target.1 :=
  ⟨label.selectedExactRelation, selectedExactRelation_inOrbit label⟩

/-- The normalized compiler label is surjective onto all thirteen public
semantic orbit labels. -/
theorem compileClassified_label_surjective (label : OrbitLabel) :
    ∃ target : ExactRelation label.1.profile,
      (compileClassified target).label = label :=
  ⟨label.selectedExactRelation,
    compileClassified_selectedExactRelation_label label⟩

/-- There are exactly thirteen realized semantic orbit labels: the label type
has cardinality thirteen, every exact relation has a unique label, and every
label has an exact representative. -/
theorem exactly_thirteen_orbitLabels :
    Fintype.card OrbitLabel = 13 ∧
      (∀ {p : Profile} (target : ExactRelation p),
        ∃! label : OrbitLabel, InOrbit label target.1) ∧
      (∀ label : OrbitLabel,
        ∃ target : ExactRelation label.1.profile, InOrbit label target.1) := by
  exact ⟨orbitLabel_card, everyExactRelation_has_unique_orbitLabel,
    everyOrbitLabel_realized⟩

/-- The first selected replay-row label in canonical profile `221`. -/
def orbitLabel22101 : OrbitLabel := ⟨.family221, (0 : Fin 3)⟩

example : orbitLabel22101.1 = .family221 := rfl
example : OrbitLabel.selectedEndpoints orbitLabel22101 =
    ⟨row22101Start, row22101Finish⟩ := rfl

/-- The certified `221-01` replay endpoints, packaged as a concrete exact
relation.  This gives a joint model of every exactness hypothesis consumed by
the semantic classifier. -/
def certified22101ExactRelation : ExactRelation profile221 :=
  ⟨⟨row22101Start, row22101Finish⟩,
    certified22101.card_start,
    certified22101.card_finish,
    certified22101.disjoint,
    (allModeMovePath_preserves_evaluation certified22101.certificate.forward).symm,
    certified22101.exact_profile⟩

example : certified22101ExactRelation.1.left = row22101Start := rfl
example : certified22101ExactRelation.1.right = row22101Finish := rfl
example : IsExactRelation certified22101ExactRelation.1 :=
  certified22101ExactRelation.2

/-- Concrete jointly satisfiable regression: row `221-01` is an exact
relation, compiles to the first `221` orbit label, has semantic membership only
in that label, and retains checked paths in both directions. -/
theorem certified22101_classified_regression :
    let target := certified22101ExactRelation
    let classified := compileClassified target
    let expected : OrbitLabel := orbitLabel22101
    classified.label = expected ∧
      InOrbit expected target.1 ∧
      (∀ label : OrbitLabel, InOrbit label target.1 → label = expected) ∧
      Nonempty (MovePath (@AllModeMove profile221)
        target.1.left target.1.right) ∧
      Nonempty (MovePath (@AllModeMove profile221)
        target.1.right target.1.left) := by
  dsimp only
  let classified := compileClassified certified22101ExactRelation
  let expected : OrbitLabel := orbitLabel22101
  have hinvariant := selectedInvariant_eq_of_inOrbit classified.label
    certified22101ExactRelation.1 classified.membership
  have hindex : classified.label.2 = (0 : Fin 3) :=
    selectedRowInvariant_injective .family221 hinvariant
  have hlabel : classified.label = expected := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq hindex
  refine ⟨hlabel, ?_, ?_, ⟨classified.certificate.forward⟩,
    ⟨classified.certificate.reverse⟩⟩
  · change InOrbit expected certified22101ExactRelation.1
    rw [← hlabel]
    exact classified.membership
  · intro label hmembership
    exact (classified.unique label hmembership).trans hlabel

example {p : Profile} (target : ExactRelation p) :
    InOrbit (compileClassified target).label target.1 ∧
      Nonempty (MovePath (@AllModeMove p) target.1.left target.1.right) ∧
      Nonempty (MovePath (@AllModeMove p) target.1.right target.1.left) := by
  exact ⟨(compileClassified target).membership,
    ⟨(compileClassified target).certificate.forward⟩,
    ⟨(compileClassified target).certificate.reverse⟩⟩

#check @everyOrbitLabel_realized
#check @compileClassified_label_surjective
#check @exactly_thirteen_orbitLabels
#print axioms orbitLabelDecidableEq
#print axioms selectedEndpoints_isExactRelation
#print axioms compileClassified_selectedExactRelation_label
#print axioms selectedExactRelation_inOrbit
#print axioms everyOrbitLabel_realized
#print axioms compileClassified_label_surjective
#print axioms exactly_thirteen_orbitLabels

#check @profileKey_perm
#check @familyProfileKey_injective
#check @profileOrientation_family_unique
#check @orbitLabel_card
#check @InOrbit
#check @selectedInvariant_eq_of_inOrbit
#check @family_eq_of_inOrbit
#check @exists_orbitLabel
#check @orbitLabel_unique
#check @everyExactRelation_has_unique_orbitLabel
#check @ClassifiedCompilation.certificate
#check @compileClassified
#check @orbitLabel22101
#check @certified22101ExactRelation
#check @certified22101_classified_regression

#print axioms profileOrientation_family_unique
#print axioms orbitLabel_card
#print axioms selectedInvariant_eq_of_inOrbit
#print axioms exists_orbitLabel
#print axioms orbitLabel_unique
#print axioms everyExactRelation_has_unique_orbitLabel
#print axioms compileClassified
#print axioms certified22101_classified_regression

end BilinearComplexity.NormalizedBinaryOrbitClassification
