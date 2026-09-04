import BilinearComplexity.NormalizedBinaryAllModeMoveTransport

set_option autoImplicit false

/-!
# Bounded normalized binary five-circuit certificates

This module gives the narrow proof-facing certificate for a disjoint two-term
and three-term endpoint pair.  A certificate contains concrete forward and
reverse `AllModeMove` paths, the requested length and altitude bounds, and
linear-span confinement in each factor mode.

Factor-span confinement is deliberately different from finite term-set
confinement.  It allows an intermediate term not occurring at either endpoint,
provided each of its factors lies in the corresponding endpoint-generated
linear span.  No executable move encoding, census, orbit coverage,
normalization, or reflection result is asserted here.

AI disclosure: produced with AI assistance (see `README`).
-/

namespace BilinearComplexity.NormalizedBinaryFiveCircuitCertificate

open BinaryCircuit
open NormalizedBinaryCarrier
open NormalizedBinaryReplay221
open NormalizedBinaryMoveTransport
open NormalizedBinaryAllModeMove
open NormalizedBinaryAllModeMoveTransport

/-- The linear span of the first factors occurring in a normalized state. -/
def firstFactorSpan {p : Profile} (D : State p) :
    Submodule F2 (CoordinateVector p.first) :=
  Submodule.span F2 ((D.image (fun t => t.1.1) : Finset _) : Set _)

/-- The linear span of the second factors occurring in a normalized state. -/
def secondFactorSpan {p : Profile} (D : State p) :
    Submodule F2 (CoordinateVector p.second) :=
  Submodule.span F2 ((D.image (fun t => t.2.1.1) : Finset _) : Set _)

/-- The linear span of the third factors occurring in a normalized state. -/
def thirdFactorSpan {p : Profile} (D : State p) :
    Submodule F2 (CoordinateVector p.third) :=
  Submodule.span F2 ((D.image (fun t => t.2.2.1) : Finset _) : Set _)

example (p : Profile) : firstFactorSpan (∅ : State p) = ⊥ := by
  simp [firstFactorSpan]

example (p : Profile) : secondFactorSpan (∅ : State p) = ⊥ := by
  simp [secondFactorSpan]

example (p : Profile) : thirdFactorSpan (∅ : State p) = ⊥ := by
  simp [thirdFactorSpan]

/-- `X` is factor-span confined by `K` when each projected factor span of `X`
is contained in the corresponding projected factor span of `K`.  This does
not require the finite term-set inclusion `X ⊆ K`. -/
def FactorSpanConfined {p : Profile} (K X : State p) : Prop :=
  firstFactorSpan X ≤ firstFactorSpan K ∧
    secondFactorSpan X ≤ secondFactorSpan K ∧
    thirdFactorSpan X ≤ thirdFactorSpan K

example {p : Profile} (D : State p) : FactorSpanConfined D D :=
  ⟨le_rfl, le_rfl, le_rfl⟩

/-- A path is factor-span confined by `K` when every actual path vertex is
factor-span confined by `K`.  This is linear-span confinement, not containment
of every vertex in the finite term set `K`. -/
def PathFactorSpanConfined {p : Profile}
    {R : State p → State p → Prop} {D E : State p}
    (path : MovePath R D E) (K : State p) : Prop :=
  ∀ X, PathVertex path X → FactorSpanConfined K X

example {p : Profile} (D : State p) :
    PathFactorSpanConfined
      (.singleton D : MovePath (@AllModeMove p) D D) D := by
  intro X hX
  have hXD : X = D := by
    simpa only [PathVertex, MovePath.vertices, List.mem_singleton] using hX
  rw [hXD]
  exact ⟨le_rfl, le_rfl, le_rfl⟩

/-- A normalized state has its exact ambient factor profile when its three
projected factor spans are the full coordinate spaces.  This is a future row
predicate and is not required of a transport-stable certificate. -/
def HasExactFactorProfile {p : Profile} (D : State p) : Prop :=
  firstFactorSpan D = ⊤ ∧
    secondFactorSpan D = ⊤ ∧
    thirdFactorSpan D = ⊤

/-- Mapping a state maps its first factor span by the induced linear map. -/
theorem firstFactorSpan_mapState {p q : Profile}
    (f : FactorwiseAdditiveInjection p q) (D : State p) :
    firstFactorSpan (mapState f D) =
      Submodule.map (f.first.toZModLinearMap 2) (firstFactorSpan D) := by
  unfold firstFactorSpan
  have hprojection :
      (mapState f D).image (fun t => t.1.1) =
        (D.image (fun t => t.1.1)).image f.first := by
    simp only [mapState, Finset.image_image]
    rfl
  rw [hprojection, Finset.coe_image]
  change Submodule.span F2
      ((f.first.toZModLinearMap 2 : CoordinateVector p.first →
          CoordinateVector q.first) ''
        ((D.image (fun t => t.1.1) : Finset _) : Set _)) = _
  rw [← LinearMap.map_span]

/-- Mapping a state maps its second factor span by the induced linear map. -/
theorem secondFactorSpan_mapState {p q : Profile}
    (f : FactorwiseAdditiveInjection p q) (D : State p) :
    secondFactorSpan (mapState f D) =
      Submodule.map (f.second.toZModLinearMap 2) (secondFactorSpan D) := by
  unfold secondFactorSpan
  have hprojection :
      (mapState f D).image (fun t => t.2.1.1) =
        (D.image (fun t => t.2.1.1)).image f.second := by
    simp only [mapState, Finset.image_image]
    rfl
  rw [hprojection, Finset.coe_image]
  change Submodule.span F2
      ((f.second.toZModLinearMap 2 : CoordinateVector p.second →
          CoordinateVector q.second) ''
        ((D.image (fun t => t.2.1.1) : Finset _) : Set _)) = _
  rw [← LinearMap.map_span]

/-- Mapping a state maps its third factor span by the induced linear map. -/
theorem thirdFactorSpan_mapState {p q : Profile}
    (f : FactorwiseAdditiveInjection p q) (D : State p) :
    thirdFactorSpan (mapState f D) =
      Submodule.map (f.third.toZModLinearMap 2) (thirdFactorSpan D) := by
  unfold thirdFactorSpan
  have hprojection :
      (mapState f D).image (fun t => t.2.2.1) =
        (D.image (fun t => t.2.2.1)).image f.third := by
    simp only [mapState, Finset.image_image]
    rfl
  rw [hprojection, Finset.coe_image]
  change Submodule.span F2
      ((f.third.toZModLinearMap 2 : CoordinateVector p.third →
          CoordinateVector q.third) ''
        ((D.image (fun t => t.2.2.1) : Finset _) : Set _)) = _
  rw [← LinearMap.map_span]

/-- Factor-span confinement is preserved by an ordered factorwise additive
injection. -/
theorem FactorSpanConfined.map {p q : Profile}
    (f : FactorwiseAdditiveInjection p q) {K X : State p}
    (h : FactorSpanConfined K X) :
    FactorSpanConfined (mapState f K) (mapState f X) := by
  rw [FactorSpanConfined, firstFactorSpan_mapState,
    firstFactorSpan_mapState, secondFactorSpan_mapState,
    secondFactorSpan_mapState, thirdFactorSpan_mapState,
    thirdFactorSpan_mapState]
  exact ⟨Submodule.map_mono h.1, Submodule.map_mono h.2.1,
    Submodule.map_mono h.2.2⟩

/-- Factor-span confinement of an all-mode path is preserved by factorwise
path transport. -/
theorem PathFactorSpanConfined.map {p q : Profile}
    (f : FactorwiseAdditiveInjection p q) {D E K : State p}
    {path : MovePath (@AllModeMove p) D E}
    (h : PathFactorSpanConfined path K) :
    PathFactorSpanConfined (mapAllModePath f path) (mapState f K) := by
  intro Y hY
  obtain ⟨X, hX, hXY⟩ :=
    (mapAllModePath_pathVertex_iff f path Y).mp hY
  rw [← hXY]
  exact (h X hX).map f

/-- A bounded bidirectional all-mode replay for disjoint two-term and
three-term endpoints.  Its confinement fields control factor spans and do not
assert containment in the finite endpoint term set. -/
structure FiveCircuitCertificate (p : Profile) (A B : State p) : Type where
  /-- The two endpoint states have no common normalized term. -/
  disjoint : Disjoint A B
  /-- The left endpoint has exactly two terms. -/
  card_left : A.card = 2
  /-- The right endpoint has exactly three terms. -/
  card_right : B.card = 3
  /-- A concrete all-mode path from the two-term endpoint to the three-term endpoint. -/
  forward : MovePath (@AllModeMove p) A B
  /-- A concrete all-mode path from the three-term endpoint to the two-term endpoint. -/
  reverse : MovePath (@AllModeMove p) B A
  /-- The forward path has at most three edges. -/
  forward_length_le : forward.length ≤ 3
  /-- The reverse path has at most three edges. -/
  reverse_length_le : reverse.length ≤ 3
  /-- Every forward vertex has at most four terms. -/
  forward_altitude_le : forward.altitude ≤ 4
  /-- Every reverse vertex has at most four terms. -/
  reverse_altitude_le : reverse.altitude ≤ 4
  /-- Every forward vertex is confined to the endpoint-generated factor spans. -/
  forward_confined : PathFactorSpanConfined forward (A ∪ B)
  /-- Every reverse vertex is confined to the endpoint-generated factor spans. -/
  reverse_confined : PathFactorSpanConfined reverse (A ∪ B)

/-- The endpoint union of a five-circuit certificate is a normalized binary
circuit. -/
theorem FiveCircuitCertificate.circuit {p : Profile} {A B : State p}
    (cert : FiveCircuitCertificate p A B) :
    Circuit (@tensorEvaluation p) (A ∪ B) := by
  apply tensorEvaluation_circuit_union_of_disjoint_card_two_card_three
    cert.disjoint cert.card_left cert.card_right
  exact (allModeMovePath_preserves_evaluation cert.forward).symm

/-- A five-circuit certificate transports along an ordered factorwise additive
injection, retaining both concrete paths, both bounds, and factor-span
confinement. -/
def FiveCircuitCertificate.map {p q : Profile} {A B : State p}
    (cert : FiveCircuitCertificate p A B)
    (f : FactorwiseAdditiveInjection p q) :
    FiveCircuitCertificate q (mapState f A) (mapState f B) where
  disjoint := (Finset.disjoint_image (mapTerm_injective f)).mpr cert.disjoint
  card_left := (mapState_card f A).trans cert.card_left
  card_right := (mapState_card f B).trans cert.card_right
  forward := mapAllModePath f cert.forward
  reverse := mapAllModePath f cert.reverse
  forward_length_le := by
    rw [mapAllModePath_length]
    exact cert.forward_length_le
  reverse_length_le := by
    rw [mapAllModePath_length]
    exact cert.reverse_length_le
  forward_altitude_le := by
    rw [mapAllModePath_altitude]
    exact cert.forward_altitude_le
  reverse_altitude_le := by
    rw [mapAllModePath_altitude]
    exact cert.reverse_altitude_le
  forward_confined := by
    simpa only [mapState_union] using cert.forward_confined.map f
  reverse_confined := by
    simpa only [mapState_union] using cert.reverse_confined.map f

/-- The forward path stored by a transported certificate is exactly the
factorwise image of the source certificate's forward path. -/
@[simp] theorem FiveCircuitCertificate.map_forward {p q : Profile}
    {A B : State p} (cert : FiveCircuitCertificate p A B)
    (f : FactorwiseAdditiveInjection p q) :
    (cert.map f).forward = mapAllModePath f cert.forward :=
  rfl

private theorem movePath_mono_vertices {p : Profile}
    {R S : State p → State p → Prop}
    (hRS : ∀ {X Y}, R X Y → S X Y) {D E : State p}
    (path : MovePath R D E) :
    (path.mono hRS).vertices = path.vertices := by
  induction path with
  | singleton => simp only [MovePath.mono, MovePath.vertices]
  | snoc path _ ih =>
      simp only [MovePath.mono, MovePath.vertices, ih]

private theorem movePath_mono_length {p : Profile}
    {R S : State p → State p → Prop}
    (hRS : ∀ {X Y}, R X Y → S X Y) {D E : State p}
    (path : MovePath R D E) :
    (path.mono hRS).length = path.length := by
  induction path with
  | singleton => simp only [MovePath.mono, MovePath.length]
  | snoc path _ ih =>
      simp only [MovePath.mono, MovePath.length, ih]

private theorem movePath_mono_altitude {p : Profile}
    {R S : State p → State p → Prop}
    (hRS : ∀ {X Y}, R X Y → S X Y) {D E : State p}
    (path : MovePath R D E) :
    (path.mono hRS).altitude = path.altitude := by
  induction path with
  | singleton => simp only [MovePath.mono, MovePath.altitude]
  | snoc path _ ih =>
      simp only [MovePath.mono, MovePath.altitude, ih]

/-- The designated forward profile-`221` replay included in `AllModeMove`
through the identity orientation `abc`. -/
def replay221ForwardABC :
    MovePath (@AllModeMove profile221) S0 S2 :=
  forwardPath.mono fun h => allModeMove_of_move h

/-- The designated reverse profile-`221` replay included in `AllModeMove`
through the identity orientation `abc`. -/
def replay221ReverseABC :
    MovePath (@AllModeMove profile221) S2 S0 :=
  reversePath.mono fun h => allModeMove_of_move h

/-- The identity-orientation forward replay retains the three designated
vertices. -/
theorem replay221ForwardABC_vertices :
    replay221ForwardABC.vertices = [S0, S1, S2] := by
  rw [replay221ForwardABC, movePath_mono_vertices, forwardPath_vertices]

/-- The identity-orientation reverse replay retains the three designated
vertices in reverse order. -/
theorem replay221ReverseABC_vertices :
    replay221ReverseABC.vertices = [S2, S1, S0] := by
  rw [replay221ReverseABC, movePath_mono_vertices, reversePath_vertices]

/-- Both identity-orientation replays have exact length two and exact altitude
three. -/
theorem replay221ABC_path_metrics :
    replay221ForwardABC.length = 2 ∧
    replay221ReverseABC.length = 2 ∧
    replay221ForwardABC.altitude = 3 ∧
    replay221ReverseABC.altitude = 3 := by
  rw [replay221ForwardABC, replay221ReverseABC, movePath_mono_length,
    movePath_mono_length, movePath_mono_altitude, movePath_mono_altitude]
  exact path_metrics

private theorem designated_endpoint_firstFactorSpan_eq_top :
    firstFactorSpan (S0 ∪ S2) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  change Module.finrank F2
      (Submodule.span F2
        (((S0 ∪ S2).image (fun t => t.1.1) : Finset (Fin 2 → F2)) :
          Set (Fin 2 → F2))) = Module.finrank F2 (Fin 2 → F2)
  rw [designated_endpoint_exact_profile_221.2.2.2.1,
    Module.finrank_fin_fun]

private theorem designated_endpoint_secondFactorSpan_eq_top :
    secondFactorSpan (S0 ∪ S2) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  change Module.finrank F2
      (Submodule.span F2
        (((S0 ∪ S2).image (fun t => t.2.1.1) : Finset (Fin 2 → F2)) :
          Set (Fin 2 → F2))) = Module.finrank F2 (Fin 2 → F2)
  rw [designated_endpoint_exact_profile_221.2.2.2.2.1,
    Module.finrank_fin_fun]

private theorem designated_endpoint_thirdFactorSpan_eq_top :
    thirdFactorSpan (S0 ∪ S2) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  change Module.finrank F2
      (Submodule.span F2
        (((S0 ∪ S2).image (fun t => t.2.2.1) : Finset (Fin 1 → F2)) :
          Set (Fin 1 → F2))) = Module.finrank F2 (Fin 1 → F2)
  rw [designated_endpoint_exact_profile_221.2.2.2.2.2.1,
    Module.finrank_fin_fun]

/-- The designated endpoint union uses the full profile-`221` factor spaces. -/
theorem designated_endpoint_hasExactFactorProfile :
    HasExactFactorProfile (S0 ∪ S2) :=
  ⟨designated_endpoint_firstFactorSpan_eq_top,
    designated_endpoint_secondFactorSpan_eq_top,
    designated_endpoint_thirdFactorSpan_eq_top⟩

private theorem factorSpanConfined_by_designated_endpoints
    (X : State profile221) : FactorSpanConfined (S0 ∪ S2) X := by
  rw [FactorSpanConfined, designated_endpoint_firstFactorSpan_eq_top,
    designated_endpoint_secondFactorSpan_eq_top,
    designated_endpoint_thirdFactorSpan_eq_top]
  exact ⟨le_top, le_top, le_top⟩

/-- The existing designated `S0`/`S2` replay is one bounded bidirectional
profile-`221` certificate using `abc` all-mode edges.  This makes no census or
orbit-representativeness claim. -/
def designatedReplay221Certificate :
    FiveCircuitCertificate profile221 S0 S2 where
  disjoint := designated_endpoint_exact_profile_221.1
  card_left := state_cardinalities.1
  card_right := state_cardinalities.2.2
  forward := replay221ForwardABC
  reverse := replay221ReverseABC
  forward_length_le := by
    have hmetric := replay221ABC_path_metrics.1
    omega
  reverse_length_le := by
    have hmetric := replay221ABC_path_metrics.2.1
    omega
  forward_altitude_le := by
    have hmetric := replay221ABC_path_metrics.2.2.1
    omega
  reverse_altitude_le := by
    have hmetric := replay221ABC_path_metrics.2.2.2
    omega
  forward_confined := by
    intro X _hX
    exact factorSpanConfined_by_designated_endpoints X
  reverse_confined := by
    intro X _hX
    exact factorSpanConfined_by_designated_endpoints X

/-- The designated certificate recovers the already established circuit on
`S0 ∪ S2`. -/
theorem designatedReplay221Certificate_circuit :
    Circuit (@tensorEvaluation profile221) (S0 ∪ S2) :=
  designatedReplay221Certificate.circuit

#check @firstFactorSpan
#check @secondFactorSpan
#check @thirdFactorSpan
#check @FactorSpanConfined
#check @PathFactorSpanConfined
#check @HasExactFactorProfile
#check @firstFactorSpan_mapState
#check @secondFactorSpan_mapState
#check @thirdFactorSpan_mapState
#check @FactorSpanConfined.map
#check @PathFactorSpanConfined.map
#check @FiveCircuitCertificate
#check @FiveCircuitCertificate.circuit
#check @FiveCircuitCertificate.map
#check @replay221ForwardABC
#check @replay221ReverseABC
#check @designatedReplay221Certificate

#print axioms firstFactorSpan_mapState
#print axioms secondFactorSpan_mapState
#print axioms thirdFactorSpan_mapState
#print axioms FactorSpanConfined.map
#print axioms PathFactorSpanConfined.map
#print axioms FiveCircuitCertificate.circuit
#print axioms FiveCircuitCertificate.map
#print axioms designated_endpoint_hasExactFactorProfile
#print axioms designatedReplay221Certificate
#print axioms designatedReplay221Certificate_circuit

end BilinearComplexity.NormalizedBinaryFiveCircuitCertificate
