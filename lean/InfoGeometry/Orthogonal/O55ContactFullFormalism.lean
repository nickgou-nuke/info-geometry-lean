import InfoGeometry.Orthogonal.O55ContactZeroGrade

/-!
# Full finite `so(5,5)` contact-multigrading formalism

This capstone combines the exact results proved by the focused owners:

* a nondegenerate split `(5,5)` form and its native orthogonal Lie algebra;
* the `|2|` contact grading and exact five-term reconstruction;
* source/target block bigrading and induced parity;
* two-step Heisenberg radicals and the degree-zero action;
* five Witt pairs and crosscap grade reversal;
* projective two-boundary selection rules;
* faithful action on a common CAR--CCR carrier;
* compatibility readouts with the repository's independent `Pin(5,5)` lane.

The generic Freudenthal/symplectic contact algebra on the parent branch is a
separate Lie algebra.  No equality or isomorphism between the two contact
constructions is asserted without an explicit intertwiner.
-/

noncomputable section

namespace InfoGeometry.Orthogonal.O55Contact

/-- Native multigrading and representation packet. -/
theorem o55_contact_multigrading_core
    {k l : ℤ} {A B : O55Lie}
    (hA : A ∈ contactGradeSpace k)
    (hB : B ∈ contactGradeSpace l) :
    ⁅A, B⁆ ∈ contactGradeSpace (k + l) ∧
      canonicalMultiDegree (k + l) =
        (canonicalMultiDegree k).add (canonicalMultiDegree l) ∧
      crosscapConjugation A ∈ contactGradeSpace (-k) ∧
      A = gradeMinusTwoProjection A +
        gradeMinusOneProjection A + gradeZeroProjection A +
        gradePlusOneProjection A + gradePlusTwoProjection A ∧
      IsRepresentedGrade k (commonAction A) ∧
      commonAction ⁅A, B⁆ = ⁅commonAction A, commonAction B⁆ := by
  exact ⟨contactGrade_bracket hA hB,
    (multigraded_bracket hA hB).2,
    crosscap_reverses_grade hA,
    five_grade_reconstruction A,
    commonRepresentation_preserves_grade hA,
    commonAction_bracket A B⟩

/-- The two nilpotent radicals and the degree-zero algebraic action. -/
theorem o55_contact_heisenberg_zero_core
    (a b c d : Outer2) (u v w z : Middle6) :
    ⁅negativeOneGenerator a u, negativeOneGenerator b v⁆ =
        (-(middlePairing u v * outerArea a b)) • gradeMinusTwo ∧
      ⁅positiveOneGenerator a u, positiveOneGenerator b v⁆ =
        (-(middlePairing u v * outerArea a b)) • gradePlusTwo ∧
      ⁅negativeTwoGenerator a b, negativeOneGenerator c w⁆ = 0 ∧
      ⁅positiveTwoGenerator a b, positiveOneGenerator c w⁆ = 0 ∧
      ⁅outerZeroGenerator a b, middleZeroGenerator u v⁆ = 0 ∧
      ⁅outerZeroGenerator a b, outerZeroGenerator c d⁆ =
        outerPairing b c • outerZeroGenerator a d -
          outerPairing a d • outerZeroGenerator c b ∧
      ⁅middleZeroGenerator u v, middleZeroGenerator w z⁆ =
        middlePairing v w • middleZeroGenerator u z -
        middlePairing u w • middleZeroGenerator v z -
        middlePairing v z • middleZeroGenerator u w +
        middlePairing u z • middleZeroGenerator v w := by
  exact ⟨negativeOne_bracket_scalar a b u v,
    positiveOne_bracket_scalar a b u v,
    negativeTwo_bracket_negativeOne a b c w,
    positiveTwo_bracket_positiveOne a b c w,
    outerZero_bracket_middleZero a b u v,
    outerZero_bracket a b c d,
    middleZero_bracket u v w z⟩

/-- Projective boundary selection and crosscap covariance. -/
theorem o55_contact_boundary_selection_core
    {a b k : ℤ} (B : BoundaryPair55) {A : O55Lie}
    (hv : IsKetWeight a B.ket)
    (hf : IsBraWeight b B.bra)
    (hA : A ∈ contactGradeSpace k) :
    (B.readout (A : End55) ≠ 0 → b - a = k) ∧
      IsKetWeight (-a) B.crosscap.ket ∧
      IsBraWeight (-b) B.crosscap.bra ∧
      crosscapConjugation A ∈ contactGradeSpace (-k) ∧
      B.crosscap.readout (crosscapConjugation A : End55) =
        B.readout (A : End55) := by
  rcases crosscap_selection_packet B hv hf hA with
    ⟨hket, hbra, hgrade, hread⟩
  exact ⟨fun hnonzero =>
      contact_degree_of_nonzero_readout B hv hf hA hnonzero,
    hket, hbra, hgrade, hread⟩

/-- Exact operator-envelope packet: native CAR, CCR, faithful Lie action,
contact-grade preservation and crosscap covariance. -/
theorem o55_contact_operator_envelope_core
    {k : ℤ} {A : O55Lie} (hA : A ∈ contactGradeSpace k) :
    fermionAnnihilation * fermionAnnihilation = 0 ∧
      fermionCreation * fermionCreation = 0 ∧
      fermionAnnihilation * fermionCreation +
        fermionCreation * fermionAnnihilation = 1 ∧
      bosonAnnihilation * bosonCreation -
        bosonCreation * bosonAnnihilation = 1 ∧
      Function.Injective commonRepresentation ∧
      IsRepresentedGrade k (commonAction A) ∧
      commonCrosscap * commonAction A * commonCrosscap =
        commonAction (crosscapConjugation A) ∧
      IsRepresentedGrade (-k)
        (commonCrosscap * commonAction A * commonCrosscap) ∧
      commonAction A * pointwiseLift fermionAnnihilation =
        pointwiseLift fermionAnnihilation * commonAction A ∧
      commonAction A * pointwiseLift fermionCreation =
        pointwiseLift fermionCreation * commonAction A ∧
      commonAction A * bosonCreation = bosonCreation * commonAction A ∧
      commonAction A * bosonAnnihilation = bosonAnnihilation * commonAction A := by
  exact ⟨fermionAnnihilation_sq,
    fermionCreation_sq,
    fermion_CAR,
    boson_CCR,
    commonRepresentation_injective,
    commonRepresentation_preserves_grade hA,
    commonCrosscap_conjugates_action A,
    commonCrosscap_reverses_represented_grade hA,
    common_commutes_fermionAnnihilation A,
    common_commutes_fermionCreation A,
    common_commutes_bosonCreation A,
    common_commutes_bosonAnnihilation A⟩

/-- Global finite structural census and independent Pin/null-sheet readout. -/
theorem o55_contact_structural_census :
    Fintype.card (Fin 10) = 10 ∧
      Nat.choose 10 2 = 45 ∧
      Fintype.card ContactGeneratorLabel = 45 ∧
      Fintype.card (ContactLaneLabel (-2)) = 1 ∧
      Fintype.card (ContactLaneLabel (-1)) = 12 ∧
      Fintype.card (ContactLaneLabel 0) = 19 ∧
      Fintype.card (ContactLaneLabel 1) = 12 ∧
      Fintype.card (ContactLaneLabel 2) = 1 ∧
      PinO55GlideReflection.crosscapOrientationSign = -1 ∧
      Clifford55.twisted_adj
          PinO55GlideReflection.crosscapReflectionPin55
          (Clifford55.n_pair PinO55GlideReflection.crosscapIndex) =
        -Clifford55.ι55
          (Clifford55.nbar_pair PinO55GlideReflection.crosscapIndex) ∧
      Clifford55.twisted_adj
          PinO55GlideReflection.crosscapReflectionPin55
          (Clifford55.nbar_pair PinO55GlideReflection.crosscapIndex) =
        -Clifford55.ι55
          (Clifford55.n_pair PinO55GlideReflection.crosscapIndex) := by
  rcases contact_lane_label_counts with ⟨h₂m, h₁m, h₀, h₁, h₂⟩
  exact ⟨carrier_and_generator_counts.1,
    carrier_and_generator_counts.2,
    contact_generator_label_count,
    h₂m, h₁m, h₀, h₁, h₂,
    pin_crosscap_orientation_sign,
    pin_crosscap_n_to_neg_nbar,
    pin_crosscap_nbar_to_neg_n⟩

/-- Final full-formalism packet.  The 45-label census is deliberately stated
as a coordinate-generator census; a native finrank/basis theorem for every
homogeneous submodule remains a separate theorem obligation. -/
theorem o55_contact_full_formalism_packet
    {k l : ℤ} {A B : O55Lie}
    (hA : A ∈ contactGradeSpace k)
    (hB : B ∈ contactGradeSpace l) :
    (∀ X : O55Lie,
      X = gradeMinusTwoProjection X +
        gradeMinusOneProjection X + gradeZeroProjection X +
        gradePlusOneProjection X + gradePlusTwoProjection X) ∧
      ⁅A, B⁆ ∈ contactGradeSpace (k + l) ∧
      crosscapConjugation A ∈ contactGradeSpace (-k) ∧
      IsRepresentedGrade k (commonAction A) ∧
      Function.Injective commonRepresentation ∧
      fermionAnnihilation * fermionCreation +
        fermionCreation * fermionAnnihilation = 1 ∧
      bosonAnnihilation * bosonCreation -
        bosonCreation * bosonAnnihilation = 1 ∧
      Fintype.card ContactGeneratorLabel = 45 := by
  exact ⟨five_grade_reconstruction,
    contactGrade_bracket hA hB,
    crosscap_reverses_grade hA,
    commonRepresentation_preserves_grade hA,
    commonRepresentation_injective,
    fermion_CAR,
    boson_CCR,
    contact_generator_label_count⟩

end InfoGeometry.Orthogonal.O55Contact
