/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Orthogonal.O55FullFormalismAll
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Orthogonal.O55ContactGradeDecomposition
import InfoGeometry.Orthogonal.O55ContactGrading
import InfoGeometry.Orthogonal.O55ContactCommonCrosscap
import InfoGeometry.Orthogonal.O55ContactCARCCRRepresentation
import InfoGeometry.Orthogonal.O55ContactGeneratorLabels
import InfoGeometry.Orthogonal.O55PinContactBridge
import InfoGeometry.Orthogonal.O55ContactHeisenberg
import InfoGeometry.Orthogonal.O55ContactMultiGrading
import InfoGeometry.Orthogonal.O55ContactZeroGrade

/-!
# Compatibility entry point for the O(5,5) contact formalism

The canonical implementation is owned by `O55FullFormalismAll`.  This module
keeps the upstream spelling available without copying or redefining any of
the contact, Clifford, multigrading, or two-boundary constructions.
-/


noncomputable section

namespace InfoGeometry.Orthogonal.O55Contact

/-- Native multigrading and representation packet. -/
theorem o55_contact_multigrading_core
    {k l : ℤ} {A B : O55Lie}
    (hA : A ∈ realContactGradeSpace k)
    (hB : B ∈ realContactGradeSpace l) :
    ⁅A, B⁆ ∈ realContactGradeSpace (k + l) ∧
      canonicalMultiDegree (k + l) =
        (canonicalMultiDegree k).add (canonicalMultiDegree l) ∧
      crosscapConjugation A ∈ realContactGradeSpace (-k) ∧
      A = gradeMinusTwoProjection A + gradeMinusOneProjection A + gradeZeroProjection A +
        gradePlusOneProjection A + gradePlusTwoProjection A ∧
      IsRepresentedGrade k (commonAction A) ∧
      commonAction ⁅A, B⁆ = ⁅commonAction A, commonAction B⁆ := by
  exact ⟨contactGrade_bracket hA hB, (multigraded_bracket hA hB).2,
    crosscap_reverses_grade hA, five_grade_reconstruction A,
    commonRepresentation_preserves_grade hA, commonAction_bracket A B⟩

/-- The two nilpotent radicals and the degree-zero algebraic action. -/
theorem o55_contact_heisenberg_zero_core
    (a b c d : Outer2) (u v w z : Middle6) :
    ⁅negativeOneGeneratorH a w, negativeOneGeneratorH b v⁆ =
        (-(middlePairing w v * outerArea a b)) • gradeMinusTwoH ∧
      ⁅positiveOneGeneratorH a u, positiveOneGeneratorH b v⁆ =
        (-(middlePairing u v * outerArea a b)) • gradePlusTwoH ∧
      ⁅negativeTwoGeneratorH a b, negativeOneGeneratorH c w⁆ = 0 ∧
      ⁅positiveTwoGeneratorH a b, positiveOneGeneratorH c w⁆ = 0 ∧
      ⁅outerZeroGenerator a b, middleZeroGenerator u v⁆ = 0 ∧
      ⁅outerZeroGenerator a b, outerZeroGenerator c d⁆ =
        outerPairing b c • outerZeroGenerator a d -
          outerPairing a d • outerZeroGenerator c b ∧
      ⁅middleZeroGenerator u v, middleZeroGenerator w z⁆ =
        middlePairing v w • middleZeroGenerator u z -
        middlePairing u w • middleZeroGenerator v z -
        middlePairing v z • middleZeroGenerator u w +
        middlePairing u z • middleZeroGenerator v w := by
  exact ⟨negativeOne_bracket_scalar a b w v, positiveOne_bracket_scalar a b u v,
    negativeTwo_bracket_negativeOne a b c w, positiveTwo_bracket_positiveOne a b c w,
    outerZero_bracket_middleZero a b u v, outerZero_bracket a b c d,
    middleZero_bracket u v w z⟩

/-- Projective boundary selection and crosscap covariance. -/
theorem o55_contact_boundary_selection_core
    {a b k : ℤ} (B : BoundaryPair55) {A : O55Lie}
    (hv : IsKetWeight a B.ket) (hf : IsBraWeight b B.bra)
    (hA : A ∈ realContactGradeSpace k) :
    (B.readout (A : End55) ≠ 0 → b - a = k) ∧
      IsKetWeight (-a) B.crosscap.ket ∧ IsBraWeight (-b) B.crosscap.bra ∧
      crosscapConjugation A ∈ realContactGradeSpace (-k) ∧
      B.crosscap.readout (crosscapConjugation A : End55) = B.readout (A : End55) := by
  rcases crosscap_selection_packet B hv hf hA with ⟨hket, hbra, hgrade, hread⟩
  exact ⟨fun hnonzero => contact_degree_of_nonzero_readout B hv hf hA hnonzero,
    hket, hbra, hgrade, hread⟩

/-- Exact operator-envelope packet. -/
theorem o55_contact_operator_envelope_core {k : ℤ} {A : O55Lie}
    (hA : A ∈ realContactGradeSpace k) :
    fermionAnnihilation * fermionAnnihilation = 0 ∧
      fermionCreation * fermionCreation = 0 ∧
      fermionAnnihilation * fermionCreation + fermionCreation * fermionAnnihilation = 1 ∧
      bosonAnnihilation * bosonCreation - bosonCreation * bosonAnnihilation = 1 ∧
      Function.Injective commonRepresentation ∧ IsRepresentedGrade k (commonAction A) ∧
      commonCrosscap * commonAction A * commonCrosscap = commonAction A ∧
      IsRepresentedGrade k (commonCrosscap * commonAction A * commonCrosscap) ∧
      commonAction A * pointwiseLift fermionAnnihilation =
        pointwiseLift fermionAnnihilation * commonAction A ∧
      commonAction A * pointwiseLift fermionCreation =
        pointwiseLift fermionCreation * commonAction A ∧
      commonAction A * bosonCreation = bosonCreation * commonAction A ∧
      commonAction A * bosonAnnihilation = bosonAnnihilation * commonAction A := by
  exact ⟨fermionAnnihilation_sq, fermionCreation_sq, fermion_CAR, boson_CCR,
    commonRepresentation_injective, commonRepresentation_preserves_grade hA,
    commonCrosscap_conjugates_action A, commonRepresentation_preserves_grade hA,
    common_commutes_fermionAnnihilation A, common_commutes_fermionCreation A,
    common_commutes_bosonCreation A, common_commutes_bosonAnnihilation A⟩

/-- Final full-formalism packet. -/
theorem o55_contact_full_formalism_packet
    {k l : ℤ} {A B : O55Lie}
    (hA : A ∈ realContactGradeSpace k) (hB : B ∈ realContactGradeSpace l) :
    (∀ X : O55Lie, X = gradeMinusTwoProjection X + gradeMinusOneProjection X +
        gradeZeroProjection X + gradePlusOneProjection X + gradePlusTwoProjection X) ∧
      ⁅A, B⁆ ∈ realContactGradeSpace (k + l) ∧
      crosscapConjugation A ∈ realContactGradeSpace (-k) ∧
      IsRepresentedGrade k (commonAction A) ∧
      Function.Injective commonRepresentation ∧
      fermionAnnihilation * fermionCreation + fermionCreation * fermionAnnihilation = 1 ∧
      bosonAnnihilation * bosonCreation - bosonCreation * bosonAnnihilation = 1 ∧
      Fintype.card ContactGeneratorLabel = 45 := by
  exact ⟨five_grade_reconstruction, contactGrade_bracket hA hB,
    crosscap_reverses_grade hA, commonRepresentation_preserves_grade hA,
    commonRepresentation_injective, fermion_CAR, boson_CCR,
    contact_generator_label_counts⟩

end InfoGeometry.Orthogonal.O55Contact
