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
