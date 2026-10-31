/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.Zorn.G2FlagCellQuotientWitness
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2ResidualCoordinateCellOne
import InfoGeometry.Algebra.Zorn.G2FactorizationAlignmentCertificate

namespace InfoGeometry.Algebra.Zorn.G2QuotientCollisionAudit

open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2ResidualCoordinateCellOne
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity
open InfoGeometry.Algebra.Zorn.G2FactorizationAlignmentCertificate
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem quotientRepresentative_24_eq_45 :
    quotientRepresentative 24 = quotientRepresentative 45 := by
  obtain ⟨e, he⟩ : ∃ e : PCWordExp,
      autMatrix ((flagRepresentative 24)⁻¹ * flagRepresentative 45) =
        autMatrix (pcWord e) := by
    decide
  exact quotientRepresentative_eq_of_pc_matrix_factor 24 45 e he

theorem quotient_collision_not_residual_coordinate_alignment :
    quotientRepresentative 24 = quotientRepresentative 45 ∧
      InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity.residualWord 1 24 ≠
        InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity.residualWord 1 45 :=
  ⟨quotientRepresentative_24_eq_45, by decide⟩

theorem quotientRepresentative_not_injective :
    ¬ Function.Injective quotientRepresentative := by
  intro hinj
  have hindex : (24 : Fin 189) = 45 :=
    hinj quotientRepresentative_24_eq_45
  omega

/-- The full factorization/alignment package cannot coexist with the concrete
collision above: its residual-alignment and within-cell injectivity fields
would force `quotientRepresentative` to be injective. -/
theorem no_factorization_alignment_system :
    ¬ Nonempty FactorizationAlignmentSystem := by
  rintro ⟨C⟩
  have hinj := quotientRepresentative_injective C
  exact quotientRepresentative_not_injective hinj

/-- The concrete-generator variant of the alignment package is likewise
inconsistent with the exhibited quotient collision. -/
theorem no_concrete_factorization_alignment_system :
    ¬ Nonempty ConcreteFactorizationAlignmentSystem := by
  rintro ⟨C⟩
  have hinj := concrete_quotientRepresentative_injective C
  exact quotientRepresentative_not_injective hinj

end InfoGeometry.Algebra.Zorn.G2QuotientCollisionAudit
