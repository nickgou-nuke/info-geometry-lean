import InfoGeometry.Algebra.Zorn.G2FlagCellQuotientWitness
import InfoGeometry.Algebra.Zorn.G2ResidualCoordinateCellOne

namespace InfoGeometry.Algebra.Zorn.G2QuotientCollisionAudit

open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2ResidualCoordinateCellOne
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity
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

end InfoGeometry.Algebra.Zorn.G2QuotientCollisionAudit
