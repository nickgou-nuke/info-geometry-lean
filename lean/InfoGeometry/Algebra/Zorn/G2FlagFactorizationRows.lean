import InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2CASFactorizationProbe
import InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
import InfoGeometry.Algebra.Zorn.G2FlagRepresentativeBase
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylG2

namespace InfoGeometry.Algebra.Zorn.G2FlagFactorizationRows

/-! These are selected, independently checked rows.  They are not a uniform
    factorization theorem for the full `Fin 12 × Fin 189` table. -/

open InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagRepresentativeBase
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem row_0_0 :
    flagRepresentative 0 =
      collect (leftFactorWord 0 0) *
        weylNF (orbitWeyl 0).1 (orbitWeyl 0).2 *
          collect (rightFactorWord 0 0) := by
  rw [flagRepresentative_zero_eq_one]
  change 1 = 1 * weylNF 0 false * 1
  rw [weylNF_zero_false]
  simp

theorem row_1_24 :
    flagRepresentative 24 =
      collect (leftFactorWord 1 24) *
        weylNF (orbitWeyl 1).1 (orbitWeyl 1).2 *
          collect (rightFactorWord 1 24) := by
  have h := orbitCellAnchor_eq_weylNF 1
  change flagRepresentative 24 =
    1 * weylNF (orbitWeyl 1).1 (orbitWeyl 1).2 * 1
  simpa [orbitCellAnchor] using h

theorem row_4_6 :
    flagRepresentative 6 =
      collect (leftFactorWord 4 6) *
        weylNF (orbitWeyl 4).1 (orbitWeyl 4).2 *
          collect (rightFactorWord 4 6) := by
  have h := orbitCellAnchor_eq_weylNF 4
  change flagRepresentative 6 =
    1 * weylNF (orbitWeyl 4).1 (orbitWeyl 4).2 * 1
  simpa [orbitCellAnchor] using h

theorem row_4_18 :
    flagRepresentative 18 =
      collect (rightFactorWord 4 18) *
        weylNF (orbitWeyl 4).1 (orbitWeyl 4).2 *
          collect (leftFactorWord 4 18) := by
  apply autMatrix_injective
  decide

theorem row_1_45 :
    flagRepresentative 45 =
      collect (leftFactorWord 1 45) *
        weylNF (orbitWeyl 1).1 (orbitWeyl 1).2 *
          collect (rightFactorWord 1 45) := by
  exact InfoGeometry.Algebra.Zorn.G2CASFactorizationProbe.cell_one_45_factorization

theorem row_1_73_left_quotient_matrix :
    ∃ e : PCWordExp,
      autMatrix ((flagRepresentative 73)⁻¹ *
        (collect (leftFactorWord 1 73) *
          weylNF (orbitWeyl 1).1 (orbitWeyl 1).2)) =
        autMatrix (pcWord e) := by
  exact InfoGeometry.Algebra.Zorn.G2CASFactorizationProbe.cell_one_73_left_quotient_matrix

theorem row_1_178_left_quotient_matrix :
    ∃ e : PCWordExp,
      autMatrix ((flagRepresentative 178)⁻¹ *
        (collect (leftFactorWord 1 178) *
          weylNF (orbitWeyl 1).1 (orbitWeyl 1).2)) =
        autMatrix (pcWord e) := by
  exact InfoGeometry.Algebra.Zorn.G2CASFactorizationProbe.cell_one_178_left_quotient_matrix

end InfoGeometry.Algebra.Zorn.G2FlagFactorizationRows
