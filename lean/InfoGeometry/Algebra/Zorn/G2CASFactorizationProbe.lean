import InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
import InfoGeometry.Algebra.Zorn.G2FlagRepresentativeBase
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylG2

namespace InfoGeometry.Algebra.Zorn.G2CASFactorizationProbe

open InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

set_option maxRecDepth 100000 in
theorem cell_one_45_factorization :
    flagRepresentative 45 =
      collect (leftFactorWord 1 45) *
        weylNF (orbitWeyl 1).1 (orbitWeyl 1).2 *
          collect (rightFactorWord 1 45) := by
  apply autMatrix_injective
  decide

set_option maxRecDepth 100000 in
theorem cell_one_45_quotient_witness :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        quotientRepresentative 45 =
          b • (QuotientGroup.mk
            (weylNF (orbitWeyl 1).1 (orbitWeyl 1).2) : CarrierQuotient) := by
  refine ⟨collect (leftFactorWord 1 45),
    collect_mem_unipotentSubgroup _, ?_⟩
  rw [quotientRepresentative, cell_one_45_factorization]
  change QuotientGroup.mk
      (collect (leftFactorWord 1 45) *
        weylNF (orbitWeyl 1).1 (orbitWeyl 1).2 *
          collect (rightFactorWord 1 45)) =
    QuotientGroup.mk (collect (leftFactorWord 1 45) *
      weylNF (orbitWeyl 1).1 (orbitWeyl 1).2)
  rw [QuotientGroup.eq]
  have hri :
      (collect (rightFactorWord 1 45))⁻¹ ∈ unipotentSubgroup :=
    unipotentSubgroup.inv_mem (collect_mem_unipotentSubgroup _)
  obtain ⟨e, he⟩ :=
    hri
  refine ⟨e, ?_⟩
  simp [mul_assoc]
  rw [← he]

set_option maxRecDepth 100000 in
theorem cell_one_178_left_quotient_matrix :
    ∃ e : PCWordExp,
      autMatrix ((flagRepresentative 178)⁻¹ *
        (collect (leftFactorWord 1 178) *
          weylNF (orbitWeyl 1).1 (orbitWeyl 1).2)) =
        autMatrix (pcWord e) := by
  decide

set_option maxRecDepth 100000 in
theorem cell_one_73_left_quotient_matrix :
    ∃ e : PCWordExp,
      autMatrix ((flagRepresentative 73)⁻¹ *
        (collect (leftFactorWord 1 73) *
          weylNF (orbitWeyl 1).1 (orbitWeyl 1).2)) =
        autMatrix (pcWord e) := by
  decide

end InfoGeometry.Algebra.Zorn.G2CASFactorizationProbe
