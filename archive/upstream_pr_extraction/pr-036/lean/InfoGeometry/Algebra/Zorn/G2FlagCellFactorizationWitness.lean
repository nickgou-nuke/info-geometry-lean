import InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
import InfoGeometry.Algebra.Zorn.G2FlagCellFactorizationBridge
import InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
import InfoGeometry.Algebra.Zorn.G2FlagWordCertificateEval
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

namespace InfoGeometry.Algebra.Zorn.G2FlagCellFactorizationWitness

open InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.Algebra.Zorn.G2FlagCellFactorizationBridge
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

set_option maxRecDepth 100000 in
theorem factorization_on_cell
    (k : Fin 12) (i : Fin 189) (hi : i ∈ orbitCells k) :
    flagRepresentative i =
      collect (leftFactorWord k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
          collect (rightFactorWord k i) := by
  fin_cases k <;> fin_cases i <;>
    simp [orbitCells, flagCells] at hi ⊢ <;>
    decide

set_option maxRecDepth 100000 in
theorem hcell_of_factorization
    (k : Fin 12) (i : Fin 189) (hi : i ∈ orbitCells k) :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        orbitEnum i = b •
          (QuotientGroup.mk
            (weylNF (orbitWeyl k).1 (orbitWeyl k).2) :
            CarrierQuotient) := by
  refine ⟨collect (leftFactorWord k i),
    collect_mem_unipotentSubgroup _, ?_⟩
  exact quotientRepresentative_eq_left_smul_of_factorization i
    (collect (leftFactorWord k i))
    (collect (rightFactorWord k i))
    (weylNF (orbitWeyl k).1 (orbitWeyl k).2)
    (collect_mem_unipotentSubgroup _)
    (factorization_on_cell k i hi)

end InfoGeometry.Algebra.Zorn.G2FlagCellFactorizationWitness
