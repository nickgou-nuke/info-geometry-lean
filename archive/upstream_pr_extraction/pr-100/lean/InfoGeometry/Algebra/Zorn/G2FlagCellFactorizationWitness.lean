import InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
import InfoGeometry.Algebra.Zorn.G2FlagCellFactorizationBridge
import InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
import InfoGeometry.Algebra.Zorn.G2FlagWordCertificateEval
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessAssembly

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
open InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessAssembly
open InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessData
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure

theorem factorization_on_cell
    (k : Fin 12) (i : Fin 189) (hi : i ∈ orbitCells k) :
    flagRepresentative i =
      collect (gapLeftWitness k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
          collect (gapRightWitness k i) := by
  exact all_gapWitnessFactorization k i hi

theorem hcell_of_factorization
    (k : Fin 12) (i : Fin 189) (hi : i ∈ orbitCells k) :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        orbitEnum i = b •
          (QuotientGroup.mk
            (weylNF (orbitWeyl k).1 (orbitWeyl k).2) :
            CarrierQuotient) := by
  refine ⟨collect (gapLeftWitness k i),
    gapLeftWitness_mem_unipotentSubgroup k i, ?_⟩
  exact quotientRepresentative_eq_left_smul_of_factorization i
    (collect (gapLeftWitness k i))
    (collect (gapRightWitness k i))
    (weylNF (orbitWeyl k).1 (orbitWeyl k).2)
    (gapRightWitness_mem_unipotentSubgroup k i)
    (factorization_on_cell k i hi)

end InfoGeometry.Algebra.Zorn.G2FlagCellFactorizationWitness
