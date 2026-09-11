import InfoGeometry.Algebra.Zorn.G2FlagCellWitnessCertificate
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.Zorn.G2OneNontrivialCellCertificate

open InfoGeometry.Algebra.Zorn.G2FlagCellWitnessCertificate
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

def pcGeneratorWord : List (Fin 6) → SplitOctF2Aut
  | [] => 1
  | i :: is => pcGenerator i * pcGeneratorWord is

set_option maxRecDepth 100000 in
theorem cell_one_factorization_24 :
    flagRepresentative 24 =
      pcGeneratorWord [] *
        weylNF (orbitWeyl 1).1 (orbitWeyl 1).2 *
        pcGeneratorWord [] := by
  apply autMatrix_injective
  simp [pcGeneratorWord]
  decide

end InfoGeometry.Algebra.Zorn.G2OneNontrivialCellCertificate
