import InfoGeometry.Algebra.Zorn.G2FlagFactorizationRows
import InfoGeometry.Algebra.Zorn.G2FlagWordCertificateEval
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

namespace InfoGeometry.Algebra.Zorn.G2FlagFactorizationConcreteCertificate

open InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2FlagFactorizationRows
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagRepresentativeBase
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

structure AnchorFactorizationData where
  cell : Fin 12
  representative : Fin 189
  left : FactorWord
  right : FactorWord

def anchorFactorizationData : Fin 12 → AnchorFactorizationData := fun k =>
  { cell := k
    representative := orbitCellAnchor k
    left := leftFactorWord k (orbitCellAnchor k)
    right := rightFactorWord k (orbitCellAnchor k) }

theorem anchorFactorizationData_mem (k : Fin 12) :
    (anchorFactorizationData k).representative ∈ orbitCells k := by
  exact orbitCellAnchor_mem k

theorem anchorFactorizationData_sound (k : Fin 12) :
    flagRepresentative (anchorFactorizationData k).representative =
      collect (anchorFactorizationData k).left *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
          collect (anchorFactorizationData k).right := by
  apply autMatrix_injective
  fin_cases k <;> decide

theorem anchorFactorizationData_matrix_sound (k : Fin 12) :
    autMatrix (flagRepresentative (anchorFactorizationData k).representative) =
      autMatrix
        (collect (anchorFactorizationData k).left *
          weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
            collect (anchorFactorizationData k).right) := by
  rw [anchorFactorizationData_sound k]

structure VerifiedRowData where
  cell : Fin 12
  representative : Fin 189
  left : FactorWord
  right : FactorWord

def verifiedRows : Fin 5 → VerifiedRowData
  | 0 =>
      { cell := 0, representative := 0
        left := leftFactorWord 0 0, right := rightFactorWord 0 0 }
  | 1 =>
      { cell := 1, representative := 24
        left := leftFactorWord 1 24, right := rightFactorWord 1 24 }
  | 2 =>
      { cell := 4, representative := 6
        left := leftFactorWord 4 6, right := rightFactorWord 4 6 }
  | 3 =>
      { cell := 4, representative := 18
        left := rightFactorWord 4 18, right := leftFactorWord 4 18 }
  | 4 =>
      { cell := 1, representative := 45
        left := leftFactorWord 1 45, right := rightFactorWord 1 45 }

theorem verifiedRows_sound (j : Fin 5) :
    flagRepresentative (verifiedRows j).representative =
      collect (verifiedRows j).left *
        weylNF (orbitWeyl (verifiedRows j).cell).1
          (orbitWeyl (verifiedRows j).cell).2 *
          collect (verifiedRows j).right := by
  fin_cases j
  · exact row_0_0
  · exact row_1_24
  · exact row_4_6
  · exact row_4_18
  · exact row_1_45

theorem verifiedRows_matrix_sound (j : Fin 5) :
    autMatrix (flagRepresentative (verifiedRows j).representative) =
      autMatrix
        (collect (verifiedRows j).left *
          weylNF (orbitWeyl (verifiedRows j).cell).1
            (orbitWeyl (verifiedRows j).cell).2 *
            collect (verifiedRows j).right) := by
  rw [verifiedRows_sound j]

end InfoGeometry.Algebra.Zorn.G2FlagFactorizationConcreteCertificate
