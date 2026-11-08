import InfoGeometry.Algebra.Zorn.G2QuotientOrbitSeparation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

namespace InfoGeometry.Algebra.Zorn.G2PCMatrixSeparationBridge

open InfoGeometry.Algebra.Zorn.G2QuotientOrbitSeparation
open InfoGeometry.Algebra.Zorn.G2BNPair
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/-!
Transport boundary for the Bruhat separation argument.  A matrix inequality
for every PC triple is enough to produce the required group inequality.  No
enumeration of the automorphism carrier is involved.
-/

theorem pc_separation_of_matrix_separation
    (hmatrix : ∀ {k l : Fin 12}, k ≠ l →
      ∀ a c d : PCWordExp,
        autMatrix (pcWord c * orbitWeylRepresentative l) ≠
          autMatrix (pcWord a * orbitWeylRepresentative k * pcWord d)) :
    ∀ {k l : Fin 12}, k ≠ l →
      ∀ a c d : PCWordExp,
        pcWord c * orbitWeylRepresentative l ≠
          pcWord a * orbitWeylRepresentative k * pcWord d := by
  intro k l hkl a c d heq
  apply hmatrix hkl a c d
  exact congrArg autMatrix heq

theorem quotientOrbit_disjoint_of_matrix_separation
    (hmatrix : ∀ {k l : Fin 12}, k ≠ l →
      ∀ a c d : PCWordExp,
        autMatrix (pcWord c * orbitWeylRepresentative l) ≠
          autMatrix (pcWord a * orbitWeylRepresentative k * pcWord d)) :
    ∀ {k l : Fin 12}, k ≠ l →
      Disjoint
        (quotientOrbit unipotentSubgroup (orbitWeylRepresentative k))
        (quotientOrbit unipotentSubgroup (orbitWeylRepresentative l)) := by
  apply quotientOrbit_disjoint_of_pc_separation
  exact pc_separation_of_matrix_separation hmatrix

end InfoGeometry.Algebra.Zorn.G2PCMatrixSeparationBridge
