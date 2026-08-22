import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
import InfoGeometry.Algebra.Zorn.G2TwoExplicitGenerators
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylGroup
import InfoGeometry.Algebra.Zorn.G2ConcreteBN2CorrectSecondConjugation

/-!
# First CAS/Lean carrier-alignment certificate

The rows below are the exact GAP support rows for the first PC generator.
They are included only after comparison with the Lean coordinate order
`(a,b,x0,x1,x2,y0,y1,y2)`.  This file deliberately certifies the matrix
orientation before any quotient or orbit transport is attempted.
-/

namespace InfoGeometry.Algebra.Zorn.G2LeanCarrierMatrixAlignment

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2ConcreteWeyl

abbrev F2 := ZMod 2

def pc1Matrix : Matrix (Fin 8) (Fin 8) F2 :=
  ![![1, 0, 0, 1, 0, 0, 0, 0],
    ![0, 1, 0, 1, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 1],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 1, 1, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![1, 1, 0, 1, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

theorem autMatrix_pc1Aut_eq : autMatrix pc1Aut = pc1Matrix := by
  native_decide

def pc2Matrix : Matrix (Fin 8) (Fin 8) F2 :=
  ![![1, 0, 0, 0, 0, 0, 0, 1],
    ![0, 1, 0, 0, 0, 0, 0, 1],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 0],
    ![1, 1, 0, 1, 1, 0, 0, 1],
    ![0, 0, 1, 1, 0, 1, 1, 1],
    ![0, 0, 1, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

def pc3Matrix : Matrix (Fin 8) (Fin 8) F2 :=
  ![![1, 0, 1, 0, 0, 0, 0, 1],
    ![0, 1, 1, 0, 0, 0, 0, 1],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 1],
    ![1, 1, 0, 1, 1, 0, 1, 0],
    ![1, 1, 1, 1, 0, 1, 0, 1],
    ![0, 0, 1, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

def pc4Matrix : Matrix (Fin 8) (Fin 8) F2 :=
  ![![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

def pc5Matrix : Matrix (Fin 8) (Fin 8) F2 :=
  ![![1, 0, 0, 0, 0, 0, 0, 1],
    ![0, 1, 0, 0, 0, 0, 0, 1],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![1, 1, 0, 1, 1, 0, 0, 1],
    ![0, 0, 0, 1, 0, 1, 0, 0],
    ![0, 0, 1, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

def pc6Matrix : Matrix (Fin 8) (Fin 8) F2 :=
  ![![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 1, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

theorem autMatrix_pc2Aut_eq : autMatrix pc2Aut = pc2Matrix := by native_decide
theorem autMatrix_pc3Aut_eq : autMatrix pc3Aut = pc3Matrix := by native_decide
theorem autMatrix_pc4Aut_eq : autMatrix pc4Aut = pc4Matrix := by native_decide
theorem autMatrix_pc5Aut_eq : autMatrix pc5Aut = pc5Matrix := by native_decide
theorem autMatrix_pc6Aut_eq : autMatrix pc6Aut = pc6Matrix := by native_decide

def swap01Matrix : Matrix (Fin 8) (Fin 8) F2 :=
  ![![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

theorem autMatrix_swap01Aut_eq : autMatrix swap01Aut = swap01Matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [autMatrix, swap01Aut_apply, swap01Fun, carrierToVec,
      splitOctF2EquivBits, splitOctF2ToBits, basis8, bitToF2,
      ePlus, eMinus, up0, up1, up2, down0, down1, down2, swap01Matrix]

open InfoGeometry.Algebra.Zorn.G2ConcreteBN2CorrectSecondConjugation

def correctedTMatrix : Matrix (Fin 8) (Fin 8) F2 :=
  ![![0, 1, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0]]

theorem autMatrix_correctedT_eq : autMatrix correctedT = correctedTMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [autMatrix, correctedT, concreteWeylElement,
      swap01Aut_apply, swap01Fun, swapCartanAut, swapCartanEquiv,
      swapCartanFun, cycle012Aut_apply, cycle012Fun, basis8,
      carrierToVec, splitOctF2EquivBits, splitOctF2ToBits, bitToF2,
      ePlus, eMinus, up0, up1, up2, down0, down1, down2,
      correctedTMatrix]

end InfoGeometry.Algebra.Zorn.G2LeanCarrierMatrixAlignment
