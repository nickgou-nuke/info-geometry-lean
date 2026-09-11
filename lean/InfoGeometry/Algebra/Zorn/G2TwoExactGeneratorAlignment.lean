import InfoGeometry.Algebra.Zorn.G2SteinbergPositiveRoots
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.Zorn.G2TwoExactGeneratorAlignment

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2SteinbergRoots
open InfoGeometry.Algebra.Zorn.G2Unipotent

/-- The basis images of the second CAS generator, in the native seven-image
    parametrisation.  The CAS matrix has columns
    `e⁺, e⁻, x₀, x₁, x₁+x₂, y₀, y₁+y₂, y₂`. -/
def casLongBasis : Fin 7 → SplitOctF2 :=
  ![ePlus, up0, up1, add up1 up2, down0, add down1 down2, down2]

def casLongGenerator : SplitOctF2Aut := unipotentLongAut true

theorem casLongGenerator_basis :
    basisRestriction7 casLongGenerator = casLongBasis := by
  funext i
  fin_cases i <;>
    simp [basisRestriction7, casLongGenerator, casLongBasis, basis7,
      unipotentLongAut, unipotentLongEquiv, unipotentLong] <;>
    decide

theorem casLongGenerator_is_native_long :
    casLongGenerator = uLong := rfl

theorem casLongGenerator_square :
    casLongGenerator * casLongGenerator = 1 := by
  exact unipotentLongAut_order true

end InfoGeometry.Algebra.Zorn.G2TwoExactGeneratorAlignment
