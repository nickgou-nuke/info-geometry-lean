import InfoGeometry.Algebra.Zorn.G2SteinbergPositiveRoots

namespace InfoGeometry.Algebra.Zorn.G2TwoExactGeneratorAlignment

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2SteinbergRoots
open InfoGeometry.Algebra.Zorn.G2Unipotent

/-- The basis images of the second CAS generator, in the native seven-image
    parametrisation.  The CAS matrix has columns
    `e⁺, e⁻, x₀, x₁+x₂, x₂, y₀, y₁, y₁+y₂`. -/
def casLongBasis : Fin 7 → SplitOctF2 :=
  ![ePlus, up0, add up1 up2, up2, down0, down1, add down1 down2]

def casLongGenerator : SplitOctF2Aut := unipotentLongAut true

theorem casLongGenerator_basis :
    basisRestriction7 casLongGenerator = casLongBasis := by
  funext i
  fin_cases i <;>
    rfl

theorem casLongGenerator_is_native_long :
    casLongGenerator = uLong := rfl

theorem casLongGenerator_square :
    casLongGenerator * casLongGenerator = 1 := by
  exact unipotentLongAut_order true

end InfoGeometry.Algebra.Zorn.G2TwoExactGeneratorAlignment
