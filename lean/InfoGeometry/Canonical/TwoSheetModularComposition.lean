import InfoGeometry.Canonical.TwoSheetModularTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.TwoSheetModularTopological

open InfoGeometry.Canonical.TwoSheetOperatorCoordinates

theorem modularAction_comp
    (rho₁ rho₁Inv rho₂ rho₂Inv A : M6C) :
    modularAction rho₂ rho₂Inv (modularAction rho₁ rho₁Inv A) =
      modularAction (rho₂ * rho₁) (rho₁Inv * rho₂Inv) A := by
  simp [modularAction, Matrix.mul_assoc]

theorem modularActionInverse_comp
    (rho₁ rho₁Inv rho₂ rho₂Inv A : M6C) :
      modularActionInverse rho₂ rho₂Inv
        (modularActionInverse rho₁ rho₁Inv A) =
      modularActionInverse (rho₁ * rho₂) (rho₂Inv * rho₁Inv) A := by
  simp [modularActionInverse, Matrix.mul_assoc]

end InfoGeometry.Canonical.TwoSheetModularTopological
