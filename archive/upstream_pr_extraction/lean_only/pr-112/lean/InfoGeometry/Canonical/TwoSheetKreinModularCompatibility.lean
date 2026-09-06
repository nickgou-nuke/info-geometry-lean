import InfoGeometry.Canonical.TwoSheetModularComposition
import InfoGeometry.Canonical.TwoSheetKreinAdjoint

namespace InfoGeometry.Canonical.TwoSheetModularTopological

open InfoGeometry.Canonical.TwoSheetOperatorCoordinates
open InfoGeometry.Canonical.TwoSheetKreinAdjoint

theorem kreinAdjoint_modularAction
    (rho rhoInv A : M6C)
    (hρ : kreinAdjoint rho = rhoInv)
    (hρInv : kreinAdjoint rhoInv = rho) :
    kreinAdjoint (modularAction rho rhoInv A) =
      modularAction rho rhoInv (kreinAdjoint A) := by
  change kreinAdjoint ((rho * A) * rhoInv) =
    rho * kreinAdjoint A * rhoInv
  rw [kreinAdjoint_mul, kreinAdjoint_mul, hρ, hρInv]
  simp only [Matrix.mul_assoc]

end InfoGeometry.Canonical.TwoSheetModularTopological
