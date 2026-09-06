import InfoGeometry.Canonical.TwoSheetModularContinuousLinear
import InfoGeometry.Canonical.TwoSheetStokesTopological

namespace InfoGeometry.Canonical.TwoSheetModularTopological

noncomputable section

open InfoGeometry.Canonical.TwoSheetOperatorCoordinates
open InfoGeometry.Canonical.TwoSheetStokesCoordinates
open InfoGeometry.Canonical.TwoSheetStokesTopological

def stokesModularActionContinuousLinearEquiv
    (rho rhoInv : M6C)
    (hleft : rhoInv * rho = 1)
    (hright : rho * rhoInv = 1) :
    StokesQuad ≃L[ℂ] StokesQuad :=
  operatorStokesContinuousLinearEquiv.symm.trans
    ((modularActionContinuousLinearEquiv rho rhoInv hleft hright).trans
      operatorStokesContinuousLinearEquiv)

theorem stokesModularActionContinuousLinearEquiv_apply
    (rho rhoInv : M6C)
    (hleft : rhoInv * rho = 1)
    (hright : rho * rhoInv = 1)
    (q : StokesQuad) :
    stokesModularActionContinuousLinearEquiv rho rhoInv hleft hright q =
      operatorStokesLinearEquiv
        (modularAction rho rhoInv (operatorStokesLinearEquiv.symm q)) := by
  rfl

end

end InfoGeometry.Canonical.TwoSheetModularTopological
