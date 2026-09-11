import InfoGeometry.Canonical.TwoSheetKreinModularCompatibility
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TwoSheetStokesModularComposition
import InfoGeometry.Canonical.TwoSheetStokesKreinTopological

namespace InfoGeometry.Canonical.TwoSheetModularTopological

open InfoGeometry.Canonical.TwoSheetOperatorCoordinates
open InfoGeometry.Canonical.TwoSheetKreinAdjoint
open InfoGeometry.Canonical.TwoSheetStokesKreinTopological
open InfoGeometry.Canonical.TwoSheetStokesCoordinates

theorem stokesKreinAdjointHomeomorph_modularActionHomeomorph
    (rho rhoInv : M6C)
    (hleft : rhoInv * rho = 1)
    (hright : rho * rhoInv = 1)
    (hρ : kreinAdjoint rho = rhoInv)
    (hρInv : kreinAdjoint rhoInv = rho)
    (q : StokesQuad) :
    stokesKreinAdjointHomeomorph
        (stokesModularActionHomeomorph rho rhoInv hleft hright q) =
      stokesModularActionHomeomorph rho rhoInv hleft hright
        (stokesKreinAdjointHomeomorph q) := by
  simpa [stokesKreinAdjointHomeomorph, stokesModularActionHomeomorph,
    Homeomorph.trans_apply, kreinAdjoint_stokes] using
    congrArg operatorStokesLinearEquiv
      (kreinAdjoint_modularAction rho rhoInv
        (operatorStokesLinearEquiv.symm q) hρ hρInv)

end InfoGeometry.Canonical.TwoSheetModularTopological
