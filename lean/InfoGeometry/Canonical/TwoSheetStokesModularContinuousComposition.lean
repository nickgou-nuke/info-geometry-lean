import InfoGeometry.Canonical.TwoSheetStokesModularContinuousLinear
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TwoSheetModularComposition

namespace InfoGeometry.Canonical.TwoSheetModularTopological

noncomputable section

open InfoGeometry.Canonical.TwoSheetOperatorCoordinates
open InfoGeometry.Canonical.TwoSheetStokesCoordinates
open InfoGeometry.Canonical.TwoSheetStokesTopological

theorem stokesModularActionContinuousLinearEquiv_trans
    (rho₁ rho₁Inv rho₂ rho₂Inv : M6C)
    (h₁left : rho₁Inv * rho₁ = 1)
    (h₁right : rho₁ * rho₁Inv = 1)
    (h₂left : rho₂Inv * rho₂ = 1)
    (h₂right : rho₂ * rho₂Inv = 1) :
    (stokesModularActionContinuousLinearEquiv
      rho₁ rho₁Inv h₁left h₁right).trans
        (stokesModularActionContinuousLinearEquiv
          rho₂ rho₂Inv h₂left h₂right) =
      stokesModularActionContinuousLinearEquiv
        (rho₂ * rho₁) (rho₁Inv * rho₂Inv)
        (by
          calc
            (rho₁Inv * rho₂Inv) * (rho₂ * rho₁) =
                rho₁Inv * (rho₂Inv * rho₂) * rho₁ := by noncomm_ring
            _ = 1 := by rw [h₂left]; simpa using h₁left)
        (by
          calc
            (rho₂ * rho₁) * (rho₁Inv * rho₂Inv) =
                rho₂ * (rho₁ * rho₁Inv) * rho₂Inv := by noncomm_ring
            _ = 1 := by rw [h₁right]; simpa using h₂right) := by
  apply ContinuousLinearEquiv.ext
  funext q
  simp only [ContinuousLinearEquiv.trans_apply,
    stokesModularActionContinuousLinearEquiv_apply,
    LinearEquiv.symm_apply_apply]
  change operatorStokesLinearEquiv
      (modularAction rho₂ rho₂Inv
        (modularAction rho₁ rho₁Inv (operatorStokesLinearEquiv.symm q))) =
    operatorStokesLinearEquiv
      (modularAction (rho₂ * rho₁) (rho₁Inv * rho₂Inv)
        (operatorStokesLinearEquiv.symm q))
  rw [modularAction_comp]

end

end InfoGeometry.Canonical.TwoSheetModularTopological
