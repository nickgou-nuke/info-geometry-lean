import Mathlib.Analysis.Normed.Module.FiniteDimension
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TwoSheetModularTopological

namespace InfoGeometry.Canonical.TwoSheetModularTopological

noncomputable section

open InfoGeometry.Canonical.TwoSheetOperatorCoordinates

def modularActionLinearMap (rho rhoInv : M6C) : M6C →ₗ[ℂ] M6C where
  toFun := modularAction rho rhoInv
  map_add' A B := by
    simp [modularAction, add_mul, mul_add]
  map_smul' c A := by
    simp [modularAction, smul_mul_assoc, mul_smul_comm]

theorem modularActionLinearMap_apply
    (rho rhoInv A : M6C) :
    modularActionLinearMap rho rhoInv A = modularAction rho rhoInv A := rfl

def modularActionLinearEquiv
    (rho rhoInv : M6C)
    (hleft : rhoInv * rho = 1)
    (hright : rho * rhoInv = 1) : M6C ≃ₗ[ℂ] M6C where
  toLinearMap := modularActionLinearMap rho rhoInv
  invFun := modularActionInverse rho rhoInv
  left_inv A := modularActionInverse_modularAction rho rhoInv A hleft hright
  right_inv A := modularAction_modularActionInverse rho rhoInv A hleft hright

theorem modularActionLinearEquiv_apply
    (rho rhoInv : M6C)
    (hleft : rhoInv * rho = 1)
    (hright : rho * rhoInv = 1)
    (A : M6C) :
    modularActionLinearEquiv rho rhoInv hleft hright A =
      modularAction rho rhoInv A := rfl

def modularActionContinuousLinearEquiv
    (rho rhoInv : M6C)
    (hleft : rhoInv * rho = 1)
    (hright : rho * rhoInv = 1) : M6C ≃L[ℂ] M6C :=
  (modularActionLinearEquiv rho rhoInv hleft hright).toContinuousLinearEquiv

theorem modularActionContinuousLinearEquiv_apply
    (rho rhoInv : M6C)
    (hleft : rhoInv * rho = 1)
    (hright : rho * rhoInv = 1)
    (A : M6C) :
    modularActionContinuousLinearEquiv rho rhoInv hleft hright A =
      modularAction rho rhoInv A := rfl

end

end InfoGeometry.Canonical.TwoSheetModularTopological
