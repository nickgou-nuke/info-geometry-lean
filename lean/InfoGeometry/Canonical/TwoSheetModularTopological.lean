import Mathlib.Topology.Algebra.Module.FiniteDimension
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TwoSheetStokesTopological

noncomputable section

namespace InfoGeometry.Canonical.TwoSheetModularTopological

open InfoGeometry.Canonical.TwoSheetOperatorCoordinates
open InfoGeometry.Canonical.TwoSheetStokesCoordinates
open InfoGeometry.Canonical.TwoSheetStokesTopological

def modularAction (rho rhoInv A : M6C) : M6C :=
  rho * A * rhoInv

def modularActionInverse (rho rhoInv A : M6C) : M6C :=
  rhoInv * A * rho

theorem modularActionInverse_modularAction
    (rho rhoInv A : M6C)
    (hleft : rhoInv * rho = 1)
    (hright : rho * rhoInv = 1) :
    modularActionInverse rho rhoInv (modularAction rho rhoInv A) = A := by
  simp only [modularActionInverse, modularAction]
  calc
    rhoInv * (rho * A * rhoInv) * rho =
        (rhoInv * rho) * A * (rhoInv * rho) := by noncomm_ring
    _ = A := by rw [hleft]; simp

theorem modularAction_modularActionInverse
    (rho rhoInv A : M6C)
    (hleft : rhoInv * rho = 1)
    (hright : rho * rhoInv = 1) :
    modularAction rho rhoInv (modularActionInverse rho rhoInv A) = A := by
  simp only [modularAction, modularActionInverse]
  calc
    rho * (rhoInv * A * rho) * rhoInv =
        (rho * rhoInv) * A * (rho * rhoInv) := by noncomm_ring
    _ = A := by rw [hright]; simp

theorem continuous_modularAction (rho rhoInv : M6C) :
    Continuous (modularAction rho rhoInv) := by
  unfold modularAction
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem continuous_modularActionInverse (rho rhoInv : M6C) :
    Continuous (modularActionInverse rho rhoInv) := by
  unfold modularActionInverse
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

noncomputable def modularActionHomeomorph
    (rho rhoInv : M6C)
    (hleft : rhoInv * rho = 1)
    (hright : rho * rhoInv = 1) : M6C ≃ₜ M6C where
  toFun := modularAction rho rhoInv
  invFun := modularActionInverse rho rhoInv
  left_inv A := modularActionInverse_modularAction rho rhoInv A hleft hright
  right_inv A := modularAction_modularActionInverse rho rhoInv A hleft hright
  continuous_toFun := continuous_modularAction rho rhoInv
  continuous_invFun := continuous_modularActionInverse rho rhoInv

def stokesModularActionHomeomorph
    (rho rhoInv : M6C)
    (hleft : rhoInv * rho = 1)
    (hright : rho * rhoInv = 1) : StokesQuad ≃ₜ StokesQuad :=
  operatorStokesHomeomorph.symm.trans
    ((modularActionHomeomorph rho rhoInv hleft hright).trans
      operatorStokesHomeomorph)

theorem stokesModularActionHomeomorph_apply
    (rho rhoInv : M6C)
    (hleft : rhoInv * rho = 1)
    (hright : rho * rhoInv = 1)
    (q : StokesQuad) :
    stokesModularActionHomeomorph rho rhoInv hleft hright q =
      operatorStokesLinearEquiv
        (modularAction rho rhoInv (operatorStokesLinearEquiv.symm q)) := by
  rfl

end InfoGeometry.Canonical.TwoSheetModularTopological
