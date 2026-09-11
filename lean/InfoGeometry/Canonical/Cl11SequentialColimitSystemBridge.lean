import InfoGeometry.Canonical.InductiveColimitBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CantorCl11Limit

/-!
# Concrete sequential colimit system for the Cl(1,1) matrix tower

This file instantiates the repository's generic sequential-colimit interface
with the existing finite matrix stages, bonding maps, and direct-limit readout.
It does not add a C*-completion or an analytic infinite tensor product.
-/

namespace InfoGeometry.Canonical.Cl11SequentialColimitSystemBridge

noncomputable section

open InfoGeometry.Canonical.InductiveColimitBridge
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit

def cl11System : SequentialColimitSystem where
  Stage := fun n => InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage n
  Limit := InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit
  bond := fun n => InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n
  toLimit := fun n => InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n
  cone_comm := by
    intro n x
    exact InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage_apply_bond n x

theorem cl11_toLimit_bondSeq
    (n m : ℕ)
    (x : InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage n) :
    cl11System.toLimit (n + m) (cl11System.bondSeq n m x) =
      cl11System.toLimit n x := by
  exact cl11System.toLimit_bondSeq n m x

end

end InfoGeometry.Canonical.Cl11SequentialColimitSystemBridge
