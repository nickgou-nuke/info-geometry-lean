import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.CFT.StressTensorCentralCharge

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def cylinderStressTensor (c T_plane : ℝ) : ℝ :=
  T_plane - c / 24

def casimirVacuumEnergy (c : ℝ) : ℝ :=
  - c / 24

theorem stress_tensor_plane_to_cylinder (c : ℝ) :
    cylinderStressTensor c 0 = casimirVacuumEnergy c := by
  unfold cylinderStressTensor casimirVacuumEnergy
  ring

theorem casimir_energy_c1 :
    casimirVacuumEnergy 1 = - 1 / 24 := by
  unfold casimirVacuumEnergy
  ring

theorem grand_stress_tensor_central_charge_synthesis (c : ℝ) :
    (cylinderStressTensor c 0 = casimirVacuumEnergy c) ∧
    (casimirVacuumEnergy 1 = - 1 / 24) :=
  ⟨stress_tensor_plane_to_cylinder c,
   casimir_energy_c1⟩
