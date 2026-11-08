import InfoGeometry.CFT.StressTensorCentralCharge
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.StressTensorCentralChargeCapstone

open InfoGeometry.CFT.StressTensorCentralCharge

theorem capstone_stress_tensor_central_charge_synthesis (c : ℝ) :
    (cylinderStressTensor c 0 = casimirVacuumEnergy c) ∧
    (casimirVacuumEnergy 1 = - 1 / 24) := by
  exact ⟨stress_tensor_plane_to_cylinder c, casimir_energy_c1⟩

end InfoGeometry.Canonical.StressTensorCentralChargeCapstone
