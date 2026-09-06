import InfoGeometry.CFT.StressTensorCentralCharge

namespace InfoGeometry.Canonical.StressTensorCentralChargeCapstone

open InfoGeometry.CFT.StressTensorCentralCharge

theorem capstone_stress_tensor_central_charge_synthesis (c : ℝ) :
    (cylinderStressTensor c 0 = casimirVacuumEnergy c) ∧
    (casimirVacuumEnergy 1 = - 1 / 24) :=
  grand_stress_tensor_central_charge_synthesis c

end InfoGeometry.Canonical.StressTensorCentralChargeCapstone
