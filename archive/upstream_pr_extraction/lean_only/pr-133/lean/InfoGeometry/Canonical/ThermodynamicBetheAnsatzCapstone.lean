import InfoGeometry.Thermal.ThermodynamicBetheAnsatz

namespace InfoGeometry.Canonical.ThermodynamicBetheAnsatzCapstone

open InfoGeometry.Thermal.ThermodynamicBetheAnsatz

theorem capstone_thermodynamic_bethe_ansatz_synthesis (ε : ℝ) :
    (0 < yangYangLFunction ε) ∧
    (HasDerivAt yangYangLFunction (- (1 / (1 + Real.exp ε))) ε) ∧
    (effectiveCentralChargeTBA = 1 / 2) ∧
    (effectiveCentralChargeTBA + effectiveCentralChargeTBA = 1) :=
  grand_thermodynamic_bethe_ansatz_synthesis ε

end InfoGeometry.Canonical.ThermodynamicBetheAnsatzCapstone
