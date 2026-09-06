import InfoGeometry.Gauge.NonAbelianSL2Extension

namespace InfoGeometry.Canonical.NonAbelianSL2ExtensionCapstone

open InfoGeometry.Gauge.NonAbelianSL2Extension

theorem capstone_sl2_algebra_synthesis :
    (genJ * genJ = - 1) ∧
    (genK * genK = 1) ∧
    (genK * genE - genE * genK = (2 : ℝ) • genE) ∧
    (genK * genF - genF * genK = -((2 : ℝ) • genF)) ∧
    (genE * genF - genF * genE = genK) :=
  grand_sl2_algebra_synthesis

end InfoGeometry.Canonical.NonAbelianSL2ExtensionCapstone
