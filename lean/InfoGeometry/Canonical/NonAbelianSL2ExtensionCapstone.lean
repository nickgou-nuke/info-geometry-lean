import InfoGeometry.Gauge.NonAbelianSL2Extension
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.NonAbelianSL2ExtensionCapstone

open InfoGeometry.Gauge.NonAbelianSL2Extension

theorem capstone_sl2_algebra_synthesis :
    (genJ * genJ = - 1) ∧ (genK * genK = 1) ∧
    (genK * genE - genE * genK = (2 : ℝ) • genE) ∧
    (genK * genF - genF * genK = -((2 : ℝ) • genF)) ∧
    (genE * genF - genF * genE = genK) := by
  exact ⟨genJ_sq_eq_neg_one, genK_sq_eq_one, comm_K_E, comm_K_F, comm_E_F⟩

end InfoGeometry.Canonical.NonAbelianSL2ExtensionCapstone
