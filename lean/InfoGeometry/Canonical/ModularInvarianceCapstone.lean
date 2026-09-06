import InfoGeometry.CFT.ModularInvariance

namespace InfoGeometry.Canonical.ModularInvarianceCapstone

open InfoGeometry.CFT.ModularInvariance

theorem capstone_modular_invariance_synthesis (τ : ℂ) (hτ : τ ≠ 0) :
    modularS (modularS τ) = τ := by
  exact modular_S_involution τ hτ

end InfoGeometry.Canonical.ModularInvarianceCapstone
