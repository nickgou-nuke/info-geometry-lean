import InfoGeometry.CFT.ModularInvariance

namespace InfoGeometry.Canonical.ModularInvarianceCapstone

open InfoGeometry.CFT.ModularInvariance

theorem capstone_modular_invariance_synthesis (τ : ℂ) (hτ : τ ≠ 0) :
    modularS (modularS τ) = τ :=
  grand_modular_invariance_synthesis τ hτ

end InfoGeometry.Canonical.ModularInvarianceCapstone
