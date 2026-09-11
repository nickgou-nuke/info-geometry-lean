import InfoGeometry.Holography.ChernSimonsToLiouville
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.ChernSimonsToLiouvilleCapstone

open InfoGeometry.Holography.ChernSimonsToLiouville

theorem capstone_chern_simons_to_liouville_synthesis (b μ ϕ : ℝ) (hb : b ≠ 0) :
    (liouvilleBackgroundCharge (1 / b) = liouvilleBackgroundCharge b) ∧
    (liouvilleCentralCharge (1 / b) = liouvilleCentralCharge b) ∧
    (brownHenneauxCentralCharge (1 / 6) = 1) ∧
    (HasDerivAt (fun x : ℝ => μ * Real.exp (2 * b * x))
      (2 * b * (μ * Real.exp (2 * b * ϕ))) ϕ) := by
  exact ⟨liouville_background_charge_self_dual b hb,
    liouville_central_charge_self_dual b hb,
    brown_henneaux_c1_at_one_sixth,
    hasDerivAt_liouville_potential b μ ϕ⟩

end InfoGeometry.Canonical.ChernSimonsToLiouvilleCapstone
