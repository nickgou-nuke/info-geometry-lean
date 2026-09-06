import InfoGeometry.Holography.ChernSimonsToLiouville

namespace InfoGeometry.Canonical.ChernSimonsToLiouvilleCapstone

open InfoGeometry.Holography.ChernSimonsToLiouville

theorem capstone_chern_simons_to_liouville_synthesis (b μ ϕ : ℝ) (hb : b ≠ 0) :
    (liouvilleBackgroundCharge (1 / b) = liouvilleBackgroundCharge b) ∧
    (liouvilleCentralCharge (1 / b) = liouvilleCentralCharge b) ∧
    (brownHenneauxCentralCharge (1 / 6) = 1) ∧
    (HasDerivAt (fun x : ℝ => μ * Real.exp (2 * b * x))
                (2 * b * (μ * Real.exp (2 * b * ϕ))) ϕ) :=
  grand_chern_simons_to_liouville_synthesis b μ ϕ hb

end InfoGeometry.Canonical.ChernSimonsToLiouvilleCapstone
