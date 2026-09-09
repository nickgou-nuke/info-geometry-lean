import InfoGeometry.Topological.ChernSimonsCochain

namespace InfoGeometry.Canonical.ChernSimonsCochainCapstone

open InfoGeometry.Topological.ChernSimonsCochain

/-! The finite cochain packet combines large-gauge periodicity with the
Wilson-loop lower bound, without adding a global gauge-bundle assertion. -/
theorem capstone_chern_simons_cochain_synthesis (k w : ℤ) (γ p : ℝ) (hp : 0 < p) :
    (Complex.exp (((k * w : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) = 1) ∧
    (2 ≤ wilsonLoopTrace γ p) := by
  exact ⟨large_gauge_exp_integer k w, wilson_loop_lower_bound γ p hp⟩

end InfoGeometry.Canonical.ChernSimonsCochainCapstone
