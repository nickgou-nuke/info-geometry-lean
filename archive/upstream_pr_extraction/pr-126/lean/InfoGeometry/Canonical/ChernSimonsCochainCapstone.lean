import InfoGeometry.Topological.ChernSimonsCochain

namespace InfoGeometry.Canonical.ChernSimonsCochainCapstone

open InfoGeometry.Topological.ChernSimonsCochain

theorem capstone_chern_simons_cochain_synthesis (k w : ℤ) (γ p : ℝ) (hp : 0 < p) :
    (Complex.exp (((k * w : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) = 1) ∧
    (2 ≤ wilsonLoopTrace γ p) :=
  grand_chern_simons_cochain_synthesis k w γ p hp

end InfoGeometry.Canonical.ChernSimonsCochainCapstone
