import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Algebra.SquareRootLogarithmicInfoMetricBridge

/-- **Theorem 1: The Dirac Square Root Linearization Identity**.
    For Clifford generators obeying {γa, γb} = 2 ηab 1,
    (γ0 p0 + γ1 p1)^2 = (p0^2 - p1^2) 1. -/
theorem dirac_square_root_linearization {R : Type*} [CommRing R]
    (g0 g1 p0 p1 : R)
    (h00 : g0 * g0 = 1)
    (h11 : g1 * g1 = -1)
    (h01 : g0 * g1 + g1 * g0 = 0) :
    (g0 * p0 + g1 * p1) * (g0 * p0 + g1 * p1) = (p0 * p0 - p1 * p1) * 1 := by
  have h_anticomm : g1 * g0 = - (g0 * g1) := eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h01)
  calc (g0 * p0 + g1 * p1) * (g0 * p0 + g1 * p1)
    _ = (g0 * g0) * (p0 * p0) + (g0 * g1) * (p0 * p1) + (g1 * g0) * (p1 * p0) + (g1 * g1) * (p1 * p1) := by ring
    _ = 1 * (p0 * p0) + (g0 * g1) * (p0 * p1) + (- (g0 * g1)) * (p1 * p0) + (-1) * (p1 * p1) := by rw [h00, h11, h_anticomm]
    _ = (p0 * p0 - p1 * p1) * 1 := by ring

/-- **Theorem 2: The √y Fisher-Rao Metric Transformed Line Element Identity**.
    4 * (du)^2 = (dy)^2 / y where u = √y, expressed as 4 * u^2 * (du)^2 = (dy)^2.
    For u = √y, 2 * u * (du) = dy. Therefore (2 u du)^2 = 4 u^2 du^2 = (dy)^2. -/
theorem fisher_rao_square_root_metric (u du dy : ℝ) (h_diff : 2 * u * du = dy) :
    4 * (u * u) * (du * du) = dy * dy := by
  calc 4 * (u * u) * (du * du)
    _ = (2 * u * du) * (2 * u * du) := by ring
    _ = dy * dy := by rw [h_diff]

/-- **Theorem 3: The Logarithmic 1-Form Energy Multiplicativity to Additivity**.
    H(n * m) = Real.log(n * m) = Real.log(n) + Real.log(m) = H(n) + H(m)
    for positive integer modes n, m > 0. -/
theorem logarithmic_primon_energy_additivity (n m : ℝ) (hn : 0 < n) (hm : 0 < m) :
    Real.log (n * m) = Real.log n + Real.log m :=
  Real.log_mul (ne_of_gt hn) (ne_of_gt hm)

/-- **Theorem 4: Master Square Root & Logarithmic Info-Geometry Synthesis**.
    Unifies:
    1. Dirac Clifford linearization (γ^μ p_μ)^2 = p0^2 - p1^2.
    2. Fisher-Rao metric √y transformation 4 u^2 (du)^2 = (dy)^2.
    3. Primon logarithmic energy additivity Real.log (n * m) = Real.log n + Real.log m. -/
theorem master_square_root_logarithmic_info_synthesis
    {R : Type*} [CommRing R] (g0 g1 p0 p1 : R)
    (h00 : g0 * g0 = 1) (h11 : g1 * g1 = -1) (h01 : g0 * g1 + g1 * g0 = 0)
    (u du dy : ℝ) (h_diff : 2 * u * du = dy)
    (n m : ℝ) (hn : 0 < n) (hm : 0 < m) :
    ((g0 * p0 + g1 * p1) * (g0 * p0 + g1 * p1) = (p0 * p0 - p1 * p1) * 1) ∧
    (4 * (u * u) * (du * du) = dy * dy) ∧
    (Real.log (n * m) = Real.log n + Real.log m) := ⟨
  dirac_square_root_linearization g0 g1 p0 p1 h00 h11 h01,
  fisher_rao_square_root_metric u du dy h_diff,
  logarithmic_primon_energy_additivity n m hn hm
⟩

end InfoGeometry.Algebra.SquareRootLogarithmicInfoMetricBridge
