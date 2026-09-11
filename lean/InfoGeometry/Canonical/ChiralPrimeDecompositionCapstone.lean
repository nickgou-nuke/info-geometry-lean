import InfoGeometry.LightCone.ChiralPrimeDecomposition
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.ChiralPrimeDecompositionCapstone

open InfoGeometry.LightCone.ChiralPrimeDecomposition

/-! The two chiral generators are the canonical half-sum/half-difference
coordinates for scaling and angular directions. -/
theorem capstone_chiral_prime_decomposition_synthesis (d_chi d_theta : ℝ) :
    (chiralLeftGen d_chi d_theta - chiralRightGen d_chi d_theta = d_theta) ∧
    (chiralLeftGen d_chi d_theta + chiralRightGen d_chi d_theta = d_chi) := by
  exact ⟨angular_generator_decomposition d_chi d_theta,
    scaling_generator_decomposition d_chi d_theta⟩

end InfoGeometry.Canonical.ChiralPrimeDecompositionCapstone
