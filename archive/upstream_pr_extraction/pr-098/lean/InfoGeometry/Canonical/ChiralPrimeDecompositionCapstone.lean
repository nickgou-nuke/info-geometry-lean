import InfoGeometry.LightCone.ChiralPrimeDecomposition

namespace InfoGeometry.Canonical.ChiralPrimeDecompositionCapstone

open InfoGeometry.LightCone.ChiralPrimeDecomposition

theorem capstone_chiral_prime_decomposition_synthesis (d_chi d_theta : ℝ) :
    (chiralLeftGen d_chi d_theta - chiralRightGen d_chi d_theta = d_theta) ∧
    (chiralLeftGen d_chi d_theta + chiralRightGen d_chi d_theta = d_chi) :=
  grand_chiral_prime_decomposition_synthesis d_chi d_theta

end InfoGeometry.Canonical.ChiralPrimeDecompositionCapstone
