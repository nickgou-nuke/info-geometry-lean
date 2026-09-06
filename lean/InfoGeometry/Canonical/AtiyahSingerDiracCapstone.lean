import InfoGeometry.IndexTheory.AtiyahSingerDirac

namespace InfoGeometry.Canonical.AtiyahSingerDiracCapstone

open InfoGeometry.IndexTheory.AtiyahSingerDirac

theorem capstone_atiyah_singer_dirac_synthesis (d_xi d_theta : ℝ) (k : ℤ) :
    ((1 / 2) * (d_xi + d_theta) - (1 / 2) * (d_xi - d_theta) = d_theta) ∧
    (analyticDiracIndex 1 1 = 0) ∧
    (topologicalDiracIndex 0 = 0) ∧
    (analyticDiracIndex k 0 = topologicalDiracIndex k) ∧
    (aHatGenusCylinder * (firstChernClassFlux k : ℝ) = ((topologicalDiracIndex k : ℤ) : ℝ)) := by
  exact ⟨dirac_light_cone_reduction d_xi d_theta,
    analytic_index_vacuum_zero,
    topological_index_vacuum_zero,
    atiyah_singer_index_theorem_match k,
    atiyah_singer_integral_identity k⟩

end InfoGeometry.Canonical.AtiyahSingerDiracCapstone
