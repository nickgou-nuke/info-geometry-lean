import InfoGeometry.IndexTheory.AtiyahSingerDirac

namespace InfoGeometry.Canonical.AtiyahSingerDiracCapstone

open InfoGeometry.IndexTheory.AtiyahSingerDirac

theorem capstone_atiyah_singer_dirac_synthesis (d_xi d_theta : ℝ) (k : ℤ) :
    ((1 / 2) * (d_xi + d_theta) - (1 / 2) * (d_xi - d_theta) = d_theta) ∧
    (analyticDiracIndex 1 1 = 0) ∧
    (topologicalDiracIndex 0 = 0) ∧
    (analyticDiracIndex k 0 = topologicalDiracIndex k) ∧
    (aHatGenusCylinder * (firstChernClassFlux k : ℝ) = ((topologicalDiracIndex k : ℤ) : ℝ)) :=
  grand_atiyah_singer_dirac_synthesis d_xi d_theta k

end InfoGeometry.Canonical.AtiyahSingerDiracCapstone
