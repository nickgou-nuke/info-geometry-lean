import InfoGeometry.Spectral.RiemannVonMangoldtStaircase
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.RiemannVonMangoldtStaircaseCapstone

open InfoGeometry.Spectral.RiemannVonMangoldtStaircase

theorem capstone_riemann_von_mangoldt_staircase_synthesis (E : ℝ) (hE : 0 < E) :
    HasDerivAt smoothZeroStaircase
      ((1 / (2 * Real.pi)) * Real.log (E / (2 * Real.pi))) E := by
  exact smooth_staircase_deriv E hE

end InfoGeometry.Canonical.RiemannVonMangoldtStaircaseCapstone
