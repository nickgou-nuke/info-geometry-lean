import InfoGeometry.Canonical.SplitSpinFactorHomothetySO55
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Compatibility owner for the upstream homothety path. -/
noncomputable section

namespace InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticHomothety

open InfoGeometry.Canonical.SplitSpinFactorHomothetySO55
open InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticRepresentation

abbrev Zorn := InfoGeometry.Algebra.ZornVectorMatrix ℝ
abbrev V10 := SplitAlbertPeirceZeroQuadraticRepresentation.SplitSpacetime10

abbrev zornPolar := SplitSpinFactorHomothetySO55.zornPolar
abbrev U10Coordinate := SplitSpinFactorHomothetySO55.spinU10

theorem splitInterval10_U10_homothety (u v : V10) :
    splitInterval10 (U10Coordinate u v) =
      (splitInterval10 u) ^ 2 * splitInterval10 v :=
  SplitSpinFactorHomothetySO55.splitInterval10_spinU10_homothety u v

theorem splitInterval10_U10_isometry_of_unit (u : V10)
    (hu : splitInterval10 u = 1) :
    splitInterval10 (U10Coordinate u u) = 1 := by
  rw [splitInterval10_U10_homothety, hu]
  ring

end InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticHomothety
end noncomputable section
