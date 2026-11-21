/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitSpinFactorHomothetySO55
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Compatibility owner for the upstream homothety path. -/
noncomputable section

namespace InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticHomothety

open InfoGeometry.Canonical.SplitSpinFactorHomothetySO55
open InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticRepresentation
open InfoGeometry.Canonical.SplitAlbertTripotentPeirceBoundary

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

theorem splitInterval10_U10_isometry_of_neg_unit (u v : V10)
    (hu : splitInterval10 u = -1) :
    splitInterval10 (U10Coordinate u v) = splitInterval10 v := by
  rw [splitInterval10_U10_homothety, hu]
  ring

theorem splitInterval10_U10_null_image (u v : V10)
    (hu : splitInterval10 u = 0) :
    splitInterval10 (U10Coordinate u v) = 0 := by
  rw [splitInterval10_U10_homothety, hu]
  ring

/-- The native split-octonion polar form is symmetric. -/
theorem zornPolar_comm (x y : Zorn) :
    zornPolar x y = zornPolar y x := by
  exact SplitSpinFactorHomothetySO55.zornPolar_symm x y

/-- The homothety theorem in the diagonal `(5,5)` quadratic readout. -/
theorem q55Real_U10_readout (u v : V10) :
    q55Real (h2ToVec55 (U10Coordinate u v).1.1 (U10Coordinate u v).1.2
      (U10Coordinate u v).2) =
      splitInterval10 u ^ 2 * q55Real (h2ToVec55 v.1.1 v.1.2 v.2) := by
  rw [← splitInterval10_eq_q55Real (U10Coordinate u v),
    splitInterval10_U10_homothety]
  simp_rw [splitInterval10_eq_q55Real]

end InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticHomothety
end noncomputable section
