/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Arithmetic.ActualRiemannXiEntireSchwarzBridge
import InfoGeometry.Arithmetic.ZetaSymmetryHeuristicComplement
import InfoGeometry.Arithmetic.RiemannLectureDependencies
import InfoGeometry.Arithmetic.SarnakLocalCertification

namespace InfoGeometry.Arithmetic.ActualRiemannXiLocalZeroTests

open ActualRiemannXiEntireBridge ActualRiemannXiEntireSchwarzBridge
open ZetaSymmetryHeuristicComplement

example {point : ℂ} (zero_at_point : entireRiemannXi point = 0) :
    entireRiemannXi (InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.antiunitaryCriticalReflection point) = 0 :=
  SarnakLocalCertification.entireRiemannXi_zero_reflection zero_at_point

example : ∃ function : ℂ → ℂ, ∃ point : ℂ,
    EvenCentered function ∧ ZeroAt function point ∧
      ZeroAt function (-point) ∧ point.re ≠ 0 :=
  even_symmetry_allows_off_axis_zero_pair

#print axioms even_symmetry_allows_off_axis_zero_pair
#print axioms RiemannLectureDependencies.arithmetic_branch
#print axioms RiemannLectureDependencies.symmetry_branch
#print axioms RiemannLectureDependencies.finite_zero_pairing_branch
#print axioms RiemannLectureDependencies.arithmetic_and_finite_zero_pairing_incomparable
#print axioms RiemannLectureDependencies.no_cycle
#print axioms SarnakLocalCertification.entireRiemannXi_zero_reflection
#print axioms SarnakLocalCertification.entireRiemannXi_zero_reflection_iff
#print axioms SarnakLocalCertification.symmetric_functions_need_not_have_critical_zeros

end InfoGeometry.Arithmetic.ActualRiemannXiLocalZeroTests
