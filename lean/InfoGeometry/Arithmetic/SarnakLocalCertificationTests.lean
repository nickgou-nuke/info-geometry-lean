/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Arithmetic.ReflectionZeroCount

namespace InfoGeometry.Arithmetic.SarnakLocalCertificationTests

open SarnakLocalCertification ActualRiemannXiEntireBridge
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry

example (point : ℂ) :
    antiunitaryCriticalReflection (antiunitaryCriticalReflection point) = point :=
  critical_reflection_involutive point

example (point : ℂ) :
    point.re = 1 / 2 ↔ antiunitaryCriticalReflection point = point :=
  (InfoGeometry.Topology.KleinBottleQuotient.critical_reflection_fixed_iff point).symm

example {point : ℂ} (zeroAt : entireRiemannXi point = 0) :
    entireRiemannXi (antiunitaryCriticalReflection point) = 0 :=
  entireRiemannXi_zero_reflection zeroAt

example {point : ℂ} :
    entireRiemannXi point = 0 ↔
      entireRiemannXi (antiunitaryCriticalReflection point) = 0 :=
  entireRiemannXi_zero_reflection_iff point

example : counterexample_f 0 = 0 ∧ (0 : ℂ).re ≠ 1 / 2 :=
  symmetric_zero_can_be_off_horizon

example : ({(0 : ℂ), 1 / 2, 1} : Finset ℂ).card =
    (({(0 : ℂ), 1 / 2, 1} : Finset ℂ).filter fun z => z.re = 1 / 2).card +
      2 * (({(0 : ℂ), 1 / 2, 1} : Finset ℂ).filter fun z => z.re < 1 / 2).card := by
  classical
  apply reflection_card_decomposition
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl <;> norm_num [antiunitaryCriticalReflection]

#print axioms critical_reflection_involutive
#print axioms entireRiemannXi_zero_reflection
#print axioms entireRiemannXi_zero_reflection_iff
#print axioms reflection_card_left_eq_right
#print axioms reflection_card_decomposition
#print axioms reflection_exists_on_line_of_odd_card
#print axioms exists_entireRiemannXi_zero_on_line_of_odd_count
#print axioms symmetric_zero_can_be_off_horizon

end InfoGeometry.Arithmetic.SarnakLocalCertificationTests
