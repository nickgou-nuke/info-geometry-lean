/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSuperoperators.MixedActions

/-!
# Exact vanishing criterion for the mixed Lie–Jordan correction

On the full associative algebra over a commutative ring, the uncorrected
mixed formula holds precisely when every antisymmetric sandwich is killed
by doubling. No commutativity of the algebra or cancellation of two is assumed.
The dependency is `MixedActions.lie_jordan_difference`; the unit input gives
a necessary coefficient-bracket condition, not a sufficient one.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSuperoperators

open InfoGeometry.Core.JordanMultiplicationClosure
attribute [local instance] LieRing.ofAssociativeRing

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

local notation "D" => LieAlgebra.ad R A
local notation "J" => jordanLeft (R := R)

theorem lie_jordan_difference_eq_iff (u v : A) :
    D u * J v - D v * J u = J ⁅u, v⁆ ↔
      ∀ x : A, (2 : ℕ) • (u * x * v - v * x * u) = 0 := by
  rw [lie_jordan_difference, add_eq_left]
  constructor
  · intro h x
    have hx := congrArg (fun T : Module.End R A => T x) h
    simpa only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.mulLeft_apply, LinearMap.mulRight_apply, LinearMap.zero_apply,
      mul_assoc] using hx
  · intro h
    ext x
    simpa only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.mulLeft_apply, LinearMap.mulRight_apply, LinearMap.zero_apply,
      mul_assoc] using h x

theorem lie_jordan_difference_eq_implies_bracket_torsion (u v : A)
    (h : D u * J v - D v * J u = J ⁅u, v⁆) :
    (2 : ℕ) • ⁅u, v⁆ = 0 := by
  simpa only [mul_one, Ring.lie_def] using (lie_jordan_difference_eq_iff u v).mp h 1

theorem lie_jordan_difference_ne_of_bracket_not_torsion (u v : A)
    (h : (2 : ℕ) • ⁅u, v⁆ ≠ 0) :
    D u * J v - D v * J u ≠ J ⁅u, v⁆ :=
  fun he => h (lie_jordan_difference_eq_implies_bracket_torsion u v he)

end InfoGeometry.OperatorAlgebra.PeirceSuperoperators
