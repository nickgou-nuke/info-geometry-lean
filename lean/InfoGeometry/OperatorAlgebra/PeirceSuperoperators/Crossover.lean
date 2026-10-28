/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceGrading
import InfoGeometry.OperatorAlgebra.PeirceSuperoperators.MixedActions

/-!
# Identity and reflection crossover for opposite Peirce corners

The four evaluations use native inner Lie and Jordan actions. The reflection
is the existing Peirce reflection, and the two coefficients are actual
oppositely oriented corner components. No star, inverse normalization, or
restriction on the characteristic is needed.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSuperoperators

open InfoGeometry.Core.JordanMultiplicationClosure
open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.Core.PeirceGrading

attribute [local instance] LieRing.ofAssociativeRing

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

local notation "D" => LieAlgebra.ad R A
local notation "J" => jordanLeft (R := R)

/-- The negative symmetric double inner action annihilates the unit. -/
theorem double_lie_one (u v : A) :
    (-(D u * D v + D v * D u)) 1 = 0 := by
  change -(⁅u, ⁅v, (1 : A)⁆⁆ + ⁅v, ⁅u, (1 : A)⁆⁆) = 0
  simp only [Ring.lie_def, mul_one, one_mul, sub_self, mul_zero, zero_mul,
    add_zero, neg_zero]

/-- The mixed difference sends the unit to four times the coefficient bracket. -/
theorem mixed_difference_one (u v : A) :
    (D u * J v - D v * J u) 1 = 4 • ⁅u, v⁆ := by
  change (u * (v * 1 + 1 * v) - (v * 1 + 1 * v) * u) -
    (v * (u * 1 + 1 * u) - (u * 1 + 1 * u) * v) = 4 • (u * v - v * u)
  simp only [mul_one, one_mul, nsmul_eq_mul]
  noncomm_ring

/-- The upper directed corner has negative reflection weight for the inner action. -/
theorem lie_component10_reflection {p : A} (hp : IsIdempotentElem p) (a : A) :
    D (component10 p a) (reflection p) = -(2 • component10 p a) := by
  change (p * a * (1 - p)) * (2 * p - 1) -
    (2 * p - 1) * (p * a * (1 - p)) = -(2 • (p * a * (1 - p)))
  simp only [two_nsmul]
  noncomm_ring [hp.eq, idempotent_mul_nested p hp.eq]

/-- The lower directed corner has positive reflection weight for the inner action. -/
theorem lie_component01_reflection {p : A} (hp : IsIdempotentElem p) (a : A) :
    D (component01 p a) (reflection p) = 2 • component01 p a := by
  change ((1 - p) * a * p) * (2 * p - 1) -
    (2 * p - 1) * ((1 - p) * a * p) = 2 • ((1 - p) * a * p)
  simp only [two_nsmul]
  noncomm_ring [hp.eq, idempotent_mul_nested p hp.eq]

/-- Upper corner Jordan multiplication annihilates the actual reflection. -/
theorem jordan_component10_reflection {p : A} (hp : IsIdempotentElem p) (a : A) :
    J (component10 p a) (reflection p) = 0 := by
  change (p * a * (1 - p)) * (2 * p - 1) +
    (2 * p - 1) * (p * a * (1 - p)) = 0
  noncomm_ring [hp.eq, idempotent_mul_nested p hp.eq]

/-- Lower corner Jordan multiplication annihilates the actual reflection. -/
theorem jordan_component01_reflection {p : A} (hp : IsIdempotentElem p) (a : A) :
    J (component01 p a) (reflection p) = 0 := by
  change ((1 - p) * a * p) * (2 * p - 1) +
    (2 * p - 1) * ((1 - p) * a * p) = 0
  noncomm_ring [hp.eq, idempotent_mul_nested p hp.eq]

/-- The mixed difference vanishes on the reflection at its inner Jordan actions. -/
theorem mixed_difference_reflection {p : A} (hp : IsIdempotentElem p) (a b : A) :
    (D (component10 p a) * J (component01 p b) -
      D (component01 p b) * J (component10 p a)) (reflection p) = 0 := by
  change D (component10 p a) (J (component01 p b) (reflection p)) -
    D (component01 p b) (J (component10 p a) (reflection p)) = 0
  rw [jordan_component01_reflection hp, jordan_component10_reflection hp]
  rw [map_zero, map_zero, sub_self]

/-- Opposite corner orientation fixes the sign of the double-action crossover. -/
theorem double_lie_reflection {p : A} (hp : IsIdempotentElem p) (a b : A) :
    (-(D (component10 p a) * D (component01 p b) +
      D (component01 p b) * D (component10 p a))) (reflection p) =
        -(4 • ⁅component10 p a, component01 p b⁆) := by
  change -(D (component10 p a) (D (component01 p b) (reflection p)) +
    D (component01 p b) (D (component10 p a) (reflection p))) = _
  rw [lie_component01_reflection hp, lie_component10_reflection hp,
    map_nsmul, map_neg, map_nsmul]
  simp only [LieAlgebra.ad_apply]
  rw [lie_skew (component01 p b) (component10 p a)]
  abel

end InfoGeometry.OperatorAlgebra.PeirceSuperoperators

