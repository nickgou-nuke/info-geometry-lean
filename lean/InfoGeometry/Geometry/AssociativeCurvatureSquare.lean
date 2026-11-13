/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.AssociativeGaugeConnection

/-!
# Ordered quadratic, cubic, and quartic curvature terms

This extends the existing associative connection owner. The linear derivative
term and the quadratic commutator term keep both mixed product orders. The
identities are polynomial and require neither commuting coefficients nor
commuting derivations. They do not assert positivity of a curvature action.
-/

namespace InfoGeometry.Geometry.AssociativeGaugeConnection

variable {R A : Type*} [Ring R] [Ring A] [Module R A]

/-- The ordered square of the existing connection curvature. -/
theorem curvature_square_split (D E : Module.End R A) (a b : A) :
    curvature D E a b * curvature D E a b =
      (D b - E a) * (D b - E a) +
      ((D b - E a) * (a * b - b * a) + (a * b - b * a) * (D b - E a)) +
      (a * b - b * a) * (a * b - b * a) := by
  unfold curvature
  noncomm_ring

/-- The two middle quartic terms are kept as separate ordered words. -/
theorem commutator_square_expansion (a b : A) :
    (a * b - b * a) * (a * b - b * a) =
      a * b * a * b - a * (b * b) * a - b * (a * a) * b + b * a * b * a := by
  noncomm_ring

/-- Squaring preserves finite gauge covariance in the same carrier. -/
theorem curvature_square_gauge_covariant (D E : Module.End R A)
    [SMulCommClass R A A]
    (hD : IsLeibniz D) (hE : IsLeibniz E)
    (hcomm : ∀ x, D (E x) = E (D x)) (a b : A) (g : Aˣ) :
    curvature D E (gaugePotential D a g) (gaugePotential E b g) *
      curvature D E (gaugePotential D a g) (gaugePotential E b g) =
      conjugate g (curvature D E a b * curvature D E a b) := by
  rw [curvature_gauge_covariant D E hD hE hcomm, conjugate_mul]

end InfoGeometry.Geometry.AssociativeGaugeConnection
