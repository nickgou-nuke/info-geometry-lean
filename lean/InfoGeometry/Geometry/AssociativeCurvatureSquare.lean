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

/-- The two middle quartic terms are kept as separate ordered words. -/
theorem commutator_square_expansion (a b : A) :
    (a * b - b * a) * (a * b - b * a) =
      a * b * a * b - a * (b * b) * a - b * (a * a) * b + b * a * b * a := by
  noncomm_ring

end InfoGeometry.Geometry.AssociativeGaugeConnection
