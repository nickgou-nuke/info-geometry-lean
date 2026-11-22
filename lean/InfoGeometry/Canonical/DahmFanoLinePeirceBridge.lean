/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NoncommRing

/-!
# A Fano-line involution identity in an associative ring

The proved result is the square identity for a sum of commuting involutions.
It works in an arbitrary associative ring. It does not construct division by
`2` or `4`, a spinor module, a projective incidence geometry, or a map from
Fano points to Peirce corners.

## Three-Bucket Audit Map

- **BUCKET 1 (Proved):** the sum-square identity and four-scaled joint Peirce
  decomposition in arbitrary `[Ring R]`.
- **BUCKET 2 (Conditional):** The identity assumes both elements square to `1`
  and commute; these hypotheses are not constructed from a Clifford or Fano model.
- **BUCKET 3 (Open):** a spinor ideal, finite projective
  incidence counts, and a map into the three-horizon Peirce decomposition.
-/

namespace InfoGeometry.Canonical.DahmFanoLinePeirceBridge

universe u
variable {R : Type u} [Ring R]

/-- The square of the sum of two commuting involutions is twice one plus
their product. This is a denominator-free identity. -/
theorem commuting_involutions_sum_square
    (A C : R) (hA : A * A = 1) (hC : C * C = 1)
    (hAC : A * C = C * A) :
    (A + C) * (A + C) = 2 • (1 + A * C) := by
  have hCA : C * A = A * C := hAC.symm
  noncomm_ring [hA, hC, hCA]

/-- The positive eigenspace numerator of an involution squares to twice itself. -/
theorem involution_positive_numerator_square
    (A : R) (hA : A * A = 1) :
    (1 + A) * (1 + A) = (1 + A) + (1 + A) := by
  noncomm_ring [hA]

/-- The negative eigenspace numerator of an involution squares to twice itself. -/
theorem involution_negative_numerator_square
    (A : R) (hA : A * A = 1) :
    (1 - A) * (1 - A) = (1 - A) + (1 - A) := by
  noncomm_ring [hA]

/-- Product rule for four-cleared eigenspace numerators: when two factors
commute and each squares to twice itself, their product squares to four times
itself, written without division or an external scalar field. -/
theorem commuting_twice_idempotents_product
    (x y : R) (hx : x * x = x + x) (hy : y * y = y + y)
    (hxy : x * y = y * x) :
    (x * y) * (x * y) = x * y + x * y + x * y + x * y := by
  calc
    (x * y) * (x * y) = x * (y * x) * y := by noncomm_ring
    _ = x * (x * y) * y := by rw [hxy]
    _ = (x * x) * (y * y) := by noncomm_ring
    _ = (x + x) * (y + y) := by rw [hx, hy]
    _ = x * y + x * y + x * y + x * y := by noncomm_ring

/-- The four-cleared joint `(+,+)` eigenspace numerator is four-scaled
idempotent for a commuting pair of involutions. -/
theorem commuting_involutions_joint_positive_four_scaled_idempotent
    (A C : R) (hA : A * A = 1) (hC : C * C = 1)
    (hAC : A * C = C * A) :
    ((1 + A) * (1 + C)) * ((1 + A) * (1 + C)) =
      ((1 + A) * (1 + C)) + ((1 + A) * (1 + C)) +
        ((1 + A) * (1 + C)) + ((1 + A) * (1 + C)) := by
  apply commuting_twice_idempotents_product
  · exact involution_positive_numerator_square A hA
  · exact involution_positive_numerator_square C hC
  · noncomm_ring [hAC]

/-- The four-cleared joint `(-,-)` eigenspace numerator is four-scaled
idempotent for a commuting pair of involutions. -/
theorem commuting_involutions_joint_negative_four_scaled_idempotent
    (A C : R) (hA : A * A = 1) (hC : C * C = 1)
    (hAC : A * C = C * A) :
    ((1 - A) * (1 - C)) * ((1 - A) * (1 - C)) =
      ((1 - A) * (1 - C)) + ((1 - A) * (1 - C)) +
        ((1 - A) * (1 - C)) + ((1 - A) * (1 - C)) := by
  apply commuting_twice_idempotents_product
  · exact involution_negative_numerator_square A hA
  · exact involution_negative_numerator_square C hC
  · noncomm_ring [hAC]

/-- The four-cleared mixed `(+,-)` eigenspace numerator is four-scaled
idempotent for a commuting pair of involutions. -/
theorem commuting_involutions_joint_positive_negative_four_scaled_idempotent
    (A C : R) (hA : A * A = 1) (hC : C * C = 1)
    (hAC : A * C = C * A) :
    ((1 + A) * (1 - C)) * ((1 + A) * (1 - C)) =
      ((1 + A) * (1 - C)) + ((1 + A) * (1 - C)) +
        ((1 + A) * (1 - C)) + ((1 + A) * (1 - C)) := by
  apply commuting_twice_idempotents_product
  · exact involution_positive_numerator_square A hA
  · exact involution_negative_numerator_square C hC
  · noncomm_ring [hAC]

/-- The four-cleared mixed `(-,+)` eigenspace numerator is four-scaled
idempotent for a commuting pair of involutions. -/
theorem commuting_involutions_joint_negative_positive_four_scaled_idempotent
    (A C : R) (hA : A * A = 1) (hC : C * C = 1)
    (hAC : A * C = C * A) :
    ((1 - A) * (1 + C)) * ((1 - A) * (1 + C)) =
      ((1 - A) * (1 + C)) + ((1 - A) * (1 + C)) +
        ((1 - A) * (1 + C)) + ((1 - A) * (1 + C)) := by
  apply commuting_twice_idempotents_product
  · exact involution_negative_numerator_square A hA
  · exact involution_positive_numerator_square C hC
  · noncomm_ring [hAC]

end InfoGeometry.Canonical.DahmFanoLinePeirceBridge
