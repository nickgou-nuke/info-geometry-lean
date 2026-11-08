/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Star.Basic

/-!
# Self-adjointness of Peirce compressions

The compression `P * X * P` is self-adjoint whenever both the cut and the
observable are self-adjoint. The identity is stated for arbitrary associative
star rings; matrices over a star ring are a direct instance.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B] [StarRing B]

/-- A self-adjoint corner cut compresses self-adjoint observables to
self-adjoint elements. -/
theorem star_compression_eq_of_selfAdjoint {P X : B}
    (hP : star P = P) (hX : star X = X) :
    star (P * X * P) = P * X * P := by
  rw [star_mul, star_mul, hP, hX, ← mul_assoc]

end InfoGeometry.OperatorAlgebra.PeirceSpine
