/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Physics.FiniteMetriplecticDynamics
import InfoGeometry.OperatorAlgebra.RealMatrixSplit

/-!
# Connecting the existing metriplectic split to native matrix adjoints

The established `symmetricPart` and `antisymmetricPart`, their transpose
laws, reconstruction, and uniqueness remain in `FiniteMetriplecticDynamics`.
These equalities identify that API with Mathlib's real-linear split and
transport the full noncommutative normality defect to its existing users.
-/

namespace InfoGeometry.Physics

open OperatorAlgebra.RealMatrixSplit

variable {n : Type*}

/-- The existing symmetric component is the native self-adjoint component. -/
theorem symmetricPart_eq_selfAdjointPart (M : Matrix n n ℝ) :
    symmetricPart M = (selfAdjointPart ℝ M : Matrix n n ℝ) := by
  rw [selfAdjointPart_eq_half]
  rfl

/-- The existing antisymmetric component is the native skew-adjoint component. -/
theorem antisymmetricPart_eq_skewAdjointPart (M : Matrix n n ℝ) :
    antisymmetricPart M = (skewAdjointPart ℝ M : Matrix n n ℝ) := by
  rw [skewAdjointPart_eq_half]
  rfl

variable [Fintype n] [DecidableEq n]

/-- The old split preserves the exact ordered matrix commutator. -/
theorem symmetricPart_antisymmetricPart_normal_defect (M : Matrix n n ℝ) :
    M.transpose * M - M * M.transpose =
      (2 : ℝ) • (symmetricPart M * antisymmetricPart M -
        antisymmetricPart M * symmetricPart M) := by
  simpa only [symmetricPart_eq_selfAdjointPart, antisymmetricPart_eq_skewAdjointPart]
    using transpose_normal_defect M

/-- The existing parts commute precisely for transpose-normal matrices. -/
theorem symmetricPart_antisymmetricPart_commute_iff (M : Matrix n n ℝ) :
    Commute (symmetricPart M) (antisymmetricPart M) ↔ IsStarNormal M := by
  simpa only [symmetricPart_eq_selfAdjointPart, antisymmetricPart_eq_skewAdjointPart]
    using (isStarNormal_iff_parts_commute M).symm

end InfoGeometry.Physics
