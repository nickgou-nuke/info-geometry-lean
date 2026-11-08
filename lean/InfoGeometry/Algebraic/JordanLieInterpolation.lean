/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebraic.JordanCliffordLieSplit

/-!
# Affine Jordan–Lie interpolation

The normalized two-channel exchange is expressed in the repository's
canonical Jordan and Lie products.
-/

namespace InfoGeometry.Algebraic

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The normalized two-channel interpolation preserves the Jordan component
and scales the Lie component by the contrast parameter. -/
theorem affine_jordan_lie_interpolation (q : ℝ) (a b : A) :
    ((1 + q) / 2 : ℝ) • (a * b) + ((1 - q) / 2 : ℝ) • (b * a) =
      jordanProduct a b + q • lieBracket a b := by
  unfold jordanProduct lieBracket
  simp [smul_add, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  module

end InfoGeometry.Algebraic
