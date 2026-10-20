/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.QDeformedCommutatorCanonical
import InfoGeometry.Algebraic.JordanCliffordLieSplit

/-!
# Scalar q-exchange and the canonical Jordan--Lie channels

This module connects the existing homogeneous q-exchange owner to the
repository's normalized Jordan and Lie products.  The coefficient is a real
scalar acting on the algebra; no new operator carrier is introduced.
-/

namespace InfoGeometry.Algebra.QDeformedJordanLieBridgeWave21

open InfoGeometry.Algebraic

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Scalar-coefficient homogeneous q-exchange in an ℝ-algebra. -/
def ScalarQCommutes (q : ℝ) (X Y : A) : Prop :=
  X * Y = q • (Y * X)

/-- Scalar q-exchange is exactly the canonical algebra-coefficient relation
after transporting the scalar through the algebra structure. -/
theorem scalarQCommutes_iff_canonical (q : ℝ) (X Y : A) :
    ScalarQCommutes q X Y ↔
      InfoGeometry.Algebra.QDeformedCommutatorCanonical.QCommutes
        (algebraMap ℝ A q) X Y := by
  unfold ScalarQCommutes
  unfold InfoGeometry.Algebra.QDeformedCommutatorCanonical.QCommutes
  simp only [Algebra.smul_def]

/-- The q-exchange relation gives the division-free Jordan--Lie balance. -/
theorem jordan_lie_balance_of_scalarQCommutes (q : ℝ) (X Y : A)
    (h : ScalarQCommutes q X Y) :
    (q + 1) • lieBracket X Y = (q - 1) • jordanProduct X Y := by
  unfold ScalarQCommutes at h
  unfold lieBracket jordanProduct
  rw [h]
  module

/-- At q = 1, homogeneous exchange kills the Lie channel. -/
theorem lieBracket_eq_zero_of_scalarQCommutes_one (X Y : A)
    (h : ScalarQCommutes 1 X Y) : lieBracket X Y = 0 := by
  have hb := jordan_lie_balance_of_scalarQCommutes 1 X Y h
  simpa using hb

/-- At q = -1, homogeneous exchange kills the Jordan channel. -/
theorem jordanProduct_eq_zero_of_scalarQCommutes_neg_one (X Y : A)
    (h : ScalarQCommutes (-1) X Y) : jordanProduct X Y = 0 := by
  unfold ScalarQCommutes at h
  unfold jordanProduct
  rw [h]
  module

end InfoGeometry.Algebra.QDeformedJordanLieBridgeWave21
