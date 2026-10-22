/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Geometry.PauliParavectorBridge

/-!
# Pauli paravector adjugate readback

The canonical matrix adjugate is the correct paravector conjugation operation
for this finite carrier.  Its product with the Pauli matrix is the Minkowski
quadratic scalar, by Mathlib's adjugate identity and the existing determinant
theorem.  This does not identify the adjugate with Hilbert adjoint.
-/

namespace InfoGeometry.Canonical.PauliParavectorAdjugateBridge

open InfoGeometry.Geometry.PauliParavectorBridge

theorem pauliMatrix_mul_adjugate_eq_q_smul_one (v : Minkowski4) :
    pauliMatrix v * Matrix.adjugate (pauliMatrix v) =
      ((v.q : ℝ) : ℂ) • (1 : PauliMat) := by
  rw [Matrix.mul_adjugate, det_pauliMatrix]

theorem adjugate_mul_pauliMatrix_eq_q_smul_one (v : Minkowski4) :
    Matrix.adjugate (pauliMatrix v) * pauliMatrix v =
      ((v.q : ℝ) : ℂ) • (1 : PauliMat) := by
  rw [Matrix.adjugate_mul, det_pauliMatrix]

theorem pauliMatrix_mul_adjugate_eq_zero_of_null
    {v : Minkowski4} (hv : v.IsNull) :
    pauliMatrix v * Matrix.adjugate (pauliMatrix v) = 0 := by
  rw [pauliMatrix_mul_adjugate_eq_q_smul_one, hv]
  simp

theorem adjugate_mul_pauliMatrix_eq_zero_of_null
    {v : Minkowski4} (hv : v.IsNull) :
    Matrix.adjugate (pauliMatrix v) * pauliMatrix v = 0 := by
  rw [adjugate_mul_pauliMatrix_eq_q_smul_one, hv]
  simp

end InfoGeometry.Canonical.PauliParavectorAdjugateBridge
