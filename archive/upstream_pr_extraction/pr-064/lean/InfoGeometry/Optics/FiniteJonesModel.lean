/-
InfoGeometry/Optics/FiniteJonesModel.lean

Concrete finite Jones model.

This file contains no physical property assumptions. It defines the concrete
`2 × 2` Jones matrices used by the finite optical branch and proves the basic
projector and Brewster rank-collapse facts directly.
-/

import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Optics.FiniteJonesModel

open scoped Matrix

/-- A finite `2 × 2` Jones matrix. -/
abbrev JonesMat :=
  Matrix (Fin 2) (Fin 2) ℂ

/--
Diagonal Jones matrix.

In the `s/p` basis this is `diag(r_s, r_p)`.
-/
def diagJones (a b : ℂ) : JonesMat :=
  fun i j =>
    if i = j then
      if i = 0 then a else b
    else 0

/-- The `s`-channel projector. -/
def sProjector : JonesMat :=
  diagJones 1 0

/-- The `p`-channel projector. -/
def pProjector : JonesMat :=
  diagJones 0 1

/-- Brewster reflection matrix: the `p` channel is killed. -/
def brewsterMatrix (rs : ℂ) : JonesMat :=
  diagJones rs 0

/-- Concrete `2 × 2` determinant. -/
def det2 (M : JonesMat) : ℂ :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0

/-! ## Entrywise simplification theorems -/

@[simp]
theorem diagJones_00 (a b : ℂ) :
    diagJones a b 0 0 = a := by
  simp [diagJones]

@[simp]
theorem diagJones_11 (a b : ℂ) :
    diagJones a b 1 1 = b := by
  simp [diagJones]

@[simp]
theorem diagJones_01 (a b : ℂ) :
    diagJones a b 0 1 = 0 := by
  simp [diagJones]

@[simp]
theorem diagJones_10 (a b : ℂ) :
    diagJones a b 1 0 = 0 := by
  simp [diagJones]

/-! ## Projector laws -/

/-- The `s` channel is idempotent. -/
theorem sProjector_idem :
    sProjector * sProjector = sProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sProjector, diagJones, Matrix.mul_apply]

/-- The `p` channel is idempotent. -/
theorem pProjector_idem :
    pProjector * pProjector = pProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pProjector, diagJones, Matrix.mul_apply]

/-- The `s` and `p` projectors are disjoint on the left. -/
theorem sProjector_mul_pProjector :
    sProjector * pProjector = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sProjector, pProjector, diagJones, Matrix.mul_apply]

/-- The `s` and `p` projectors are disjoint on the right. -/
theorem pProjector_mul_sProjector :
    pProjector * sProjector = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sProjector, pProjector, diagJones, Matrix.mul_apply]

/-- The `s` and `p` projectors sum to the identity. -/
theorem sProjector_add_pProjector :
    sProjector + pProjector = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sProjector, pProjector, diagJones]

/-- Brewster reflection is a scalar multiple of the `s` projector. -/
theorem brewster_eq_scaled_sProjector
    (rs : ℂ) :
    brewsterMatrix rs = rs • sProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [brewsterMatrix, sProjector, diagJones]

/-! ## Determinant / rank-collapse facts -/

/-- The determinant of a diagonal Jones matrix is the product of its entries. -/
theorem det2_diagJones
    (a b : ℂ) :
    det2 (diagJones a b) = a * b := by
  simp [det2, diagJones]

/-- The Brewster determinant vanishes. -/
theorem det2_brewsterMatrix
    (rs : ℂ) :
    det2 (brewsterMatrix rs) = 0 := by
  simp [brewsterMatrix, det2_diagJones]

/-- Brewster reflection is idempotent up to the scalar `rs`. -/
theorem brewsterMatrix_mul_brewsterMatrix
    (rs : ℂ) :
    brewsterMatrix rs * brewsterMatrix rs = brewsterMatrix (rs * rs) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [brewsterMatrix, diagJones, Matrix.mul_apply]

/--
At `rs = 1`, Brewster reflection is exactly the `s` projector.
-/
theorem brewsterMatrix_one :
    brewsterMatrix 1 = sProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [brewsterMatrix, sProjector, diagJones]

end InfoGeometry.Optics.FiniteJonesModel
