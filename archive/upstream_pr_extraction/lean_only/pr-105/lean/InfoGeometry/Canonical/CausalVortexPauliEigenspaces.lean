/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors.
-/
import InfoGeometry.Canonical.CausalVortexPauliSpectral

/-!
# Explicit eigenspaces of the finite Cooper-pair number operator

The two vectors below are the coordinate eigenmodes of `N = 1 + σ₂`.
The final theorem gives an explicit decomposition of every vector in
`ℂ²` into those two modes; no finite-dimensional existence theorem is used.
-/

namespace CausalVortex

open Matrix
open InfoGeometry.Physics.ChiralPoincareSouriauBridge

def pauliZeroMode : PauliVector := ![Complex.I, 1]

def pauliTwoMode : PauliVector := ![-Complex.I, 1]

theorem pauliZeroMode_number_eq_zero :
    pauliNumberOperator.mulVec pauliZeroMode = 0 := by
  ext i
  fin_cases i <;>
    simp [pauliZeroMode, pauli_number_operator_eq_one_add_sigma2,
      Matrix.mulVec, Matrix.add_apply, Matrix.one_apply, σ2,
      Matrix.vecCons, Complex.I_mul_I]

theorem pauliTwoMode_number_eq_two :
    pauliNumberOperator.mulVec pauliTwoMode =
      (2 : ℂ) • pauliTwoMode := by
  ext i
  fin_cases i <;>
    simp [pauliTwoMode, pauli_number_operator_eq_one_add_sigma2,
      Matrix.mulVec, Matrix.add_apply, Matrix.one_apply, σ2,
      Matrix.vecCons, Complex.I_mul_I] <;>
    ring

theorem pauliZeroMode_projector_fixed :
    pauliProjectorZero.mulVec pauliZeroMode = pauliZeroMode := by
  exact pauliProjectorZero_eigen_iff pauliZeroMode |>.2
    pauliZeroMode_number_eq_zero

theorem pauliTwoMode_projector_fixed :
    pauliProjectorTwo.mulVec pauliTwoMode = pauliTwoMode := by
  exact pauliProjectorTwo_eigen_iff pauliTwoMode |>.2
    pauliTwoMode_number_eq_two

theorem pauliVector_decomposition (v : PauliVector) :
    ∃ a b : ℂ, v = a • pauliZeroMode + b • pauliTwoMode := by
  refine ⟨(v 1 - Complex.I * v 0) / 2,
    (v 1 + Complex.I * v 0) / 2, ?_⟩
  funext i
  fin_cases i <;>
    simp [pauliZeroMode, pauliTwoMode, Matrix.vecCons]
    <;> ring_nf
    <;> simp

theorem pauliVector_decomposition_unique
    {v : PauliVector} {a b c d : ℂ}
    (h : a • pauliZeroMode + b • pauliTwoMode =
      c • pauliZeroMode + d • pauliTwoMode) :
    a = c ∧ b = d := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [pauliZeroMode, pauliTwoMode] at h0 h1
  have hI2 : Complex.I ^ 2 = (-1 : ℂ) := by
    norm_num [pow_two, Complex.I_mul_I]
  have h0' : a - b = c - d := by
    calc
      a - b = (a * Complex.I + -(b * Complex.I)) * (-Complex.I) := by
        ring_nf
        rw [hI2]
        ring
      _ = (c * Complex.I + -(d * Complex.I)) * (-Complex.I) := by
        rw [h0]
      _ = c - d := by
        ring_nf
        rw [hI2]
        ring
  constructor
  · linear_combination (h0' + h1) / 2
  · linear_combination (h1 - h0') / 2

end CausalVortex
