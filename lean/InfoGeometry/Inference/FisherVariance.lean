/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.FisherInverse
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Local variance from inverse Fisher information

This module formalizes the local quadratic sensitivity variance associated with
an inverse Fisher information matrix. It does not assert a global confidence
theorem or identify the inverse with an exact finite-sample covariance.
-/

namespace InfoGeometry.Inference

noncomputable def localVariance
    (I : Matrix (Fin 2) (Fin 2) ℝ)
    (hI : FisherInverseContract I)
    (v : Fin 2 → ℝ) : ℝ :=
  dotProduct v (Matrix.mulVec (localCovariance I hI) v)

theorem localVariance_nonneg
    (I : Matrix (Fin 2) (Fin 2) ℝ)
    (hI : FisherInverseContract I)
    (v : Fin 2 → ℝ) :
    0 ≤ localVariance I hI v := by
  classical
  by_cases hv : v = 0
  · simp [localVariance, hv]
  · rw [localVariance, localCovariance, if_pos hI.determinant_isUnit]
    exact le_of_lt (hI.positiveDefinite.inv.dotProduct_mulVec_pos hv)

theorem localVariance_pos
    (I : Matrix (Fin 2) (Fin 2) ℝ)
    (hI : FisherInverseContract I)
    {v : Fin 2 → ℝ} (hv : v ≠ 0) :
    0 < localVariance I hI v := by
  rw [localVariance, localCovariance, if_pos hI.determinant_isUnit]
  exact hI.positiveDefinite.inv.dotProduct_mulVec_pos hv

theorem localVariance_zero_direction
    (I : Matrix (Fin 2) (Fin 2) ℝ)
    (hI : FisherInverseContract I) :
    localVariance I hI 0 = 0 := by
  simp [localVariance]

end InfoGeometry.Inference
