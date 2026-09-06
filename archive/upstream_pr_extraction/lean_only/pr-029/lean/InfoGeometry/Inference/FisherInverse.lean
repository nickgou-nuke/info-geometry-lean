/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import InfoGeometry.Inference.FisherPositivity

/-!
# Conditional inverse-Fisher sensitivity contract

Positive semidefiniteness is not enough to define a covariance matrix. This
module makes the missing nonsingularity condition explicit and records the
inverse identities used by local sensitivity reporting.
-/

namespace InfoGeometry.Inference

structure FisherInverseContract
    (I : Matrix (Fin 2) (Fin 2) ℝ) where
  positiveDefinite : I.PosDef
  determinant_isUnit : IsUnit I.det

noncomputable def localCovariance
    (I : Matrix (Fin 2) (Fin 2) ℝ)
    (hI : FisherInverseContract I) : Matrix (Fin 2) (Fin 2) ℝ :=
  by
    classical
    exact if IsUnit I.det then I⁻¹ else 0

theorem fisher_mul_localCovariance
    (I : Matrix (Fin 2) (Fin 2) ℝ)
    (hI : FisherInverseContract I) :
    I * localCovariance I hI = 1 := by
  classical
  rw [localCovariance, if_pos hI.determinant_isUnit]
  exact Matrix.mul_nonsing_inv I hI.determinant_isUnit

theorem localCovariance_mul_fisher
    (I : Matrix (Fin 2) (Fin 2) ℝ)
    (hI : FisherInverseContract I) :
    localCovariance I hI * I = 1 := by
  classical
  rw [localCovariance, if_pos hI.determinant_isUnit]
  exact Matrix.nonsing_inv_mul I hI.determinant_isUnit

theorem fisher_inverse_contract_requires_nonsingularity
    (I : Matrix (Fin 2) (Fin 2) ℝ)
    (hI : FisherInverseContract I) :
    IsUnit I.det :=
  hI.determinant_isUnit

end InfoGeometry.Inference
