/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Matrix.Basic

/-!
# TCS parameter sensitivity and Fisher information

The TCS raw-count mean is `T * (C * X - K * X^2)`. This module records its
exact coordinate sensitivities and the corresponding finite weighted Fisher
matrix. It does not identify the inverse Fisher matrix with an uncertainty
estimate without an additional statistical regularity contract.
-/

open scoped BigOperators

namespace InfoGeometry.Inference

variable {Data : Type*} [Fintype Data]

/-- Raw-count TCS mean as a function of the two physical coefficients. -/
def tcsMeanAt (liveTime x C K : ℝ) : ℝ :=
  liveTime * (C * x - K * x ^ 2)

/-- Coordinate sensitivity of the TCS mean with respect to `(C, K)`. -/
def tcsSensitivity (liveTime x : ℝ) : Fin 2 → ℝ
  | 0 => liveTime * x
  | 1 => -(liveTime * x ^ 2)

theorem hasDerivAt_tcsMeanAt_C
    (liveTime x C K : ℝ) :
    HasDerivAt (fun c => tcsMeanAt liveTime x c K)
      (tcsSensitivity liveTime x 0) C := by
  unfold tcsMeanAt tcsSensitivity
  convert
    (((hasDerivAt_id' C).mul_const x).sub_const (K * x ^ 2)).const_mul liveTime
    using 1 <;> ring

theorem hasDerivAt_tcsMeanAt_K
    (liveTime x C K : ℝ) :
    HasDerivAt (fun k => tcsMeanAt liveTime x C k)
      (tcsSensitivity liveTime x 1) K := by
  unfold tcsMeanAt tcsSensitivity
  convert
    ((hasDerivAt_const K (C * x)).sub ((hasDerivAt_id' K).mul_const (x ^ 2))).const_mul liveTime
    using 1 <;> ring

/-- Finite weighted Fisher-information matrix from sensitivity vectors. -/
noncomputable def fisherInformation
    (w : Data → ℝ) (sensitivity : Data → Fin 2 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun a b => ∑ i : Data, w i * sensitivity i a * sensitivity i b

theorem fisherInformation_apply
    (w : Data → ℝ) (sensitivity : Data → Fin 2 → ℝ)
    (a b : Fin 2) :
    fisherInformation w sensitivity a b =
      ∑ i : Data, w i * sensitivity i a * sensitivity i b := rfl

theorem fisherInformation_symmetric
    (w : Data → ℝ) (sensitivity : Data → Fin 2 → ℝ) :
    Matrix.transpose (fisherInformation w sensitivity) =
      fisherInformation w sensitivity := by
  funext a b
  simp only [Matrix.transpose_apply, fisherInformation]
  congr 1
  funext i
  ring

/-- TCS Fisher information using the physical sensitivity vector. -/
noncomputable def tcsFisherInformation
    (w : Data → ℝ) (liveTime x : Data → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fisherInformation w (fun i => tcsSensitivity (liveTime i) (x i))

end InfoGeometry.Inference
