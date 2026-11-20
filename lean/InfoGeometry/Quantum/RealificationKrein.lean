/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.RealificationPhaseGrading
import InfoGeometry.Quantum.NeutralKreinMajoranaFrame

/-!
# Internal phase, conjugation, and Krein metric compatibility

The positive Hilbert adjoint remains matrix transpose. For a fundamental
symmetry `eta`, its Krein counterpart is the sandwich `eta * Tᵀ * eta`.
Commutation and anticommutation with the phase axis give different answers.
The existing neutral frame is explicitly in the anticommuting case.

The existing sheet grading implements complex conjugation on the realified
matrix image. It is not Clifford parity: a Clifford bivector is even, whereas
this conjugation reverses the phase axis.
-/

noncomputable section

open Matrix

namespace InfoGeometry.Quantum.Realification

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A commuting fundamental symmetry makes the phase generator Krein-skew. -/
theorem internalJ_krein_skew (η : Matrix (n ⊕ n) (n ⊕ n) ℝ)
    (hη : η * η = 1) (hJ : Commute η internalJ) :
    η * internalJ.transpose * η = -internalJ := by
  rw [internalJ_transpose, mul_neg, neg_mul, hJ.eq, mul_assoc, hη, mul_one]

/-- With a compatible metric, the actual phase rotor preserves the metric. -/
theorem internalRotor_preserves_metric (η : Matrix (n ⊕ n) (n ⊕ n) ℝ)
    (hJ : Commute η internalJ) (θ : ℝ) :
    (internalRotor θ).transpose * η * internalRotor θ = η := by
  have hc := (commute_internalScalar η hJ (Real.cos (-θ)) (Real.sin (-θ))).eq
  change η * internalRotor (-θ) = internalRotor (-θ) * η at hc
  rw [internalRotor_transpose, ← hc, mul_assoc, internalRotor_add,
    neg_add_cancel, internalRotor_zero, mul_one]

/-- An anticommuting fundamental symmetry instead makes `J` Krein-self-adjoint. -/
theorem internalJ_krein_self_of_anticommute (η : Matrix (n ⊕ n) (n ⊕ n) ℝ)
    (hη : η * η = 1) (hJ : η * internalJ = -(internalJ * η)) :
    η * internalJ.transpose * η = internalJ := by
  rw [internalJ_transpose, mul_neg, hJ, neg_neg, mul_assoc, hη, mul_one]

/-- The same anticommuting convention makes the phase axis an anti-isometry. -/
theorem internalJ_metric_anti_isometry (η : Matrix (n ⊕ n) (n ⊕ n) ℝ)
    (hJ : η * internalJ = -(internalJ * η)) :
    internalJ.transpose * η * internalJ = -η := by
  rw [internalJ_transpose, neg_mul, neg_mul, mul_assoc, hJ, mul_neg, neg_neg,
    ← mul_assoc, internalJ_sq, neg_one_mul]

namespace NeutralFrame

open InfoGeometry.Quantum.NeutralKreinMajoranaFrame

/-- The existing Majorana convention is the negative of the chosen phase axis. -/
theorem internalJ_eq_neg_majoranaForm (k : ℕ) :
    internalJ (n := Fin k) = -majoranaForm k := by
  ext i j
  cases i <;> cases j <;> simp [internalJ, majoranaForm]

/-- The sheet grading reverses the internal phase. -/
theorem grading_internalJ_anticommute (k : ℕ) :
    grading k * internalJ = -(internalJ * grading k) := by
  simp only [grading, internalJ, Matrix.fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;> simp [Matrix.one_apply]

/-- The existing neutral metric also anticommutes with the phase. -/
theorem metric_internalJ_anticommute (k : ℕ) :
    kreinMetric k * internalJ = -(internalJ * kreinMetric k) := by
  simp only [kreinMetric, internalJ, Matrix.fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;> simp [Matrix.one_apply]

/-- For the repository's neutral metric, the phase is Krein-self-adjoint. -/
theorem internalJ_krein_self (k : ℕ) :
    kreinMetric k * internalJ.transpose * kreinMetric k = internalJ :=
  internalJ_krein_self_of_anticommute _ (exchange_sq k)
    (metric_internalJ_anticommute k)

/-- Preserve the neutral convention: the phase axis reverses this metric. -/
theorem internalJ_anti_isometry (k : ℕ) :
    internalJ.transpose * kreinMetric k * internalJ = -kreinMetric k :=
  internalJ_metric_anti_isometry _ (metric_internalJ_anticommute k)

/-- Complex conjugation is a real sandwich by the existing sheet grading. -/
theorem grading_realify_conjugate (k : ℕ) (A : Matrix (Fin k) (Fin k) ℂ) :
    grading k * realify A * grading k = realify (A.map star) := by
  simp only [grading, realify, Matrix.fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;> simp

/-- The sheet conjugation reverses a phase rotor, unlike Clifford parity. -/
theorem grading_internalRotor (k : ℕ) (θ : ℝ) :
    grading k * internalRotor θ * grading k = internalRotor (-θ) := by
  have hJ : grading k * internalJ * grading k = -(internalJ (n := Fin k)) := by
    rw [grading_internalJ_anticommute, neg_mul, mul_assoc, grading_sq, mul_one]
  simp only [internalRotor, internalScalar, mul_add, add_mul,
    mul_smul_comm, smul_mul_assoc, mul_one, grading_sq, hJ,
    smul_neg, Real.cos_neg, Real.sin_neg, neg_smul]

end NeutralFrame

end InfoGeometry.Quantum.Realification
