/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.NeutralKreinMajoranaFrame
import InfoGeometry.CliffordWeyl.DiracSolderOperatorAction

/-! Dirac ket–bras for the existing neutral Krein–Majorana frame.
The skew Majorana form is self-adjoint for the neutral metric, whereas the
grading is skew-adjoint for that metric. These statements concern arbitrary
spinors in the full doubled carrier, not just individual coordinate vectors.
-/
namespace InfoGeometry.Quantum.NeutralKreinMajoranaFrame
open Matrix InfoGeometry.CliffordWeyl.SpinorBilinearSoldering

theorem kreinMetric_sq (n : ℕ) : kreinMetric n * kreinMetric n = 1 :=
  exchange_sq n

theorem majoranaForm_metric_adjoint (n : ℕ) :
    kreinMetric n * (majoranaForm n).conjTranspose * kreinMetric n =
      majoranaForm n := by
  rw [conjTranspose_eq_transpose_of_trivial, majoranaForm_transpose]
  unfold kreinMetric majoranaForm
  rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.fromBlocks]

theorem grading_metric_adjoint (n : ℕ) :
    kreinMetric n * (grading n).conjTranspose * kreinMetric n =
      -(grading n) := by
  rw [conjTranspose_eq_transpose_of_trivial]
  unfold kreinMetric grading
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.fromBlocks]

theorem solder_majoranaForm_right (n : ℕ) (l r : Carrier n → ℝ) :
    solder (kreinMetric n) l (majoranaForm n *ᵥ r) =
      solder (kreinMetric n) l r * majoranaForm n := by
  rw [solder_right_operator_action _ _ _ (kreinMetric_sq n),
    majoranaForm_metric_adjoint]

theorem solder_grading_right (n : ℕ) (l r : Carrier n → ℝ) :
    solder (kreinMetric n) l (grading n *ᵥ r) =
      -(solder (kreinMetric n) l r * grading n) := by
  rw [solder_right_operator_action _ _ _ (kreinMetric_sq n),
    grading_metric_adjoint, mul_neg]

theorem bilinear_majoranaForm_adjoint (n : ℕ) (l r : Carrier n → ℝ) :
    bilinear (kreinMetric n) 1 (majoranaForm n *ᵥ l) r =
      bilinear (kreinMetric n) (majoranaForm n) l r := by
  rw [bilinear_metric_adjoint_action _ _ _ (kreinMetric_sq n),
    majoranaForm_metric_adjoint]

end InfoGeometry.Quantum.NeutralKreinMajoranaFrame
