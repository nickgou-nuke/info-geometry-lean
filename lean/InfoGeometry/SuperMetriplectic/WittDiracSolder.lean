/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.NeutralKreinDiracSolder
import InfoGeometry.SuperMetriplectic.MajoranaSouriauMetriplecticLoxodromic

/-! The existing Witt operators exchange with a minus sign under the neutral
metric adjoint. This is a statement about the full doubled matrix carrier and
arbitrary spinors. No new carrier or adjoint is introduced.
-/

noncomputable section

namespace InfoGeometry.SuperMetriplectic.MajoranaSouriauMetriplecticLoxodromic

open Matrix InfoGeometry.Quantum.NeutralKreinMajoranaFrame
open InfoGeometry.CliffordWeyl.SpinorBilinearSoldering

theorem wittAnnihilator_eq_half_sum (n : ℕ) :
    wittAnnihilator n = (1 / 2 : ℝ) • (grading n + majoranaForm n) := by
  change ((1 / 2 : ℝ) • (1 : Matrix2 n)) * (grading n + majoranaForm n) = _
  rw [smul_mul_assoc, one_mul]

theorem wittCreator_eq_half_sub (n : ℕ) :
    wittCreator n = (1 / 2 : ℝ) • (grading n - majoranaForm n) := by
  change ((1 / 2 : ℝ) • (1 : Matrix2 n)) * (grading n - majoranaForm n) = _
  rw [smul_mul_assoc, one_mul]

theorem wittAnnihilator_metric_adjoint (n : ℕ) :
    kreinMetric n * (wittAnnihilator n).conjTranspose * kreinMetric n =
      -wittCreator n := by
  rw [wittAnnihilator_eq_half_sum, wittCreator_eq_half_sub]
  simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_add,
    mul_smul_comm, smul_mul_assoc, mul_add, add_mul]
  rw [grading_metric_adjoint, majoranaForm_metric_adjoint]
  simp only [smul_add, smul_sub, smul_neg]
  abel

theorem wittCreator_metric_adjoint (n : ℕ) :
    kreinMetric n * (wittCreator n).conjTranspose * kreinMetric n =
      -wittAnnihilator n := by
  rw [wittCreator_eq_half_sub, wittAnnihilator_eq_half_sum]
  simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_sub,
    mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul]
  rw [grading_metric_adjoint, majoranaForm_metric_adjoint]
  simp only [smul_add, smul_sub, smul_neg]
  abel

theorem solder_wittAnnihilator_right (n : ℕ) (l r : Carrier n → ℝ) :
    solder (kreinMetric n) l (wittAnnihilator n *ᵥ r) =
      -(solder (kreinMetric n) l r * wittCreator n) := by
  rw [solder_right_operator_action _ _ _ (kreinMetric_sq n),
    wittAnnihilator_metric_adjoint, mul_neg]

theorem solder_wittCreator_right (n : ℕ) (l r : Carrier n → ℝ) :
    solder (kreinMetric n) l (wittCreator n *ᵥ r) =
      -(solder (kreinMetric n) l r * wittAnnihilator n) := by
  rw [solder_right_operator_action _ _ _ (kreinMetric_sq n),
    wittCreator_metric_adjoint, mul_neg]

end InfoGeometry.SuperMetriplectic.MajoranaSouriauMetriplecticLoxodromic
