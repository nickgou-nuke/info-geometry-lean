/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Canonical.MatrixTracedChernWeilBridge
import InfoGeometry.Canonical.ExteriorEvenTraceChernWeil

/-!
# Chern–Simons transgression kernel

Single canonical proof of the Chern–Simons transgression identity for a
matrix-valued one-form connection over an exterior-form carrier.  The kernel
is stated in unfolded form — the density is the explicit trace expression
`Tr(A * dA + (2/3) • A³)` and the curvature square is the explicit product
`(dA + A²) * (dA + A²)` — so that both

* `ChernSimonsTransgressionInstantonBridge` (which owns the
  `chernSimonsDensityForm` / `curvatureFromConnection` definitions), and
* `ChernSimonsCorrectCoefficientTransgressionBridge`

delegate to this one proof instead of maintaining two bodies.

The degree hypotheses are explicit because the graded-derivation interface
alone does not assert that `d` raises degree, and characteristic-zero plus
torsion-freeness are required for the degree-four trace-vanishing step.
-/

noncomputable section

namespace InfoGeometry.Canonical.ChernSimonsTransgressionKernel

open ExteriorAlgebra
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
open InfoGeometry.Canonical.ExteriorEvenTraceChernWeil
open InfoGeometry.Canonical.ExteriorGradedDerivationBridge
open BigOperators

variable {R V : Type*} [Field R] [AddCommGroup V] [Module R V] {n : ℕ}

/-- The full Chern–Simons transgression: `d Tr(A dA + (2/3) A³) = Tr(F²)` for
`F = dA + A²`, stated in unfolded form. -/
theorem transgression_kernel
    [CharZero R] [Module.IsTorsionFree R (ExteriorAlgebra R V)]
    (d : Module.End R (ExteriorAlgebra R V))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (h_d_sq : d.comp d = 0)
    (h_graded : InfoGeometry.Canonical.ExteriorGradedDerivationBridge.IsGradedDerivation d)
    (hA : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 1 A)
    (h_dA : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 2
      (matrixExteriorDerivative d A)) :
    d (matrixTraceForm (A * matrixExteriorDerivative d A + (2 / 3 : R) • (A * A * A))) =
      matrixTraceForm ((matrixExteriorDerivative d A + A * A) *
        (matrixExteriorDerivative d A + A * A)) := by
  have D : InfoGeometry.Canonical.ExteriorGradedDerivationBridge.ExteriorDifferentialData R V :=
    ⟨d, h_graded, h_d_sq⟩
  have h_d_ad : d (matrixTraceForm (A * matrixExteriorDerivative d A)) =
      matrixTraceForm (matrixExteriorDerivative d A * matrixExteriorDerivative d A) := by
    rw [exteriorDerivative_matrixTraceForm]
    rw [matrixExteriorDerivative_one_form_mul_derivative d h_d_sq h_graded A hA]
  have hA2 : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 2
      (A * A) := matrix_one_form_square_homogeneous A hA
  have h_dA_A : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 3
      (matrixExteriorDerivative d A * A) := by
    have h := matrix_mul_homogeneous (matrixExteriorDerivative d A) A h_dA hA
    simpa using h
  have hcycle := matrix_trace_one_three_anticommute A
    (matrixExteriorDerivative d A * A) hA h_dA_A
  have h_even := matrix_trace_even_cyclic (matrixExteriorDerivative d A) (A * A) hA2
  have hcycle' : matrixTraceForm (A * matrixExteriorDerivative d A * A) =
      -matrixTraceForm (matrixExteriorDerivative d A * A * A) := by
    simpa [mul_assoc] using hcycle
  have h_even' : matrixTraceForm (A * A * matrixExteriorDerivative d A) =
      matrixTraceForm (matrixExteriorDerivative d A * A * A) := by
    simpa [mul_assoc] using h_even.symm
  have h_d_a3 : d (matrixTraceForm (A * A * A)) =
      (3 : R) • matrixTraceForm (matrixExteriorDerivative d A * A * A) := by
    rw [exteriorDerivative_matrixTraceForm,
      matrixExteriorDerivative_one_form_cube_of_graded d h_graded A hA]
    simp only [map_add, map_sub]
    rw [hcycle', h_even']
    simp only [sub_eq_add_neg, neg_neg, add_assoc]
    rw [ofNat_smul_eq_nsmul R 3, three_nsmul]
  have h_d_ad' : matrixTraceForm
      (matrixExteriorDerivative d (A * matrixExteriorDerivative d A)) =
      matrixTraceForm (matrixExteriorDerivative d A * matrixExteriorDerivative d A) := by
    rw [← exteriorDerivative_matrixTraceForm]
    exact h_d_ad
  have h_d_a3' : matrixTraceForm (matrixExteriorDerivative d (A * A * A)) =
      (3 : R) • matrixTraceForm (matrixExteriorDerivative d A * A * A) := by
    rw [← exteriorDerivative_matrixTraceForm]
    exact h_d_a3
  have h_d_cs : d (matrixTraceForm
      (A * matrixExteriorDerivative d A + (2 / 3 : R) • (A * A * A))) =
      matrixTraceForm (matrixExteriorDerivative d A * matrixExteriorDerivative d A) +
        2 • matrixTraceForm (matrixExteriorDerivative d A * A * A) := by
    rw [exteriorDerivative_matrixTraceForm]
    have hlin : matrixExteriorDerivative d
        (A * matrixExteriorDerivative d A + (2 / 3 : R) • (A * A * A)) =
        matrixExteriorDerivative d (A * matrixExteriorDerivative d A) +
          (2 / 3 : R) • matrixExteriorDerivative d (A * A * A) := by
      ext i j
      simp [matrixExteriorDerivative]
    rw [hlin, map_add, map_smul, h_d_ad', h_d_a3']
    have hcoeff : (2 / 3 : R) * 3 = 2 := by
      field_simp
    rw [smul_smul, hcoeff, ofNat_smul_eq_nsmul R 2]
  have h_tr_f2 : matrixTraceForm ((matrixExteriorDerivative d A + A * A) *
      (matrixExteriorDerivative d A + A * A)) =
      matrixTraceForm (matrixExteriorDerivative d A * matrixExteriorDerivative d A) +
        2 • matrixTraceForm (matrixExteriorDerivative d A * A * A) := by
    rw [matrixTrace_curvature_square_expansion]
    rw [h_even'.symm, matrix_trace_fourth_power_one_form_eq_zero A hA]
    simp [two_smul, add_assoc]
  rw [h_d_cs, h_tr_f2]

end InfoGeometry.Canonical.ChernSimonsTransgressionKernel
