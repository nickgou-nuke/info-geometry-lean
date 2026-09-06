/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.ApolloniusTauDifferential
import InfoGeometry.ParaKahler.ApolloniusCylinder

noncomputable section

open scoped InnerProductSpace

namespace InfoGeometry.Arithmetic.CompletedXiHestenesHomogeneousCoordinates

open Complex
open InfoGeometry.ParaKahler.ApolloniusCylinder

private theorem inner_scaled_coordinates
    (a b c d : ℝ) (z : ℂ) :
    ⟪((a : ℂ) + I * (b : ℂ)) * z,
      ((c : ℂ) + I * (d : ℂ)) * z⟫_ℝ =
      Complex.normSq z * (a * c + b * d) := by
  simp [Complex.inner, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

private theorem inner_scaled_I_coordinates
    (a b c d : ℝ) (z : ℂ) :
    ⟪((a : ℂ) + I * (b : ℂ)) * z,
      I * (((c : ℂ) + I * (d : ℂ)) * z)⟫_ℝ =
      Complex.normSq z * (b * c - a * d) := by
  simp [Complex.inner, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem paraComplexStructure_mulVec_apply (v : Fin 2 → ℝ) :
    Matrix.mulVec paraComplexStructure v = ![v 0, -v 1] := by
  funext i
  fin_cases i <;>
    simp [paraComplexStructure, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem evalMetric_eq_coordinates (v w : Fin 2 → ℝ) :
    evalMetric v w = v 0 * w 0 - v 1 * w 1 := by
  simp [evalMetric, paraMetric, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem evalSymplectic_eq_coordinates (v w : Fin 2 → ℝ) :
    evalSymplectic v w = v 1 * w 0 - v 0 * w 1 := by
  simp [evalSymplectic, symplecticForm, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  ring

theorem apolloniusTauFDeriv_paraMetric_pullback
    (u v w : ApolloniusParameterSpace) :
    ⟪apolloniusTauFDeriv u v,
      apolloniusTauFDeriv u (Matrix.mulVec paraComplexStructure w)⟫_ℝ =
      Complex.normSq (apolloniusTauOfParameter u) * evalMetric v w := by
  rw [apolloniusTauFDeriv_apply, apolloniusTauFDeriv_apply,
    paraComplexStructure_mulVec_apply, evalMetric_eq_coordinates]
  simpa using inner_scaled_coordinates (v 0) (v 1) (w 0) (-w 1)
    (apolloniusTauOfParameter u)

theorem apolloniusTauFDeriv_symplectic_pullback
    (u v w : ApolloniusParameterSpace) :
    ⟪apolloniusTauFDeriv u v,
      I * apolloniusTauFDeriv u w⟫_ℝ =
      Complex.normSq (apolloniusTauOfParameter u) * evalSymplectic v w := by
  rw [apolloniusTauFDeriv_apply, apolloniusTauFDeriv_apply,
    evalSymplectic_eq_coordinates]
  exact inner_scaled_I_coordinates (v 0) (v 1) (w 0) (w 1)
    (apolloniusTauOfParameter u)

theorem apolloniusTauFDeriv_radial_angular_orthogonal
    (u : ApolloniusParameterSpace) :
    ⟪apolloniusTauFDeriv u entropyGradientVector,
      apolloniusTauFDeriv u
        (Matrix.mulVec paraComplexStructure phaseFlowVector)⟫_ℝ = 0 := by
  rw [apolloniusTauFDeriv_paraMetric_pullback,
    metric_flow_orthogonality, mul_zero]

theorem apolloniusTauFDeriv_phase_radial_symplectic
    (u : ApolloniusParameterSpace) :
    ⟪apolloniusTauFDeriv u phaseFlowVector,
      I * apolloniusTauFDeriv u entropyGradientVector⟫_ℝ =
      Complex.normSq (apolloniusTauOfParameter u) := by
  rw [apolloniusTauFDeriv_symplectic_pullback,
    symplectic_flow_pairing.2, mul_one]

end InfoGeometry.Arithmetic.CompletedXiHestenesHomogeneousCoordinates
