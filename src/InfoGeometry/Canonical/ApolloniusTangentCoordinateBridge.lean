/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Canonical.ApolloniusTauDifferential
import InfoGeometry.ParaKahler.ApolloniusCylinder

/-! Tangent-coordinate bridge for the native Apollonius homogeneous carrier. -/

noncomputable section

namespace InfoGeometry.Arithmetic.CompletedXiHestenesHomogeneousCoordinates

open Complex Real
open InfoGeometry.Projective.ApolloniusNatural
open InfoGeometry.ParaKahler.ApolloniusCylinder

@[simp] theorem apolloniusParameter_zero (ξ θ : ℝ) :
    apolloniusParameter ξ θ 0 = ξ := rfl

@[simp] theorem apolloniusParameter_one (ξ θ : ℝ) :
    apolloniusParameter ξ θ 1 = θ := rfl

def apolloniusRayOfParameter (u : Fin 2 → ℝ) : HomogeneousCoord :=
  apolloniusRay (u 0) (u 1)

@[simp] theorem apolloniusRayOfParameter_mk (ξ θ : ℝ) :
    apolloniusRayOfParameter (apolloniusParameter ξ θ) =
      apolloniusRay ξ θ := rfl

theorem apolloniusParameter_add_entropyGradientVector
    (ξ θ t : ℝ) :
    apolloniusParameter ξ θ + t • entropyGradientVector =
      apolloniusParameter (ξ + t) θ := by
  funext i
  fin_cases i <;> simp [apolloniusParameter, entropyGradientVector]

theorem apolloniusParameter_add_phaseFlowVector
    (ξ θ φ : ℝ) :
    apolloniusParameter ξ θ + φ • phaseFlowVector =
      apolloniusParameter ξ (θ + φ) := by
  funext i
  fin_cases i <;> simp [apolloniusParameter, phaseFlowVector]

theorem apolloniusRay_entropyGradient_path (ξ θ t : ℝ) :
    apolloniusRayOfParameter
        (apolloniusParameter ξ θ + t • entropyGradientVector) =
      apolloniusRay (ξ + t) θ := by
  rw [apolloniusParameter_add_entropyGradientVector]
  rfl

theorem apolloniusRay_phaseFlow_path (ξ θ φ : ℝ) :
    apolloniusRayOfParameter
        (apolloniusParameter ξ θ + φ • phaseFlowVector) =
      apolloniusRay ξ (θ + φ) := by
  rw [apolloniusParameter_add_phaseFlowVector]
  rfl

end InfoGeometry.Arithmetic.CompletedXiHestenesHomogeneousCoordinates
