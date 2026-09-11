/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic
import InfoGeometry.Canonical.ApolloniusHomogeneousCoordinatesBridge
import InfoGeometry.ParaKahler.ApolloniusCylinder

noncomputable section

namespace InfoGeometry.Arithmetic.CompletedXiHestenesHomogeneousCoordinates

open Complex Real
open InfoGeometry.Projective.ApolloniusNatural
open InfoGeometry.ParaKahler.ApolloniusCylinder

abbrev ApolloniusParameterSpace : Type := Fin 2 → ℝ

def radialCoordinateCLM : ApolloniusParameterSpace →L[ℝ] ℝ :=
  ContinuousLinearMap.proj 0

def angularCoordinateCLM : ApolloniusParameterSpace →L[ℝ] ℝ :=
  ContinuousLinearMap.proj 1

def apolloniusComplexCoordinateCLM : ApolloniusParameterSpace →L[ℝ] ℂ :=
  (Complex.ofRealCLM.comp radialCoordinateCLM) +
    (Complex.ofRealCLM.comp angularCoordinateCLM).smulRight Complex.I

@[simp] theorem apolloniusComplexCoordinateCLM_apply
    (v : ApolloniusParameterSpace) :
    apolloniusComplexCoordinateCLM v =
      (v 0 : ℂ) + Complex.I * (v 1 : ℂ) := by
  simp [apolloniusComplexCoordinateCLM, radialCoordinateCLM,
    angularCoordinateCLM]
  ring

def apolloniusTauOfParameter (u : ApolloniusParameterSpace) : ℂ :=
  Complex.exp (apolloniusComplexCoordinateCLM u)

@[simp] theorem apolloniusTauOfParameter_apply
    (u : ApolloniusParameterSpace) :
    apolloniusTauOfParameter u =
      Complex.exp ((u 0 : ℂ) + Complex.I * (u 1 : ℂ)) := by
  simp [apolloniusTauOfParameter, apolloniusComplexCoordinateCLM_apply]

def apolloniusTauFDeriv (u : ApolloniusParameterSpace) :
    ApolloniusParameterSpace →L[ℝ] ℂ :=
  (ContinuousLinearMap.restrictScalars ℝ
      (ContinuousLinearMap.toSpanSingleton ℂ
        (Complex.exp (apolloniusComplexCoordinateCLM u)))).comp
    apolloniusComplexCoordinateCLM

@[simp] theorem apolloniusTauFDeriv_apply
    (u v : ApolloniusParameterSpace) :
    apolloniusTauFDeriv u v =
      ((v 0 : ℂ) + Complex.I * (v 1 : ℂ)) *
        apolloniusTauOfParameter u := by
  simp [apolloniusTauFDeriv, apolloniusComplexCoordinateCLM_apply]

theorem hasFDerivAt_apolloniusTauOfParameter
    (u : ApolloniusParameterSpace) :
    HasFDerivAt apolloniusTauOfParameter
      (apolloniusTauFDeriv u) u := by
  have harg : HasFDerivAt apolloniusComplexCoordinateCLM
      apolloniusComplexCoordinateCLM u :=
    apolloniusComplexCoordinateCLM.hasFDerivAt
  have hexp : HasFDerivAt Complex.exp
      (ContinuousLinearMap.restrictScalars ℝ
        (ContinuousLinearMap.toSpanSingleton ℂ
          (Complex.exp (apolloniusComplexCoordinateCLM u))))
        (apolloniusComplexCoordinateCLM u) := by
    have hcomplex :=
      (Complex.hasDerivAt_exp (apolloniusComplexCoordinateCLM u)).hasFDerivAt
    simpa using hcomplex.restrictScalars ℝ
  have h := hexp.comp u harg
  convert h using 1

theorem apolloniusTauFDeriv_entropyGradientVector
    (u : ApolloniusParameterSpace) :
    apolloniusTauFDeriv u entropyGradientVector =
      apolloniusTauOfParameter u := by
  simp [apolloniusTauFDeriv_apply, entropyGradientVector]

theorem apolloniusTauFDeriv_phaseFlowVector
    (u : ApolloniusParameterSpace) :
    apolloniusTauFDeriv u phaseFlowVector =
      Complex.I * apolloniusTauOfParameter u := by
  simp [apolloniusTauFDeriv_apply, phaseFlowVector]

def apolloniusParameter (ξ θ : ℝ) : ApolloniusParameterSpace := ![ξ, θ]

@[simp] theorem apolloniusTauOfParameter_mk (ξ θ : ℝ) :
    apolloniusTauOfParameter (apolloniusParameter ξ θ) =
      Complex.exp ((ξ : ℂ) + Complex.I * (θ : ℂ)) := by
  simp [apolloniusParameter, apolloniusTauOfParameter_apply]

theorem apolloniusTauFDeriv_entropyGradientVector_mk (ξ θ : ℝ) :
    apolloniusTauFDeriv (apolloniusParameter ξ θ) entropyGradientVector =
      Complex.exp ((ξ : ℂ) + Complex.I * (θ : ℂ)) := by
  rw [apolloniusTauFDeriv_entropyGradientVector]
  exact apolloniusTauOfParameter_mk ξ θ

theorem apolloniusTauFDeriv_phaseFlowVector_mk (ξ θ : ℝ) :
    apolloniusTauFDeriv (apolloniusParameter ξ θ) phaseFlowVector =
      Complex.I * Complex.exp ((ξ : ℂ) + Complex.I * (θ : ℂ)) := by
  rw [apolloniusTauFDeriv_phaseFlowVector]
  rw [apolloniusTauOfParameter_mk]

theorem tangent_eq_radial_add_angular (v : ApolloniusParameterSpace) :
    v = (v 0) • entropyGradientVector + (v 1) • phaseFlowVector := by
  funext i
  fin_cases i <;> simp [entropyGradientVector, phaseFlowVector]

theorem apolloniusTauFDeriv_basis_decomposition
    (u v : ApolloniusParameterSpace) :
    apolloniusTauFDeriv u v =
      (v 0 : ℂ) * apolloniusTauOfParameter u +
        (v 1 : ℂ) * (Complex.I * apolloniusTauOfParameter u) := by
  rw [apolloniusTauFDeriv_apply]
  ring

end InfoGeometry.Arithmetic.CompletedXiHestenesHomogeneousCoordinates
