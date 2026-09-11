/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.RiemannXiHomogeneousProjectionBridge
import InfoGeometry.Projective.ApolloniusNatural

noncomputable section

namespace InfoGeometry.Arithmetic.CompletedXiHestenesHomogeneousCoordinates

open Complex Real
open InfoGeometry.Projective.ApolloniusNatural
open InfoGeometry.Arithmetic.RiemannXiHomogeneousProjectionBridge
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

theorem apolloniusRay_second_ne_zero (ξ θ : ℝ) :
    (apolloniusRay ξ θ).2 ≠ 0 := by
  simp [apolloniusRay]

theorem normSq_projectiveRatio_apolloniusRay (ξ θ : ℝ) :
    Complex.normSq (projectiveRatio (apolloniusRay ξ θ)) =
      Real.exp (2 * ξ) := by
  simpa [projectiveRatio, apolloniusRay] using
    apollonius_ray_z0_normSq ξ θ

theorem projectiveRatio_apolloniusRay_unitCircle_iff_xi_zero
    (ξ θ : ℝ) :
    OnLeeYangCircle (projectiveRatio (apolloniusRay ξ θ)) ↔ ξ = 0 := by
  unfold OnLeeYangCircle
  rw [normSq_projectiveRatio_apolloniusRay]
  constructor
  · intro h
    have h' : Real.exp (2 * ξ) = Real.exp 0 := by
      simpa using h
    have : 2 * ξ = 0 := Real.exp_injective h'
    linarith
  · intro h
    subst ξ
    norm_num

theorem projectiveS_apolloniusRay_criticalLine_iff_xi_zero
    (ξ θ : ℝ)
    (hsum :
      (apolloniusRay ξ θ).1 + (apolloniusRay ξ θ).2 ≠ 0) :
    OnCriticalLine (projectiveS (apolloniusRay ξ θ)) ↔ ξ = 0 := by
  rw [projectiveS_criticalLine_iff_projectiveRatio_unitCircle
    (apolloniusRay ξ θ) (apolloniusRay_second_ne_zero ξ θ) hsum]
  exact projectiveRatio_apolloniusRay_unitCircle_iff_xi_zero ξ θ

theorem xi_zero_iff_projectiveS_apolloniusRay_criticalLine
    (ξ θ : ℝ)
    (hsum :
      (apolloniusRay ξ θ).1 + (apolloniusRay ξ θ).2 ≠ 0) :
    ξ = 0 ↔ OnCriticalLine (projectiveS (apolloniusRay ξ θ)) := by
  exact (projectiveS_apolloniusRay_criticalLine_iff_xi_zero ξ θ hsum).symm

theorem xi_zero_implies_projectiveS_criticalLine
    (θ : ℝ)
    (hsum :
      (apolloniusRay 0 θ).1 + (apolloniusRay 0 θ).2 ≠ 0) :
    OnCriticalLine (projectiveS (apolloniusRay 0 θ)) :=
  (xi_zero_iff_projectiveS_apolloniusRay_criticalLine 0 θ hsum).mp rfl

theorem projectiveS_criticalLine_implies_xi_zero
    (ξ θ : ℝ)
    (hsum :
      (apolloniusRay ξ θ).1 + (apolloniusRay ξ θ).2 ≠ 0)
    (hcrit : OnCriticalLine (projectiveS (apolloniusRay ξ θ))) :
    ξ = 0 :=
  (xi_zero_iff_projectiveS_apolloniusRay_criticalLine ξ θ hsum).mpr hcrit

end InfoGeometry.Arithmetic.CompletedXiHestenesHomogeneousCoordinates
