/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Analysis.LogDetSelfConcordantBarrier
import InfoGeometry.ExponentialFamily.Class
import InfoGeometry.Canonical.ApolloniusTauDifferential

noncomputable section

namespace InfoGeometry.Canonical.NegativeLogReadoutBridge

open Complex Real
open InfoGeometry.Arithmetic.CompletedXiHestenesHomogeneousCoordinates
open InfoGeometry.Projective.ApolloniusNatural
open InfoGeometry.Analysis.SelfConcordant
open InfoGeometry.ExponentialFamily.Class

private theorem normSq_projectiveRatio_apolloniusRay (ξ θ : ℝ) :
    Complex.normSq (projectiveRatio (apolloniusRay ξ θ)) =
      Real.exp (2 * ξ) := by
  simpa [projectiveRatio, apolloniusRay] using
    apollonius_ray_z0_normSq ξ θ

def negativeLogGenerator (x : ℝ) : ℝ := -Real.log x

def apolloniusRadialNegativeLog (ξ θ : ℝ) : ℝ :=
  negativeLogGenerator
    (Complex.normSq (projectiveRatio (apolloniusRay ξ θ)))

theorem apolloniusRadialNegativeLog_eq (ξ θ : ℝ) :
    apolloniusRadialNegativeLog ξ θ = -2 * ξ := by
  unfold apolloniusRadialNegativeLog negativeLogGenerator
  rw [normSq_projectiveRatio_apolloniusRay, Real.log_exp]
  ring

theorem apolloniusRadialNegativeLog_eq_zero_iff (ξ θ : ℝ) :
    apolloniusRadialNegativeLog ξ θ = 0 ↔ ξ = 0 := by
  rw [apolloniusRadialNegativeLog_eq]
  constructor <;> intro h <;> linarith

def exponentialFamilySurprisal
    {α η : Type*} [ExponentialFamily α η]
    (p : η) (a : α) : ℝ :=
  negativeLogGenerator (ExponentialFamily.density p a)

theorem exponentialFamilySurprisal_eq
    {α η : Type*} [ExponentialFamily α η]
    (p : η) (a : α) :
    exponentialFamilySurprisal p a =
      @ExponentialFamily.logPartition α η _ p -
        @ExponentialFamily.statistic α η _ a p := by
  unfold exponentialFamilySurprisal negativeLogGenerator
  rw [ExponentialFamily.density_eq, Real.log_exp]
  ring

theorem density_eq_exp_neg_surprisal
    {α η : Type*} [ExponentialFamily α η]
    (p : η) (a : α) :
    @ExponentialFamily.density α η _ p a =
      Real.exp (-exponentialFamilySurprisal p a) := by
  rw [exponentialFamilySurprisal_eq, ExponentialFamily.density_eq]
  congr 1
  ring

theorem exponentialFamilySurprisal_eq_apollonius
    {α η : Type*} [ExponentialFamily α η]
    (p : η) (a : α) (ξ θ : ℝ)
    (h :
      ExponentialFamily.density p a =
        Complex.normSq (projectiveRatio (apolloniusRay ξ θ))) :
    exponentialFamilySurprisal p a =
      apolloniusRadialNegativeLog ξ θ := by
  simp [exponentialFamilySurprisal, apolloniusRadialNegativeLog, h]

theorem exponentialFamilySurprisal_eq_neg_two_xi
    {α η : Type*} [ExponentialFamily α η]
    (p : η) (a : α) (ξ θ : ℝ)
    (h :
      ExponentialFamily.density p a =
        Complex.normSq (projectiveRatio (apolloniusRay ξ θ))) :
    exponentialFamilySurprisal p a = -2 * ξ := by
  rw [exponentialFamilySurprisal_eq_apollonius p a ξ θ h,
    apolloniusRadialNegativeLog_eq]

theorem logDetBarrier_eq_apollonius
    {n : ℕ} (A : PosDefCone n) (ξ θ : ℝ)
    (hdet :
      A.mat.det =
        Complex.normSq (projectiveRatio (apolloniusRay ξ θ))) :
    phi A = apolloniusRadialNegativeLog ξ θ := by
  unfold phi apolloniusRadialNegativeLog negativeLogGenerator
  rw [hdet]

theorem logDetBarrier_eq_neg_two_xi
    {n : ℕ} (A : PosDefCone n) (ξ θ : ℝ)
    (hdet :
      A.mat.det =
        Complex.normSq (projectiveRatio (apolloniusRay ξ θ))) :
    phi A = -2 * ξ := by
  rw [logDetBarrier_eq_apollonius A ξ θ hdet,
    apolloniusRadialNegativeLog_eq]

end InfoGeometry.Canonical.NegativeLogReadoutBridge
