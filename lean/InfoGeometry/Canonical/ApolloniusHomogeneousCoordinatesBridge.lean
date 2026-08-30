/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic
import InfoGeometry.Arithmetic.CompletedXiHestenesHomogeneousCoordinates
import InfoGeometry.Projective.ApolloniusNatural

/-! Apollonius natural coordinates on the existing homogeneous carrier. -/

noncomputable section

namespace InfoGeometry.Arithmetic.CompletedXiHestenesHomogeneousCoordinates

open Complex Real
open InfoGeometry.Projective.ApolloniusNatural

def apolloniusHomogeneousCoord (ξ θ : ℝ) : HomogeneousCoord :=
  apolloniusRay ξ θ

@[simp] theorem apolloniusHomogeneousCoord_apply (ξ θ : ℝ) :
    apolloniusHomogeneousCoord ξ θ =
      (Complex.exp ((ξ : ℂ) + Complex.I * (θ : ℂ)), 1) := rfl

@[simp] theorem projectiveRatio_apolloniusHomogeneousCoord
    (ξ θ : ℝ) :
    projectiveRatio (apolloniusHomogeneousCoord ξ θ) =
      Complex.exp ((ξ : ℂ) + Complex.I * (θ : ℂ)) := by
  simp [apolloniusHomogeneousCoord, apolloniusRay, projectiveRatio]

theorem normSq_projectiveRatio_apolloniusHomogeneousCoord
    (ξ θ : ℝ) :
    Complex.normSq (projectiveRatio (apolloniusHomogeneousCoord ξ θ)) =
      Real.exp (2 * ξ) := by
  rw [projectiveRatio_apolloniusHomogeneousCoord]
  exact apollonius_ray_z0_normSq ξ θ

theorem projectiveSignature_apolloniusHomogeneousCoord
    (ξ θ : ℝ) :
    projectiveSignatureQuotient (apolloniusHomogeneousCoord ξ θ) =
      Real.tanh ξ :=
  projective_signature_eq_tanh ξ θ

theorem projectiveRatio_cartanFlow_apolloniusHomogeneousCoord
    (t ξ θ : ℝ) :
    projectiveRatio (cartanFlow t (apolloniusHomogeneousCoord ξ θ)) =
      (Real.exp (2 * t) : ℂ) *
        projectiveRatio (apolloniusHomogeneousCoord ξ θ) := by
  exact projectiveRatio_cartanFlow t
    (by simp [apolloniusHomogeneousCoord, apolloniusRay])

theorem normSq_projectiveRatio_apollonius_angle_shift
    (ξ θ φ : ℝ) :
    Complex.normSq (projectiveRatio (apolloniusHomogeneousCoord ξ (θ + φ))) =
      Complex.normSq (projectiveRatio (apolloniusHomogeneousCoord ξ θ)) := by
  rw [normSq_projectiveRatio_apolloniusHomogeneousCoord,
    normSq_projectiveRatio_apolloniusHomogeneousCoord]

theorem apollonius_unitary_leaf_angle_invariant (θ φ : ℝ) :
    Complex.normSq (projectiveRatio (apolloniusHomogeneousCoord 0 (θ + φ))) = 1 := by
  rw [normSq_projectiveRatio_apolloniusHomogeneousCoord]
  norm_num

def angleFlow (φ : ℝ) (X : HomogeneousCoord) : HomogeneousCoord :=
  (Complex.exp (Complex.I * (φ : ℂ)) * X.1, X.2)

@[simp] theorem angleFlow_zero (X : HomogeneousCoord) :
    angleFlow 0 X = X := by
  rcases X with ⟨p, q⟩
  simp [angleFlow]

theorem angleFlow_add (φ ψ : ℝ) (X : HomogeneousCoord) :
    angleFlow (φ + ψ) X = angleFlow φ (angleFlow ψ X) := by
  rcases X with ⟨p, q⟩
  apply Prod.ext
  · simp only [angleFlow]
    rw [show Complex.I * ((φ + ψ : ℝ) : ℂ) =
        Complex.I * (φ : ℂ) + Complex.I * (ψ : ℂ) by norm_num; ring,
      Complex.exp_add]
    ring
  · rfl

theorem projectiveRatio_angleFlow
    (φ : ℝ) {X : HomogeneousCoord} (hq : X.2 ≠ 0) :
    projectiveRatio (angleFlow φ X) =
      Complex.exp (Complex.I * (φ : ℂ)) * projectiveRatio X := by
  rcases X with ⟨p, q⟩
  unfold angleFlow projectiveRatio
  field_simp [hq]

theorem projectiveRatio_angleFlow_apollonius (φ ξ θ : ℝ) :
    projectiveRatio (angleFlow φ (apolloniusHomogeneousCoord ξ θ)) =
      projectiveRatio (apolloniusHomogeneousCoord ξ (θ + φ)) := by
  rw [projectiveRatio_angleFlow]
  · rw [projectiveRatio_apolloniusHomogeneousCoord,
      projectiveRatio_apolloniusHomogeneousCoord]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  · simp [apolloniusHomogeneousCoord, apolloniusRay]

theorem angleFlow_cartanFlow_commute (t φ : ℝ) (X : HomogeneousCoord) :
    angleFlow φ (cartanFlow t X) = cartanFlow t (angleFlow φ X) := by
  rcases X with ⟨p, q⟩
  apply Prod.ext <;>
    simp [angleFlow, cartanFlow, mul_assoc, mul_comm, mul_left_comm]

theorem normSq_projectiveRatio_angleFlow
    (φ : ℝ) {X : HomogeneousCoord} (hq : X.2 ≠ 0) :
    Complex.normSq (projectiveRatio (angleFlow φ X)) =
      Complex.normSq (projectiveRatio X) := by
  rw [projectiveRatio_angleFlow φ hq]
  simp [Complex.normSq_mul, angularPhase]

@[simp] theorem angleFlow_neg_left (φ : ℝ) (X : HomogeneousCoord) :
    angleFlow (-φ) (angleFlow φ X) = X := by
  rw [← angleFlow_add]
  simp [angleFlow]

theorem angleFlow_neg_right (φ : ℝ) (X : HomogeneousCoord) :
    angleFlow φ (angleFlow (-φ) X) = X := by
  rw [← angleFlow_add]
  simp [angleFlow]

def cylinderFlow (t φ : ℝ) (X : HomogeneousCoord) : HomogeneousCoord :=
  angleFlow φ (cartanFlow t X)

@[simp] theorem cylinderFlow_zero (X : HomogeneousCoord) :
    cylinderFlow 0 0 X = X := by
  rw [cylinderFlow, angleFlow_zero, cartanFlow_zero]

theorem cylinderFlow_eq_cartan_angleFlow
    (t φ : ℝ) (X : HomogeneousCoord) :
    cylinderFlow t φ X = cartanFlow t (angleFlow φ X) := by
  exact angleFlow_cartanFlow_commute t φ X

theorem normSq_projectiveRatio_cylinderFlow_angle_invariant
    (t φ : ℝ) (X : HomogeneousCoord) (hq : X.2 ≠ 0) :
    Complex.normSq (projectiveRatio (cylinderFlow t φ X)) =
      Complex.normSq (projectiveRatio (cartanFlow t X)) := by
  unfold cylinderFlow
  exact normSq_projectiveRatio_angleFlow φ
    (cartanFlow_second_ne_zero t hq)

theorem hasDerivAt_radial_readout
    (X : HomogeneousCoord) :
    HasDerivAt
      (fun t : ℝ => (Real.exp (2 * t) : ℂ) * projectiveRatio X)
      ((2 : ℂ) * projectiveRatio X) 0 := by
  have hlin : HasDerivAt (fun t : ℝ => (2 * t : ℝ)) 2 0 := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) (x := (0 : ℝ))).const_mul 2
  have hexp : HasDerivAt (fun t : ℝ => (Real.exp (2 * t) : ℂ))
      (2 : ℂ) 0 := by
    simpa using (Real.hasDerivAt_exp (2 * 0)).comp 0 hlin |>.ofReal_comp
  exact hexp.mul_const (projectiveRatio X)

theorem hasDerivAt_projectiveRatio_cartanFlow_zero
    (X : HomogeneousCoord) (hq : X.2 ≠ 0) :
    HasDerivAt
      (fun t : ℝ => projectiveRatio (cartanFlow t X))
      ((2 : ℂ) * projectiveRatio X) 0 := by
  have hfinite : ∀ t : ℝ,
      projectiveRatio (cartanFlow t X) =
        (Real.exp (2 * t) : ℂ) * projectiveRatio X := by
    intro t
    exact projectiveRatio_cartanFlow t hq
  exact (hasDerivAt_radial_readout X).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => (hfinite t).symm)

theorem deriv_projectiveRatio_cartanFlow_zero
    (X : HomogeneousCoord) (hq : X.2 ≠ 0) :
    deriv (fun t : ℝ => projectiveRatio (cartanFlow t X)) 0 =
      (2 : ℂ) * projectiveRatio X :=
  (hasDerivAt_projectiveRatio_cartanFlow_zero X hq).deriv

theorem hasDerivAt_projectiveRatio_angleFlow_zero
    (X : HomogeneousCoord) (hq : X.2 ≠ 0) :
    HasDerivAt
      (fun φ : ℝ => projectiveRatio (angleFlow φ X))
      (Complex.I * projectiveRatio X) 0 := by
  have hlin : HasDerivAt
      (fun φ : ℝ => Complex.I * (φ : ℂ)) Complex.I 0 := by
    simpa using
      ((hasDerivAt_id (𝕜 := ℝ) (x := (0 : ℝ))).ofReal_comp.const_mul
        Complex.I)
  have hphase : HasDerivAt
      (fun φ : ℝ => Complex.exp (Complex.I * (φ : ℂ)))
      Complex.I 0 := by
    simpa using (Complex.hasDerivAt_exp 0).comp 0 hlin
  have hfinite : ∀ φ : ℝ,
      projectiveRatio (angleFlow φ X) =
        Complex.exp (Complex.I * (φ : ℂ)) * projectiveRatio X := by
    intro φ
    exact projectiveRatio_angleFlow φ hq
  exact (hphase.mul_const (projectiveRatio X)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun φ => (hfinite φ).symm)

theorem deriv_projectiveRatio_angleFlow_zero
    (X : HomogeneousCoord) (hq : X.2 ≠ 0) :
    deriv (fun φ : ℝ => projectiveRatio (angleFlow φ X)) 0 =
      Complex.I * projectiveRatio X :=
  (hasDerivAt_projectiveRatio_angleFlow_zero X hq).deriv

end InfoGeometry.Arithmetic.CompletedXiHestenesHomogeneousCoordinates
