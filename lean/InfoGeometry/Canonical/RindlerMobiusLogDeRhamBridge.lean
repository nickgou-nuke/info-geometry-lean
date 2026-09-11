import InfoGeometry.Dynamics.RindlerWedge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.MobiusGeometry
import InfoGeometry.Projective.KleinQuadricMonodromy
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Tactic

/-!
# Rindler projective null ratio

This file records the finite real slice of the Rindler--Möbius--logarithmic
chain.  The two positive light-cone coordinates of a Rindler point determine
a projective ratio.  The existing hyperbolic boost scales that ratio, and its
real logarithm is translated by twice the rapidity.

No complexified path, de Rham period, or winding theorem is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.RindlerMobiusLogDeRhamBridge

open InfoGeometry.Dynamics.HyperbolicComponent
open InfoGeometry.Dynamics.RapiditySpace
open InfoGeometry.Dynamics.RindlerWedge
open InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy

/-- Projective ratio of the two null coordinates. -/
def projectiveNullRatio (x : LightConeColumn) : ℝ :=
  x 0 0 / x 1 0

/-- The projective null ratio of a right-wedge Rindler point. -/
def rindlerProjectiveNullRatio (c : RindlerCoordinates) : ℝ :=
  projectiveNullRatio (rindlerToMinkowski c)

theorem rindlerProjectiveNullRatio_eq_exp (c : RindlerCoordinates) :
    rindlerProjectiveNullRatio c = Real.exp (2 * c.time) := by
  simp [rindlerProjectiveNullRatio, projectiveNullRatio, rindlerToMinkowski]
  field_simp [ne_of_gt c.radius_pos, ne_of_gt (Real.exp_pos (-c.time))]
  rw [← Real.exp_add]
  congr 1
  ring

theorem projectiveNullRatio_rindler_boost
    (c : RindlerCoordinates) (lam : ℝ) :
    projectiveNullRatio (componentAReal lam * rindlerToMinkowski c) =
      Real.exp (2 * lam) * rindlerProjectiveNullRatio c := by
  rw [rindler_flow_is_time_translation]
  change rindlerProjectiveNullRatio
      { radius := c.radius
        time := c.time + lam
        radius_pos := c.radius_pos } = _
  rw [rindlerProjectiveNullRatio_eq_exp, rindlerProjectiveNullRatio_eq_exp]
  rw [← Real.exp_add]
  congr 1
  ring

/-- Complexification of the real projective null ratio. -/
def complexProjectiveNullRatio (c : RindlerCoordinates) : ℂ :=
  (rindlerProjectiveNullRatio c : ℂ)

/-- Complexified projective dilation associated with a rapidity parameter. -/
def complexifiedProjectiveDilation (η z : ℂ) : ℂ :=
  Complex.exp (2 * η) * z

theorem complexProjectiveNullRatio_rindler_boost
    (c : RindlerCoordinates) (lam : ℝ) :
    (projectiveNullRatio (componentAReal lam * rindlerToMinkowski c) : ℂ) =
      (Real.exp (2 * lam) : ℂ) * complexProjectiveNullRatio c := by
  rw [projectiveNullRatio_rindler_boost]
  simp [complexProjectiveNullRatio]

theorem complexifiedProjectiveDilation_real_slice
    (c : RindlerCoordinates) (lam : ℝ) :
    complexifiedProjectiveDilation (lam : ℂ) (complexProjectiveNullRatio c) =
      (projectiveNullRatio
        (componentAReal lam * rindlerToMinkowski c) : ℂ) := by
  rw [complexifiedProjectiveDilation]
  rw [complexProjectiveNullRatio_rindler_boost]
  simp

theorem complexifiedProjectiveDilation_euclidean_period (z : ℂ) :
    complexifiedProjectiveDilation (Real.pi * Complex.I) z = z := by
  rw [complexifiedProjectiveDilation]
  have h : Complex.exp (2 * (Real.pi : ℂ) * Complex.I) = 1 := by
    simp [Complex.exp_two_pi_mul_I]
  have h' : Complex.exp (2 * ((Real.pi : ℂ) * Complex.I)) = 1 := by
    convert h using 1
    ring_nf
  rw [h', one_mul]

theorem euclideanRindlerOrbit_ne_zero
    (R : ℝ) (hR : 0 < R) (θ : ℝ) :
    circleMap 0 R θ ≠ 0 := by
  rw [circleMap_zero]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hR))
    (Complex.exp_ne_zero _)

theorem euclideanRindlerOrbit_periodic (R : ℝ) :
    Function.Periodic (circleMap 0 R) (2 * Real.pi) := by
  intro θ
  rw [circleMap_zero, circleMap_zero]
  rw [Complex.ofReal_add]
  rw [show ((θ : ℂ) + (2 * Real.pi : ℝ)) * Complex.I =
      θ * Complex.I + (2 * (Real.pi : ℂ) * Complex.I) by
        rw [Complex.ofReal_mul]
        simp [mul_add, mul_comm]]
  rw [Complex.exp_add]
  simp [Complex.exp_two_pi_mul_I]

theorem euclideanRindlerOrbit_circleIntegral_one_div
    (R : ℝ) (hR : 0 < R) :
    (∮ z in C((0 : ℂ), R), poleForm z) =
      (2 * Real.pi * Complex.I : ℂ) := by
  exact circleIntegral_one_div R hR

theorem euclideanRindlerOrbit_wilson_phase_of_winding
    (R : ℝ) (hR : 0 < R) (n : ℤ) :
    Complex.exp
        ((n : ℂ) * (∮ z in C((0 : ℂ), R), poleForm z)) =
      (1 : ℂ) := by
  exact wilsonPhase_of_winding R hR n

theorem mobius_dilation_real_rindler_boost
    (c : RindlerCoordinates) (lam : ℝ) :
    MobiusTransform.eval
        (dilation_transform
          (Real.exp (2 * lam) : ℂ)
          (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos (2 * lam)))))
        (some (complexProjectiveNullRatio c)) =
      some
        (projectiveNullRatio
          (componentAReal lam * rindlerToMinkowski c) : ℂ) := by
  rw [dilation_transform_eval_some]
  rw [complexProjectiveNullRatio_rindler_boost]


theorem log_rindlerProjectiveNullRatio_boost
    (c : RindlerCoordinates) (lam : ℝ) :
    Real.log
        (projectiveNullRatio (componentAReal lam * rindlerToMinkowski c)) =
      Real.log (rindlerProjectiveNullRatio c) + 2 * lam := by
  rw [projectiveNullRatio_rindler_boost]
  rw [Real.log_mul (by positivity) (by
    rw [rindlerProjectiveNullRatio_eq_exp]
    positivity)]
  rw [Real.log_exp]
  ring

end InfoGeometry.Canonical.RindlerMobiusLogDeRhamBridge
