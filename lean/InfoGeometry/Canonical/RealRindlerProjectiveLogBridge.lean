import InfoGeometry.Dynamics.RindlerWedge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RindlerWeylDecomposition
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Real Rindler projective-log bridge

This owner keeps the positive real projective ratio separate from the complex
Möbius/de Rham comparison lane.  It proves only the native real boost,
logarithmic, and inversion identities.
-/

namespace InfoGeometry.Canonical.RealRindlerProjectiveLogBridge

noncomputable section

open InfoGeometry.Dynamics.HyperbolicComponent
open InfoGeometry.Dynamics.RapiditySpace
open InfoGeometry.Dynamics.RindlerWedge
open InfoGeometry.Canonical.RindlerWeylDecomposition

def projectiveNullRatio (x : LightConeColumn) : ℝ :=
  x (0 : Fin 2) (0 : Fin 1) / x (1 : Fin 2) (0 : Fin 1)

def rindlerProjectiveNullRatio (c : RindlerCoordinates) : ℝ :=
  projectiveNullRatio (rindlerToMinkowski c)

theorem rindlerProjectiveNullRatio_eq_exp (c : RindlerCoordinates) :
    rindlerProjectiveNullRatio c = Real.exp (2 * c.time) := by
  simp [rindlerProjectiveNullRatio, projectiveNullRatio, rindlerToMinkowski]
  field_simp [ne_of_gt c.radius_pos, ne_of_gt (Real.exp_pos (-c.time))]
  rw [← Real.exp_add]
  congr 1
  ring

theorem rindlerProjectiveNullRatio_pos (c : RindlerCoordinates) :
    0 < rindlerProjectiveNullRatio c := by
  rw [rindlerProjectiveNullRatio_eq_exp]
  positivity

theorem rindlerProjectiveNullRatio_ne_zero (c : RindlerCoordinates) :
    rindlerProjectiveNullRatio c ≠ 0 :=
  ne_of_gt (rindlerProjectiveNullRatio_pos c)

theorem projectiveNullRatio_rindler_boost
    (c : RindlerCoordinates) (lam : ℝ) :
    projectiveNullRatio (componentAReal lam * rindlerToMinkowski c) =
      Real.exp (2 * lam) * rindlerProjectiveNullRatio c := by
  rw [rindler_flow_is_time_translation]
  change rindlerProjectiveNullRatio
      ⟨c.radius, c.time + lam, c.radius_pos⟩ = _
  rw [rindlerProjectiveNullRatio_eq_exp, rindlerProjectiveNullRatio_eq_exp]
  rw [← Real.exp_add]
  congr 1
  ring

theorem log_rindlerProjectiveNullRatio_boost
    (c : RindlerCoordinates) (lam : ℝ) :
    Real.log
        (projectiveNullRatio (componentAReal lam * rindlerToMinkowski c)) =
      Real.log (rindlerProjectiveNullRatio c) + 2 * lam := by
  rw [projectiveNullRatio_rindler_boost]
  rw [Real.log_mul (by positivity)
    (rindlerProjectiveNullRatio_ne_zero c)]
  rw [Real.log_exp]
  ring

def realProjectiveDilation (lam q : ℝ) : ℝ :=
  Real.exp (2 * lam) * q

theorem realProjectiveDilation_rindler
    (c : RindlerCoordinates) (lam : ℝ) :
    realProjectiveDilation lam (rindlerProjectiveNullRatio c) =
      projectiveNullRatio (componentAReal lam * rindlerToMinkowski c) := by
  exact (projectiveNullRatio_rindler_boost c lam).symm

def realProjectiveInversion (q : ℝ) : ℝ := q⁻¹

theorem inversion_conjugates_dilation
    (lam q : ℝ) :
    realProjectiveInversion (realProjectiveDilation lam q) =
      realProjectiveDilation (-lam) (realProjectiveInversion q) := by
  simp [realProjectiveInversion, realProjectiveDilation]
  rw [Real.exp_neg]
  ring

theorem rindler_xi_eq_log_radius (c : RindlerCoordinates) :
    xi
        (rindlerToMinkowski c 0 0)
        (rindlerToMinkowski c 1 0) = Real.log c.radius := by
  simp [xi, rindlerToMinkowski]
  rw [Real.log_mul (ne_of_gt c.radius_pos) (ne_of_gt (Real.exp_pos c.time)),
    Real.log_mul (ne_of_gt c.radius_pos) (ne_of_gt (Real.exp_pos (-c.time))),
    Real.log_exp, Real.log_exp]
  ring

theorem rindler_eta_eq_time (c : RindlerCoordinates) :
    eta
        (rindlerToMinkowski c 0 0)
        (rindlerToMinkowski c 1 0) = c.time := by
  simp [eta, rindlerToMinkowski]
  rw [Real.log_mul (ne_of_gt c.radius_pos) (ne_of_gt (Real.exp_pos c.time)),
    Real.log_mul (ne_of_gt c.radius_pos) (ne_of_gt (Real.exp_pos (-c.time))),
    Real.log_exp, Real.log_exp]
  ring

end
end InfoGeometry.Canonical.RealRindlerProjectiveLogBridge
