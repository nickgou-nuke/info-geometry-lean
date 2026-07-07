import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Sandbox restore: punctured-disc Poincaré density

Sandbox-only refactor of the small punctured-disc Poincaré density packet.
This keeps the local owner surface small, splits positivity into reusable helper
lemmas, and records only the finite analytic facts actually used by nearby
puncture geometry.

It does not attempt to replace the larger bilingual/operatorial Poincaré metric
surfaces in `InfoGeometry.Geometry.BilingualPoincareMetric`.
-/

open Complex Metric Topology

namespace Sandbox.Restore.PoincareMetric

/-- The punctured unit disc `D* = {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1}`. -/
def PuncturedDisc : Set ℂ := {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1}

/-- The scalar Poincaré density on the punctured disc. -/
noncomputable def poincareDensity (z : ℂ) : ℝ :=
  1 / (‖z‖ ^ 2 * (Real.log (‖z‖ ^ 2)) ^ 2)

lemma norm_sq_pos {z : ℂ} (hz : z ∈ PuncturedDisc) : 0 < ‖z‖ ^ 2 := by
  nlinarith [hz.1]

lemma norm_sq_lt_one {z : ℂ} (hz : z ∈ PuncturedDisc) : ‖z‖ ^ 2 < 1 := by
  nlinarith [norm_nonneg z, hz.2]

lemma log_norm_sq_ne_zero {z : ℂ} (hz : z ∈ PuncturedDisc) : Real.log (‖z‖ ^ 2) ≠ 0 := by
  intro hlog
  have hsq0 : 0 < ‖z‖ ^ 2 := norm_sq_pos hz
  have hsq : ‖z‖ ^ 2 = 1 := by
    rcases Real.log_eq_zero.mp hlog with hzero | hone | hneg
    · linarith
    · exact hone
    · linarith
  have hlt : ‖z‖ ^ 2 < 1 := norm_sq_lt_one hz
  linarith

lemma log_norm_sq_sq_pos {z : ℂ} (hz : z ∈ PuncturedDisc) : 0 < (Real.log (‖z‖ ^ 2)) ^ 2 := by
  have hne : Real.log (‖z‖ ^ 2) ≠ 0 := log_norm_sq_ne_zero hz
  positivity

lemma poincareDenominator_pos {z : ℂ} (hz : z ∈ PuncturedDisc) :
    0 < ‖z‖ ^ 2 * (Real.log (‖z‖ ^ 2)) ^ 2 := by
  have h1 : 0 < ‖z‖ ^ 2 := norm_sq_pos hz
  have h2 : 0 < (Real.log (‖z‖ ^ 2)) ^ 2 := log_norm_sq_sq_pos hz
  positivity

lemma poincareDensity_pos {z : ℂ} (hz : z ∈ PuncturedDisc) : 0 < poincareDensity z := by
  unfold poincareDensity
  have hden : 0 < ‖z‖ ^ 2 * (Real.log (‖z‖ ^ 2)) ^ 2 := poincareDenominator_pos hz
  positivity

end Sandbox.Restore.PoincareMetric
