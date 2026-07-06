import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic

open Complex Metric Topology

/-- The punctured unit disc D^* in the complex plane. -/
def PuncturedDisc : Set ℂ := {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1}

/-- The density function of the Poincaré metric on the punctured unit disc.
    Corresponds to the coefficient in ω_{D^*} = (i dz ∧ d z̄) / (|z|^2 (log |z|^2)^2). -/
noncomputable def poincareDensity (z : ℂ) : ℝ :=
  1 / (‖z‖ ^ 2 * (Real.log (‖z‖ ^ 2)) ^ 2)

lemma poincareDensity_pos {z : ℂ} (hz : z ∈ PuncturedDisc) : 0 < poincareDensity z := by
  sorry
