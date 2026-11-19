/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Consequences and limitations of a real information-rate budget

Source: *Complete Holographic White Paper*, version 6.1, sections 5.9--5.11.
The rate identity and the relation between speed and spatial rate are hypotheses.
The square-root formula follows for real rates and a nonnegative internal rate.
This does not prove a Lorentz transformation law, observer invariance, or a
continuum limit. The energy inequality concerns a finite real-valued expression.
-/

namespace InfoGeometry.Holographic.RateBudget

/-- The rate constraint bounds the absolute value of the calibrated velocity. -/
theorem velocity_abs_le {internal spatial maximum c velocity : ℝ}
    (hmaximum : 0 < maximum) (hc : 0 < c)
    (hbudget : internal ^ 2 + spatial ^ 2 = maximum ^ 2)
    (hspatial : spatial = velocity * maximum / c) :
    |velocity| ≤ c := by
  have hspatial_sq : spatial ^ 2 ≤ maximum ^ 2 := by
    nlinarith only [hbudget, sq_nonneg internal]
  have hscale : spatial * c = velocity * maximum :=
    (eq_div_iff hc.ne').mp hspatial
  have hscale_sq : spatial ^ 2 * c ^ 2 = velocity ^ 2 * maximum ^ 2 := by
    calc
      spatial ^ 2 * c ^ 2 = (spatial * c) ^ 2 := (mul_pow spatial c 2).symm
      _ = (velocity * maximum) ^ 2 := congrArg (fun x : ℝ => x ^ 2) hscale
      _ = velocity ^ 2 * maximum ^ 2 := mul_pow velocity maximum 2
  have hproduct : velocity ^ 2 * maximum ^ 2 ≤ c ^ 2 * maximum ^ 2 := by
    calc
      velocity ^ 2 * maximum ^ 2 = spatial ^ 2 * c ^ 2 := hscale_sq.symm
      _ ≤ maximum ^ 2 * c ^ 2 :=
        mul_le_mul_of_nonneg_right hspatial_sq (sq_nonneg c)
      _ = c ^ 2 * maximum ^ 2 := mul_comm _ _
  have hvelocity_sq : velocity ^ 2 ≤ c ^ 2 :=
    (mul_le_mul_iff_of_pos_right (pow_pos hmaximum 2)).mp hproduct
  exact abs_le_of_sq_le_sq hvelocity_sq hc.le

/-- A nonnegative spatial rate gives a velocity in the closed interval `[0, c]`. -/
theorem velocity_mem_interval {internal spatial maximum c velocity : ℝ}
    (hmaximum : 0 < maximum) (hc : 0 < c) (hspatial_nonneg : 0 ≤ spatial)
    (hbudget : internal ^ 2 + spatial ^ 2 = maximum ^ 2)
    (hspatial : spatial = velocity * maximum / c) :
    0 ≤ velocity ∧ velocity ≤ c := by
  have hscale : spatial * c = velocity * maximum :=
    (eq_div_iff hc.ne').mp hspatial
  have hproduct : 0 ≤ velocity * maximum := by
    rw [← hscale]
    exact mul_nonneg hspatial_nonneg hc.le
  exact ⟨(mul_nonneg_iff_of_pos_right hmaximum).mp hproduct,
    (le_abs_self velocity).trans (velocity_abs_le hmaximum hc hbudget hspatial)⟩

/-- The normalized internal rate has exactly the expected square. -/
theorem internal_sq_eq {internal spatial maximum c velocity : ℝ}
    (hbudget : internal ^ 2 + spatial ^ 2 = maximum ^ 2)
    (hspatial : spatial = velocity * maximum / c) :
    internal ^ 2 = maximum ^ 2 * (1 - velocity ^ 2 / c ^ 2) := by
  rw [hspatial] at hbudget
  calc
    internal ^ 2 = maximum ^ 2 - (velocity * maximum / c) ^ 2 := by linarith
    _ = maximum ^ 2 * (1 - velocity ^ 2 / c ^ 2) := by
      rw [div_pow, mul_pow]
      ring

/-- The square-root argument is nonnegative under the real rate constraint. -/
theorem rate_radicand_nonneg {internal spatial maximum c velocity : ℝ}
    (hmaximum : 0 < maximum)
    (hbudget : internal ^ 2 + spatial ^ 2 = maximum ^ 2)
    (hspatial : spatial = velocity * maximum / c) :
    0 ≤ 1 - velocity ^ 2 / c ^ 2 := by
  have h := sq_nonneg internal
  rw [internal_sq_eq hbudget hspatial] at h
  exact (mul_nonneg_iff_of_pos_left (pow_pos hmaximum 2)).mp h

/-- The nonnegative internal rate is the positive square-root branch. -/
theorem internal_eq_sqrt {internal spatial maximum c velocity : ℝ}
    (hinternal : 0 ≤ internal) (hmaximum : 0 ≤ maximum)
    (hbudget : internal ^ 2 + spatial ^ 2 = maximum ^ 2)
    (hspatial : spatial = velocity * maximum / c) :
    internal = maximum * Real.sqrt (1 - velocity ^ 2 / c ^ 2) := by
  calc
    internal = Real.sqrt (internal ^ 2) := (Real.sqrt_sq hinternal).symm
    _ = Real.sqrt (maximum ^ 2 * (1 - velocity ^ 2 / c ^ 2)) :=
      congrArg Real.sqrt (internal_sq_eq hbudget hspatial)
    _ = Real.sqrt (maximum ^ 2) * Real.sqrt (1 - velocity ^ 2 / c ^ 2) :=
      Real.sqrt_mul (sq_nonneg maximum) _
    _ = maximum * Real.sqrt (1 - velocity ^ 2 / c ^ 2) := by
      rw [Real.sqrt_sq hmaximum]

/-- At unit effective speed, equation (25) of the source permits only zero graph distance. -/
theorem unit_speed_diamond_iff {elapsed distance : ℝ} (hdistance : 0 ≤ distance) :
    |elapsed| + distance ≤ 1 * |elapsed| ↔ distance = 0 := by
  constructor
  · intro h
    linarith only [h, hdistance]
  · intro h
    simp [h]

/-- Nonnegative weights make every term of the finite real lattice energy nonnegative.

In a physical use of this expression one additionally requires `g ≠ 0`.
The inequality itself also holds at zero under the total division operation of `ℝ`.
-/
theorem finite_lattice_energy_nonneg {Edge Plaquette : Type*}
    (edges : Finset Edge) (plaquettes : Finset Plaquette)
    (electric : Edge → ℝ) (weight phase : Plaquette → ℝ) (g : ℝ)
    (hweight : ∀ p ∈ plaquettes, 0 ≤ weight p) :
    0 ≤ (g ^ 2 / 2) * (∑ e ∈ edges, electric e ^ 2) +
      (1 / g ^ 2) * (∑ p ∈ plaquettes, weight p * (1 - Real.cos (phase p))) := by
  apply add_nonneg
  · exact mul_nonneg (div_nonneg (sq_nonneg g) (by norm_num))
      (Finset.sum_nonneg (fun e _ => sq_nonneg (electric e)))
  · exact mul_nonneg (div_nonneg (by norm_num) (sq_nonneg g))
      (Finset.sum_nonneg (fun p hp =>
        mul_nonneg (hweight p hp) (sub_nonneg.mpr (Real.cos_le_one (phase p)))))

end InfoGeometry.Holographic.RateBudget
