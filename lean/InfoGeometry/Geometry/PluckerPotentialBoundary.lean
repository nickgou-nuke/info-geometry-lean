/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.PluckerDualFlatBridge
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Convex.Function
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Chosen convex potentials versus the ambient Plücker norm

The existing normalized chart has independent coordinates
`(p02,p03,p12,p13)` and dependent coordinate `p23 = p02*p13-p03*p12`.
Pulling the ambient six-coordinate Euclidean quadratic potential back along
this nonlinear chart does not preserve convexity. An exact midpoint
counterexample proves this using native `ConvexOn`.

In contrast, the quadratic potential on the four independent coordinates
is strictly convex. Its actual Fréchet derivative and Bregman divergence
are computed below. This is chosen Euclidean information-potential data,
not an identification of positive Hessian geometry with the indefinite
Klein polarity or a construction of a statistical model.
-/

noncomputable section

namespace InfoGeometry.Geometry.PluckerPotentialBoundary

open PluckerDualFlatBridge
open Matrix
open scoped BigOperators Matrix

/-- Pullback of the ambient positive quadratic potential in six coordinates. -/
def ambientPluckerPotential (u : PluckerAffineChart) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin 6, (reconstructPlucker u i) ^ 2

theorem ambientPluckerPotential_formula (u : PluckerAffineChart) :
    ambientPluckerPotential u = (1 / 2 : ℝ) *
      (1 + u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 +
        (u 0 * u 3 - u 1 * u 2) ^ 2) := by
  simp [ambientPluckerPotential, reconstructPlucker, Fin.sum_univ_succ]
  ring

/-- Strict failure of the midpoint inequality on the existing chart. -/
theorem ambientPluckerPotential_midpoint_violation :
    (ambientPluckerPotential ![3, 0, 0, 1] +
      ambientPluckerPotential ![1, 0, 0, 3]) / 2 <
      ambientPluckerPotential ![2, 0, 0, 2] := by
  norm_num [ambientPluckerPotential_formula]

/-- Positive ambient Hessian does not imply convexity in nonlinear chart coordinates. -/
theorem ambientPluckerPotential_not_convex :
    ¬ ConvexOn ℝ Set.univ ambientPluckerPotential := by
  intro h
  have hineq := h.2
  have hm := hineq (x := (![3, 0, 0, 1] : PluckerAffineChart)) (Set.mem_univ _)
    (y := (![1, 0, 0, 3] : PluckerAffineChart)) (Set.mem_univ _)
    (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  norm_num [ambientPluckerPotential_formula, Pi.add_apply, Pi.smul_apply] at hm

/-- A separately chosen quadratic potential on the independent chart coordinates. -/
def chartPotential (u : PluckerAffineChart) : ℝ := (1 / 2 : ℝ) * (u ⬝ᵥ u)

theorem chartPotential_jensen_gap (u v : PluckerAffineChart) (a b : ℝ)
    (hab : a + b = 1) :
    a * chartPotential u + b * chartPotential v - chartPotential (a • u + b • v) =
      a * b / 2 * ((u - v) ⬝ᵥ (u - v)) := by
  have hb : b = 1 - a := by linarith only [hab]
  rw [hb]
  simp only [chartPotential, dotProduct, Fin.sum_univ_four, Pi.add_apply,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

theorem chartPotential_strictConvex : StrictConvexOn ℝ Set.univ chartPotential := by
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ huv a b ha hb hab
  have hn : 0 ≤ (u - v) ⬝ᵥ (u - v) :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg ((u - v) i))
  have hne : (u - v) ⬝ᵥ (u - v) ≠ 0 := by
    intro hz
    exact huv (sub_eq_zero.mp (dotProduct_self_eq_zero.mp hz))
  have hpos : 0 < (u - v) ⬝ᵥ (u - v) := lt_of_le_of_ne hn (Ne.symm hne)
  have hgap := chartPotential_jensen_gap u v a b hab
  have hp := mul_pos (div_pos (mul_pos ha hb) (by norm_num : (0 : ℝ) < 2)) hpos
  simpa only [smul_eq_mul] using (show
    chartPotential (a • u + b • v) < a * chartPotential u + b * chartPotential v by
      linarith)

/-- Explicit derivative as a native continuous linear covector. -/
def chartGradient (u : PluckerAffineChart) : PluckerAffineChart →L[ℝ] ℝ :=
  ∑ i : Fin 4, u i • ContinuousLinearMap.proj i

@[simp] theorem chartGradient_apply (u v : PluckerAffineChart) :
    chartGradient u v = u ⬝ᵥ v := by
  simp [chartGradient, dotProduct]

theorem hasFDerivAt_chartPotential (u : PluckerAffineChart) :
    HasFDerivAt chartPotential (chartGradient u) u := by
  have hi (i : Fin 4) := (hasFDerivAt_apply (𝕜 := ℝ) i u).mul
    (hasFDerivAt_apply (𝕜 := ℝ) i u)
  have h := (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)).const_mul (1 / 2 : ℝ)
  convert h using 1
  · rfl
  · ext v
    simp [chartGradient, Fin.sum_univ_four]
    ring

/-- Use the existing potential owner, with the chosen potential now proved regular and convex. -/
def quadraticChartGeometry : PluckerHessianGeometry := ⟨chartPotential⟩

theorem quadraticChart_dualCoord (u : PluckerAffineChart) :
    pluckerDualCoord quadraticChartGeometry u = chartGradient u :=
  (hasFDerivAt_chartPotential u).fderiv

theorem quadraticChart_bregman (u v : PluckerAffineChart) :
    pluckerBregman quadraticChartGeometry u v = (1 / 2 : ℝ) * ((u - v) ⬝ᵥ (u - v)) := by
  rw [pluckerBregman, quadraticChart_dualCoord, chartGradient_apply]
  change chartPotential u - chartPotential v - v ⬝ᵥ (u - v) = _
  simp only [chartPotential, dotProduct, Fin.sum_univ_four, Pi.sub_apply]
  ring

theorem quadraticChart_bregman_nonneg (u v : PluckerAffineChart) :
    0 ≤ pluckerBregman quadraticChartGeometry u v := by
  rw [quadraticChart_bregman]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => mul_self_nonneg ((u - v) i)))

theorem quadraticChart_bregman_eq_zero_iff (u v : PluckerAffineChart) :
    pluckerBregman quadraticChartGeometry u v = 0 ↔ u = v := by
  rw [quadraticChart_bregman]
  constructor
  · intro h
    have hd : (u - v) ⬝ᵥ (u - v) = 0 :=
      (mul_eq_zero.mp h).resolve_left (by norm_num)
    exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp hd)
  · rintro rfl
    simp

end InfoGeometry.Geometry.PluckerPotentialBoundary
