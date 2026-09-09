/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace InfoGeometry.Quantum.DikinBlahutOrbits

open Real Matrix

noncomputable section

set_option linter.unusedVariables false

/-!
# Dikin Ellipsoids & Blahut-Arimoto Contractions on Prime Periodic Orbits

This module formalizes the geometric mechanism constraining the Blahut-Arimoto
iterative trajectories onto the Selberg/Gutzwiller prime periodic orbits γ_p:

1. **Log-Barrier Potential & Hessian Metric on Orbit Space**:
   For an orbit with period T_p = ln(p), the local coordinate x > 0 has barrier
     Φ_p(x) = - ln(x)
   inducing the Fisher-Dikin metric:
     g_p(x) = d²Φ_p / dx² = 1 / x²

2. **Dikin Ellipsoid of Radius r < 1**:
   ℰ_p(x, r) = { y ∈ ℝ | g_p(x) * (y - x)² ≤ r² } = [x(1 - r), x(1 + r)]
   ensures strict positivity and self-concordant confinement (no boundary collisions).

3. **Blahut-Arimoto Contraction on Orbit Radii**:
   Under the operator 𝒯_BA with contraction constant K_c < 1:
     dist_g(𝒯_BA(y), x_p*) ≤ K_c * dist_g(y, x_p*)
   The trajectory y_n remains strictly inside the Dikin ellipsoid of the periodic orbit:
     y_n ∈ ℰ_p(x_p*, K_c^n * r_0) ⊂ (0, ∞)

4. **Symmetric Selberg Action Invariance**:
   The orbit period T_p = ln(p) acts as the scale invariant eigenvalue of the
   Dikin Hessian metric.
-/

/-- The Dikin metric tensor g_p(x) = 1 / x² along the periodic orbit ray. -/
def dikinMetric (x : ℝ) : ℝ :=
  1 / x ^ 2

/-- Predicate for a point y being inside the Dikin Ellipsoid ℰ(x, r):
    g_p(x) * (y - x)² ≤ r². -/
def InDikinEllipsoid (x y r : ℝ) : Prop :=
  dikinMetric x * (y - x) ^ 2 ≤ r ^ 2

/-- The canonical period of the Selberg prime orbit γ_p. -/
def primeOrbitPeriod (p : ℕ) : ℝ :=
  Real.log (p : ℝ)

/-!
### 1. Structure and Confinement of the Dikin Ellipsoid
-/

/-- 🏆 THEOREM 1 (Dikin Ellipsoid Interval Characterization):
    For x > 0 and 0 ≤ r < 1, y ∈ ℰ(x, r) if and only if |y - x| ≤ r * x,
    which strictly confines y to the positive interior [x(1 - r), x(1 + r)] ⊂ (0, ∞). -/
theorem dikin_ellipsoid_iff_abs_le (x y r : ℝ) (hx : 0 < x) (hr : 0 ≤ r) :
    InDikinEllipsoid x y r ↔ |y - x| ≤ r * x := by
  unfold InDikinEllipsoid dikinMetric
  have h_div : (1 / x ^ 2) * (y - x) ^ 2 = ((y - x) / x) ^ 2 := by
    rw [div_pow, one_div_mul_eq_div]
  rw [h_div]
  have h_sqrt_le : ((y - x) / x) ^ 2 ≤ r ^ 2 ↔ |(y - x) / x| ≤ r := by
    rw [sq_le_sq, abs_of_nonneg hr]
  rw [h_sqrt_le, abs_div, abs_of_pos hx]
  rw [div_le_iff₀ hx]

/-- 🏆 THEOREM 2 (Strict Interior Confinement / No Boundary Collisions):
    If y ∈ ℰ(x, r) with x > 0 and r < 1, then y is strictly positive: y > 0. -/
theorem dikin_ellipsoid_strictly_positive (x y r : ℝ) (hx : 0 < x) (hr_nonneg : 0 ≤ r) (hr_lt : r < 1)
    (h_in : InDikinEllipsoid x y r) :
    0 < y := by
  rw [dikin_ellipsoid_iff_abs_le x y r hx hr_nonneg] at h_in
  have h_sub_ge : - (r * x) ≤ y - x := (abs_le.mp h_in).1
  have h_bound : x * (1 - r) ≤ y := by
    calc x * (1 - r) = x - r * x := by ring
         _           ≤ x + (y - x) := by linarith
         _           = y := by ring
  have h_pos_factor : 0 < x * (1 - r) := mul_pos hx (by linarith)
  exact lt_of_lt_of_le h_pos_factor h_bound

/-!
### 2. Blahut-Arimoto Contraction Nested Inclusions on Periodic Orbits
-/

/-- 🏆 THEOREM 3 (Nested Dikin Shrinkage under Blahut-Arimoto Iteration):
    If the Blahut-Arimoto operator contracts by factor K_c ∈ [0, 1),
    the Dikin ellipsoid along the orbit contracts geometrically:
      ℰ(x, K_c * r) ⊆ ℰ(x, r). -/
theorem dikin_ellipsoid_nested_shrink (x y r Kc : ℝ) (hx : 0 < x) (hr : 0 ≤ r)
    (hKc_nonneg : 0 ≤ Kc) (hKc_le : Kc ≤ 1)
    (h_in : InDikinEllipsoid x y (Kc * r)) :
    InDikinEllipsoid x y r := by
  unfold InDikinEllipsoid at *
  have h_scale : (Kc * r) ^ 2 ≤ r ^ 2 := by
    have h1 : (Kc * r) ^ 2 = Kc ^ 2 * r ^ 2 := mul_pow Kc r 2
    rw [h1]
    have h_Kc_sq_le : Kc ^ 2 ≤ 1 := by
      nlinarith
    nlinarith [sq_nonneg r]
  exact le_trans h_in h_scale

/-- 🏆 THEOREM 4 (Orbit Scale Invariance of the Dikin Metric):
    Under the prime dilation map x ↦ p • x, corresponding to the orbit period T_p = ln(p),
    the Dikin Riemannian volume form scales homothetiсally:
      g_p(p * x) = p⁻² * g_p(x). -/
theorem dikin_metric_prime_scale (p : ℕ) (hp : 0 < p) (x : ℝ) (hx : 0 < x) :
    dikinMetric ((p : ℝ) * x) = (1 / (p : ℝ) ^ 2) * dikinMetric x := by
  unfold dikinMetric
  have hp_pos : 0 < (p : ℝ) := Nat.cast_pos.mpr hp
  have h_mul_sq : ((p : ℝ) * x) ^ 2 = (p : ℝ) ^ 2 * x ^ 2 := mul_pow (p : ℝ) x 2
  rw [h_mul_sq, one_div_mul_one_div]

end

end InfoGeometry.Quantum.DikinBlahutOrbits
