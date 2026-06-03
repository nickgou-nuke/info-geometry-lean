import Mathlib

/-!
# Finite JKO/Weyl--Gromov Dynamics

This file records two closed finite real theorems:

* a quadratic discrete JKO/Bayesian gradient step strictly decreases free
  energy under the usual explicit step-size bound;
* projective normalization by a positive partition function is invariant under
  positive Weyl scaling.

These are finite algebraic/ordered-field statements.  They do not assert the
continuous JKO-to-Fokker--Planck limit.
-/

namespace InfoGeometry.Dynamics

noncomputable section

/--
Closed finite H-theorem for a one-dimensional quadratic JKO/Bayesian gradient
step.

For `F x = (1 / 2) * a * x^2` with `a > 0`, the explicit update
`x ↦ (1 - τ * a) * x` strictly decreases `F` whenever `x ≠ 0` and
`0 < τ < 2 / a`.
-/
theorem free_energy_decrease
    (a : ℝ) (ha : a > 0)
    (x : ℝ) (hx : x ≠ 0)
    (τ : ℝ) (hτ1 : 0 < τ) (hτ2 : τ < 2 / a) :
    (1 / 2 : ℝ) * a * ((1 - τ * a) * x)^2 <
      (1 / 2 : ℝ) * a * x^2 := by
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have h_factor : 0 < (1 / 2 : ℝ) * a * x ^ 2 := by positivity
  have h_tau_a_pos : 0 < τ * a := mul_pos hτ1 ha
  have h_tau_a_lt_two : τ * a < 2 := by
    calc
      τ * a < (2 / a) * a := mul_lt_mul_of_pos_right hτ2 ha
      _ = 2 := div_mul_cancel₀ 2 (ne_of_gt ha)
  have h_lt : (1 - τ * a) ^ 2 < 1 := by
    have h_fac : (1 - τ * a) ^ 2 - 1 = - (τ * a) * (2 - τ * a) := by ring
    have h_prod_pos : 0 < (τ * a) * (2 - τ * a) := by
      exact mul_pos h_tau_a_pos (by linarith)
    nlinarith
  have h_final :
      (1 - τ * a) ^ 2 * ((1 / 2 : ℝ) * a * x ^ 2) <
        1 * ((1 / 2 : ℝ) * a * x ^ 2) := by
    exact mul_lt_mul_of_pos_right h_lt h_factor
  calc
    (1 / 2 : ℝ) * a * ((1 - τ * a) * x)^2
        = (1 - τ * a) ^ 2 * ((1 / 2 : ℝ) * a * x ^ 2) := by ring
    _ < 1 * ((1 / 2 : ℝ) * a * x ^ 2) := h_final
    _ = (1 / 2 : ℝ) * a * x ^ 2 := by ring

/--
A finite projected state represented by an unnormalized density and a positive
partition function.
-/
structure ProjectedState where
  /-- Unnormalized state density. -/
  density : ℝ
  /-- Partition function / normalization constant. -/
  partition : ℝ
  /-- Positivity of the partition function. -/
  h_partition_pos : 0 < partition

/-- Positive Weyl scaling of both density and partition function. -/
def weyl_scale (c : ℝ) (hc : 0 < c) (P : ProjectedState) : ProjectedState where
  density := c * P.density
  partition := c * P.partition
  h_partition_pos := mul_pos hc P.h_partition_pos

/-- Gromov projective normalization by the partition function. -/
def gromov_projective_map (P : ProjectedState) : ℝ :=
  P.density / P.partition

/--
Closed finite Weyl invariance theorem for Gromov projective normalization.

Positive conformal scaling of density and partition function leaves the
normalized projected state unchanged.
-/
theorem gromov_projective_weyl_invariance
    (c : ℝ) (hc : 0 < c) (P : ProjectedState) :
    gromov_projective_map (weyl_scale c hc P) = gromov_projective_map P := by
  unfold gromov_projective_map weyl_scale
  exact mul_div_mul_left P.density P.partition (ne_of_gt hc)

end

end InfoGeometry.Dynamics
