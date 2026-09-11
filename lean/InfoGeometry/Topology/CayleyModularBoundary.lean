import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.HyperbolicSL2BoundaryFlow

namespace InfoGeometry.Topology

/-!
# Cayley transport of the hyperbolic boundary coordinate

The formulas are stated with explicit denominator hypotheses.  This keeps the
chart theorem honest at poles and leaves the real-analysis nonvanishing proof
as a separate strengthening.
-/

noncomputable def diskBoostParameter (s : ℝ) : ℝ :=
  (Real.exp (2 * s) - 1) / (Real.exp (2 * s) + 1)

noncomputable def cayleyBoundary (x : ℝ) : ℂ :=
  ((x : ℂ) - Complex.I) / ((x : ℂ) + Complex.I)

noncomputable def diskBoundaryBoost (s : ℝ) (z : ℂ) : ℂ :=
  (z + (diskBoostParameter s : ℂ)) /
    ((diskBoostParameter s : ℂ) * z + 1)

theorem cayleyBoundary_den_ne_zero (x : ℝ) :
    (x : ℂ) + Complex.I ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  norm_num at him

theorem diskBoostParameter_den_ne_zero (s : ℝ) :
    Real.exp (2 * s) + 1 ≠ 0 := by
  positivity

theorem diskBoundaryBoost_fixed_minus_one_of_den_ne_zero
    (s : ℝ)
    (hden : -(1 : ℂ) * (diskBoostParameter s : ℂ) + 1 ≠ 0) :
    diskBoundaryBoost s (-1) = (-1 : ℂ) := by
  unfold diskBoundaryBoost
  have hden' : (diskBoostParameter s : ℂ) * (-1 : ℂ) + 1 ≠ 0 := by
    simpa [mul_comm] using hden
  have hcancel : ((diskBoostParameter s : ℂ) * (-1 : ℂ) + 1) *
      ((diskBoostParameter s : ℂ) * (-1 : ℂ) + 1)⁻¹ = 1 := by
    simpa using mul_inv_cancel₀ hden'
  calc
    (-1 + (diskBoostParameter s : ℂ)) /
        ((diskBoostParameter s : ℂ) * (-1 : ℂ) + 1) =
      -(((diskBoostParameter s : ℂ) * (-1 : ℂ) + 1) *
          ((diskBoostParameter s : ℂ) * (-1 : ℂ) + 1)⁻¹) := by
      simp [div_eq_mul_inv]
      ring
    _ = -1 := by rw [hcancel]

theorem diskBoundaryBoost_fixed_one_of_den_ne_zero
    (s : ℝ)
    (hden : (diskBoostParameter s : ℂ) + 1 ≠ 0) :
    diskBoundaryBoost s 1 = (1 : ℂ) := by
  unfold diskBoundaryBoost
  simpa [div_eq_mul_inv, add_comm] using (mul_inv_cancel₀ hden)

end InfoGeometry.Topology
