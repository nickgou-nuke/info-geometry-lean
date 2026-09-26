import InfoGeometry.Canonical.PolarizedShearSpinFrame
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Evolution of the finite polarized shear and spin energy

The existing quadratic energy has an exact exponential law along a supplied
differentiable solution of the finite constant-coefficient ODE.  Its coercivity
then gives a uniform coordinate bound in the elliptic regime with nonnegative
damping.  These theorems concern the finite ODE; they do not construct a fluid
solution or assert an extension theorem for a PDE.
-/

noncomputable section

namespace InfoGeometry.Canonical.PolarizedShearSpinFrame

/-- The integrating factor is constant because its derivative vanishes. -/
theorem energy_evolution {s w nu : ℝ} {x : ℝ → Vec2}
    (hx : ∀ t : ℝ, ∀ i : Fin 2, HasDerivAt (fun tau => x tau i)
      (velocity s w nu (x t) i) t) (t0 t : ℝ) :
    energy s w (x t) =
      Real.exp (-2 * nu * (t - t0)) * energy s w (x t0) := by
  have hfactor : ∀ tau : ℝ,
      HasDerivAt (fun r => Real.exp (2 * nu * (r - t0)) * energy s w (x r))
        0 tau := by
    intro tau
    have hlin : HasDerivAt (fun r : ℝ => 2 * nu * (r - t0)) (2 * nu) tau := by
      simpa using ((hasDerivAt_id tau).sub_const t0).const_mul (2 * nu)
    convert hlin.exp.mul (hasDerivAt_energy (hx tau)) using 1
    ring
  have hconst : Real.exp (2 * nu * (t - t0)) * energy s w (x t) =
      energy s w (x t0) := by
    have hc := is_const_of_deriv_eq_zero
      (fun tau => (hfactor tau).differentiableAt)
      (fun tau => (hfactor tau).deriv) t t0
    simpa using hc
  have hinverse : Real.exp (-2 * nu * (t - t0)) *
      Real.exp (2 * nu * (t - t0)) = 1 := by
    rw [← Real.exp_add]
    have hz : -2 * nu * (t - t0) + 2 * nu * (t - t0) = 0 := by ring
    rw [hz, Real.exp_zero]
  calc
    energy s w (x t) =
        (Real.exp (-2 * nu * (t - t0)) * Real.exp (2 * nu * (t - t0))) *
          energy s w (x t) := by rw [hinverse, one_mul]
    _ = Real.exp (-2 * nu * (t - t0)) *
        (Real.exp (2 * nu * (t - t0)) * energy s w (x t)) := by ring
    _ = Real.exp (-2 * nu * (t - t0)) * energy s w (x t0) := by rw [hconst]

/-- Nonnegative damping decreases the positive adapted energy forward in time. -/
theorem energy_le_initial {s w nu t0 t : ℝ} {x : ℝ → Vec2}
    (hx : ∀ r : ℝ, ∀ i : Fin 2, HasDerivAt (fun tau => x tau i)
      (velocity s w nu (x r) i) r)
    (helliptic : |s| < w) (hnu : 0 ≤ nu) (ht : t0 ≤ t) :
    energy s w (x t) ≤ energy s w (x t0) := by
  rw [energy_evolution hx t0 t]
  have hexponent : -2 * nu * (t - t0) ≤ 0 := by
    have hp := mul_nonneg hnu (sub_nonneg.mpr ht)
    nlinarith
  have hexp := Real.exp_le_one_iff.mpr hexponent
  simpa using mul_le_mul_of_nonneg_right hexp (energy_nonneg helliptic (x t0))

/-- The fixed spectral gap `w-|s|` controls the full coordinate square sum. -/
theorem coordinate_square_bound {s w nu t0 t : ℝ} {x : ℝ → Vec2}
    (hx : ∀ r : ℝ, ∀ i : Fin 2, HasDerivAt (fun tau => x tau i)
      (velocity s w nu (x r) i) r)
    (helliptic : |s| < w) (hnu : 0 ≤ nu) (ht : t0 ≤ t) :
    x t 0 ^ 2 + x t 1 ^ 2 ≤
      ((w + |s|) / (w - |s|)) * (x t0 0 ^ 2 + x t0 1 ^ 2) := by
  have hbound : (w - |s|) * (x t 0 ^ 2 + x t 1 ^ 2) ≤
      (w + |s|) * (x t0 0 ^ 2 + x t0 1 ^ 2) :=
    (energy_lower_bound s w (x t)).trans
      ((energy_le_initial hx helliptic hnu ht).trans (energy_upper_bound s w (x t0)))
  calc
    x t 0 ^ 2 + x t 1 ^ 2 ≤
        ((w + |s|) * (x t0 0 ^ 2 + x t0 1 ^ 2)) / (w - |s|) :=
      (le_div_iff₀ (sub_pos.mpr helliptic)).mpr (by simpa [mul_comm] using hbound)
    _ = ((w + |s|) / (w - |s|)) * (x t0 0 ^ 2 + x t0 1 ^ 2) := by ring

end InfoGeometry.Canonical.PolarizedShearSpinFrame
