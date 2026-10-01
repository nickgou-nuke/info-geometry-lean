import InfoGeometry.Canonical.SpinorialCore.Algebra

/-!
# Exact dual-coordinate linearization

`eta` is an actual differentiable coordinate map and `G` its derivative.
Invertibility is supplied as a continuous linear equivalence. No claim that
an arbitrary log determinant is a Fisher potential is built into this theorem.
-/

namespace InfoGeometry.Canonical.SpinorialCore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Chain-rule linearization of the inverse-derivative flow. -/
theorem dual_coordinate_linearization
    (eta : E → E) (theta : ℝ → E) (t : ℝ) (G : E ≃L[ℝ] E)
    (heta : HasFDerivAt eta (G : E →L[ℝ] E) (theta t))
    (htheta : HasDerivAt theta (-(G.symm (eta (theta t)))) t) :
    HasDerivAt (fun s => eta (theta s)) (-(eta (theta t))) t := by
  simpa using heta.comp_hasDerivAt t htheta

/-- The integrating factor has zero derivative for every actual solution. -/
theorem dual_integrating_factor
    (v : ℝ → E) (t : ℝ) (hv : HasDerivAt v (-(v t)) t) :
    HasDerivAt (fun s => Real.exp s • v s) 0 t := by
  convert (Real.hasDerivAt_exp t).smul hv using 1 <;> simp

/-- The closed-form decaying orbit satisfies the linearized ODE. -/
theorem exponential_orbit_hasDerivAt (v0 : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-s) • v0)
      (-(Real.exp (-t) • v0)) t := by
  convert ((Real.hasDerivAt_exp (-t)).comp t
    ((hasDerivAt_id t).neg)).smul_const v0 using 1 <;> simp

end InfoGeometry.Canonical.SpinorialCore
