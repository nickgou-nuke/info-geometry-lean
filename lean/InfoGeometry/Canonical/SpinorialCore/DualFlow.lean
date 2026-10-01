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
  convert (Real.hasDerivAt_exp t).smul hv using 1
  simp

/-- The closed-form decaying orbit satisfies the linearized ODE. -/
theorem exponential_orbit_hasDerivAt (v0 : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-s) • v0)
      (-(Real.exp (-t) • v0)) t := by
  convert ((Real.hasDerivAt_exp (-t)).comp t
    ((hasDerivAt_id t).neg)).smul_const v0 using 1
  simp

/-- Every globally differentiable solution of v' = -v is its decaying exponential orbit. -/
theorem dual_solution_eq_exponential (v : ℝ → E)
    (hv : ∀ t, HasDerivAt v (-(v t)) t) (t : ℝ) :
    v t = Real.exp (-t) • v 0 := by
  let w : ℝ → E := fun s => Real.exp s • v s
  have hw : ∀ s, HasDerivAt w 0 s := fun s => dual_integrating_factor v s (hv s)
  have hconst : w t = w 0 :=
    is_const_of_deriv_eq_zero (fun s => (hw s).differentiableAt)
      (fun s => (hw s).deriv) t 0
  have h := congrArg (fun z : E => Real.exp (-t) • z) hconst
  simpa [w, smul_smul, ← Real.exp_add] using h

/-- Global closed form of a trajectory with an invertible coordinate derivative. -/
theorem dual_flow_closed_form (eta : E → E) (theta : ℝ → E)
    (G : ℝ → E ≃L[ℝ] E)
    (heta : ∀ t, HasFDerivAt eta (G t : E →L[ℝ] E) (theta t))
    (htheta : ∀ t, HasDerivAt theta (-((G t).symm (eta (theta t)))) t)
    (t : ℝ) : eta (theta t) = Real.exp (-t) • eta (theta 0) :=
  dual_solution_eq_exponential (fun s => eta (theta s))
    (fun s => dual_coordinate_linearization eta theta s (G s) (heta s) (htheta s)) t

end InfoGeometry.Canonical.SpinorialCore
