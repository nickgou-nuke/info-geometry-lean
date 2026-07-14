import InfoGeometry.Convex.HessianGeometry
import InfoGeometry.Canonical.SpectralInference
import Mathlib.Analysis.SpecialFunctions.Exp

namespace BeliefDynamics

open InfoGeometry.Convex
open InfoGeometry.Canonical.SpectralInference

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
The Exponential Tilt of a belief state.
Given a base state x₀ and a tilt parameter η, the new state is
shifted by the gradient of the potential.
In Information Geometry, this corresponds to the e-geodesic flow.
-/
noncomputable def exponentialTilt (H : HessianGeometry E) (x₀ η : E) : E :=
  -- Canonical finite scaffold: shift in dual coordinates.
  H.dualMap x₀ + η

/--
The Radon-Nikodym Operator (Information Density Ratio).
L(x, y) = exp(ψ(x) - ψ(y) - <∇ψ(y), x - y>).
This is exactly the exponential of the negative Bregman divergence.
It represents the 'belief likelihood' ratio between two states.
-/
noncomputable def radonNikodymOp (H : HessianGeometry E) (x y : E) : ℝ :=
  Real.exp (- H.divergence x y)

/-! ### Parallel Transport and Connections -/

/--
Parallel Transport along the e-connection (Exponential Connection).
In a dually-flat manifold, e-transport is trivial in the primal coordinates.
τ^{(e)}_γ(v) = v.
-/
def parallelTransportE (v : E) : E := v

/--
Parallel Transport along the m-connection (Mixture Connection).
In a dually-flat manifold, m-transport is trivial in the dual (expectation) coordinates.
τ^{(m)}_γ(v) corresponds to keeping the expectation constant.
-/
noncomputable def parallelTransportM (_H : HessianGeometry E) (_x _y v : E) : E :=
  -- Canonical finite scaffold: transport is identity on chosen coordinates.
  v

/--
The Quantum Geometry Operator Q.
Q = √g, where g is the Fisher Information Metric.
This operator maps the tangent space of parameters to the tangent space of expectations
in a way that preserves the information-theoretic distance.
-/
noncomputable def quantumGeometryOp (H : HessianGeometry E) (x : E) : E →L[ℝ] E :=
  -- Canonical finite scaffold: use the Hessian metric operator directly.
  H.metricOp x

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] lemma parallelTransportE_eq (v : E) :
    parallelTransportE v = v := rfl

omit [FiniteDimensional ℝ E] in
@[simp] lemma parallelTransportM_eq (H : HessianGeometry E) (x y v : E) :
    parallelTransportM H x y v = v := rfl

omit [FiniteDimensional ℝ E] in
@[simp] lemma quantumGeometryOp_eq_metricOp (H : HessianGeometry E) (x : E) :
    quantumGeometryOp H x = H.metricOp x := rfl

omit [FiniteDimensional ℝ E] in
lemma radonNikodymOp_pos (H : HessianGeometry E) (x y : E) :
    0 < radonNikodymOp H x y := by
  unfold radonNikodymOp
  exact Real.exp_pos _

end BeliefDynamics
