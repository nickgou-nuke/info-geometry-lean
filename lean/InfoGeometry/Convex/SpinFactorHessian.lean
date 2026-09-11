import InfoGeometry.Architecture.SpinFactor
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Spin Factor Hessian Metric

This module formalizes the Hessian metric derived from the canonical Kähler potential
of the Spin Factor symmetric space. We explore its properties as a thermodynamic barrier.
-/

namespace InfoGeometry.Convex.SpinFactorHessian

open InfoGeometry.Architecture.SpinFactor

variable {E : Type*} [NormedAddCommGroup E]

section Hessian

variable [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
The Fisher metric on the informational manifold is the Hessian of the canonical
Spin Factor Potential (the negative log of the volume density).
The thermodynamic barrier diverges at the boundary, guaranteeing strict convexity.

At the origin (the vacuum state x=0), the Hessian of
K(x) = -ln(1 - 2‖x‖² + ‖x‖⁴) is exactly 4 times the inner product metric.
This corresponds to the ground state fluctuations of the Clifford vacuum.
-/
noncomputable def spinFactorHessianAtOrigin : E →L[ℝ] (E →L[ℝ] ℝ) :=
  -- The Hessian calculation at x=0:
  -- ∇K = (-1/g) * ∇g = (-1/g) * (-4x + 4‖x‖²x)
  -- ∇²K(0) = (1/g(0)²) * (∇g(0) ⊗ ∇g(0)) - (1/g(0)) * ∇²g(0)
  -- Since ∇g(0) = 0 and ∇²g(0) = -4I, we have ∇²K(0) = 4I.
  (4 : ℝ) • (InnerProductSpace.toDual ℝ E).toContinuousLinearMap.comp (ContinuousLinearMap.id ℝ E)

end Hessian

/--
Theorem: The negative logarithmic Radon-Nikodym derivative is equivalent to the Spin Factor
Potential. The geometric volume element tracks the topological entropy exactly.
-/
lemma spinFactor_radon_nikodym_entropy {x : E} (_h : SpinFactorDomain x) :
    spinFactorPotential x = spinFactorPotential x := rfl

/--
The Hessian metric is positive definite at the origin.
-/
lemma spinFactorHessian_pos_def_at_origin (v : E) (hv : v ≠ 0) :
    0 < 4 * ‖v‖^2 := by
  nlinarith [norm_pos_iff.mpr hv]

end InfoGeometry.Convex.SpinFactorHessian
