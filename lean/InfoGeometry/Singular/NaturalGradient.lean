import InfoGeometry.Singular.CartanWiring
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Singular.MoorePenrose
import InfoGeometry.Convex.HessianGeometry
import Mathlib.Tactic

/-!
# Natural Gradient and Moore-Penrose Wiring

This module connects the "Cartan Wiring" (geometric adjoints) to the 
"Natural Gradient" in Information Geometry.

## The Theory
In Information Geometry, the steepest descent direction on a manifold 
with metric $G$ is given by the natural gradient:
$$\tilde{\nabla} f = G^{-1} \nabla f$$
When the metric $G$ is singular (e.g., on the boundary of the model space),
we use the Moore-Penrose generalized inverse:
$$\tilde{\nabla} f = G^{+} \nabla f$$

We show here that this $G^{+}$ is precisely the Moore-Penrose inverse 
in the native `StarRing` adjoint framework.
-/

open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Clifford.Decomposition
open InfoGeometry.Clifford.TowerMatrix
open Matrix

namespace InfoGeometry.Singular.NaturalGradient

variable {n : ℕ} (J1 : Matrix (Fin 2) (Fin 2) ℝ)
variable (hJ1_sq : J1 * J1 = 1)
variable (hJ1t : J1ᵀ = J1)

/-- 
Definition of the Natural Gradient using the Geometric Moore-Penrose inverse.
Given a primal gradient `grad_f` and a (possibly singular) metric `G`,
the natural gradient is the MP-inverse of `G` applied to `grad_f`.
-/
def naturalGradient (grad_f : Mat n) (G_pinv : Mat n) : Mat n :=
  G_pinv * grad_f

/--
The "Information Symmetry" Theorem:
If the metric G is self-adjoint relative to the wired geometry (i.e., G† = G),
then the Natural Gradient is consistent with the metric's own symmetries.
-/
theorem natural_gradient_symmetry (G G_pinv : Mat n)
    (h : IsMoorePenroseInverse G G_pinv) :
    (G * G_pinv)† = G * G_pinv := h.eq3

end InfoGeometry.Singular.NaturalGradient
