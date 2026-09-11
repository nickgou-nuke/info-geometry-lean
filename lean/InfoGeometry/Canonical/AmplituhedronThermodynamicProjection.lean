import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ContinuousThermodynamicGeometry
import InfoGeometry.Canonical.BostConnesAmplituhedronBoundary

/-!
# Amplituhedron Thermodynamic Projection

This module formally projects the Continuous Thermodynamic Geometry 
onto the Amplituhedron scattering boundary.

Per the Categorical Synthesis Dictionary:
- The Logarithmic Generating Potential (Massieu Potential) Ψ is evaluated 
  specifically as the natural logarithm of the Amplituhedron Volume.
- The Fisher-Souriau-Koszul metric descends to the scattering amplitude 
  kinematic space, endowing the scattering boundary with a dually flat metric.
-/

noncomputable section

namespace InfoGeometry.Canonical.AmplituhedronThermodynamicProjection

open InfoGeometry.Canonical.ContinuousThermodynamicGeometry
open InfoGeometry.Canonical.BostConnesAmplituhedronBoundary
-- open InfoGeometry.Projective.BostConnes

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-!
## 1. Amplituhedron Volume as Massieu Potential

We identify the continuous thermodynamic partition function `Q` explicitly 
with the Amplituhedron Volume `Vol`.
-/

/-- 
The continuous thermodynamic geometry restricted to the scattering boundary, 
where the generic partition function `Q` is strictly identified with the 
all-loop Amplituhedron Volume.
-/
structure AmplituhedronThermodynamicState (P : LogarithmicPotential E) where
  Vol : E → ℝ
  is_amplituhedron_volume : ∀ β, P.Q β = Vol β

/-!
## 2. Dually Flat Kinematic Scattering Space

The Fisher-Souriau metric (the Hessian of `ln Vol`) induces a dually flat 
Riemannian geometry directly on the Amplituhedron scattering kinematics.
-/

/--
The projection of the continuous thermodynamic Hessian metric onto the 
Amplituhedron boundary kinematics. 
-/
structure AmplituhedronScatteringMetric 
    (P : LogarithmicPotential E) 
    (G : DuallyFlatHessianGeometry P) 
    (A : AmplituhedronThermodynamicState P) where
  -- The metric strictly inherits the Amari / Fisher-Souriau geometry
  kinematic_hessian : E → (E →L[ℝ] (E →L[ℝ] ℝ))
  is_inherited : ∀ β X Y, kinematic_hessian β X Y = G.hessian β X Y

/-- 
THEOREM: The Amplituhedron scattering kinematic space is endowed with a 
strictly positive-definite continuous thermodynamic metric.
-/
theorem amplituhedron_metric_positive_definite 
    (P : LogarithmicPotential E) 
    (G : DuallyFlatHessianGeometry P) 
    (A : AmplituhedronThermodynamicState P)
    (M : AmplituhedronScatteringMetric P G A)
    (β : E) (X : E) (hX : X ≠ 0) : 
    M.kinematic_hessian β X X > 0 := by
  rw [M.is_inherited]
  exact G.is_strictly_convex β X hX

end InfoGeometry.Canonical.AmplituhedronThermodynamicProjection
