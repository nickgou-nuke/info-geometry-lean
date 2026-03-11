import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.PerfectPairing

/-!
# Self-Dual Proper Cones and Projective State Spaces

This module defines the self-dual proper cone structure, which provides the canonical
foundation for information geometry. 

Rather than working with a normalized simplex of probabilities, we treat unnormalized 
strictly positive states as rays in the interior of a self-dual cone C. The boundary ∂C 
smoothly incorporates degenerate and pure states. Self-duality identifies the state space
with the observable space.
-/

noncomputable section

namespace InfoGeometry.Projective

open scoped Projectivization

/-- 
A proper positive cone that equals its own inner dual.
This is the canonical setting for the Jordan/Krein observable algebra layer. 
-/
structure SelfDualCone (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] where
  cone : ProperCone ℝ E
  self_dual : ProperCone.innerDual (cone : Set E) = cone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
The regular state space consists of projective rays through the interior of the positive cone.
Using `Projectivization` quotients out the scaling gauge (normalization).
-/
def ConeInteriorStateSpace (C : ProperCone ℝ E) :=
  { ℓ : Projectivization ℝ E // ∃ (v : E) (hv : v ≠ 0), v ∈ interior (C : Set E) ∧ Projectivization.mk ℝ v hv = ℓ }

/--
The boundary state space includes degenerate, null, and pure directions, represented as 
rays through the full positive cone.
-/
def ConeBoundaryRaySpace (C : ProperCone ℝ E) :=
  { ℓ : Projectivization ℝ E // ∃ (v : E) (hv : v ≠ 0), v ∈ (C : Set E) ∧ Projectivization.mk ℝ v hv = ℓ }

end InfoGeometry.Projective
