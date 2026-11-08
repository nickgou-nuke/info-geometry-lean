import Mathlib.Analysis.Convex.Cone.InnerDual
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Self-Dual Proper Cones and Projective State Spaces

Foundational definitions for proper cones in Hilbert spaces and their 
corresponding projective ray spaces.
-/

noncomputable section

namespace InfoGeometry.Projective

open scoped Projectivization

/-- A self-dual proper cone in a Hilbert space. -/
structure SelfDualCone (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] where
  cone : ProperCone ℝ E
  self_dual : ProperCone.innerDual (cone : Set E) = cone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The state space formed by rays in the interior of a proper cone. -/
def ConeInteriorStateSpace (C : ProperCone ℝ E) :=
  { ℓ : Projectivization ℝ E // ∃ (v : E) (hv : v ≠ 0),
      v ∈ interior (C : Set E) ∧ Projectivization.mk ℝ v hv = ℓ }

/-- The space of rays on the boundary or interior of a proper cone. -/
def ConeBoundaryRaySpace (C : ProperCone ℝ E) :=
  { ℓ : Projectivization ℝ E // ∃ (v : E) (hv : v ≠ 0),
      v ∈ (C : Set E) ∧ Projectivization.mk ℝ v hv = ℓ }

end InfoGeometry.Projective
