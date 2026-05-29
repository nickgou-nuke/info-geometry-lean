import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Algebra.Module.PerfectPairing

/-!
# Self-dual cones and projective ray spaces

Scaffolding for the cone-first, projective-state approach:
* `SelfDualCone`: a proper cone equal to its inner dual in a real Hilbert space.
* `PairedSelfDualCone`: self-duality packaged via a perfect pairing.
* `ConeRay` / `ConeInteriorRay`: projectivized cone points and interior rays.
-/

namespace InfoGeometry.Convex

open scoped LinearAlgebra.Projectivization

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A proper cone equal to its inner dual (Hilbert-space self-duality). -/
structure SelfDualCone (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  cone : ProperCone ℝ E
  self_dual : ProperCone.innerDual (cone : Set E) = cone

@[simp] lemma SelfDualCone.innerDual_eq (C : SelfDualCone E) :
    ProperCone.innerDual (C.cone : Set E) = C.cone := C.self_dual

/-- Projective rays represented by nonzero cone points. -/
def ConeRay (C : ProperCone ℝ E) : Type _ :=
  {ℓ : ℙ ℝ E // ∃ v : E, ∃ hv : v ≠ 0, v ∈ (C : Set E) ∧ Projectivization.mk ℝ v hv = ℓ}

/-- Projective rays represented by nonzero interior cone points. -/
def ConeInteriorRay (C : ProperCone ℝ E) : Type _ :=
  {ℓ : ℙ ℝ E // ∃ v : E, ∃ hv : v ≠ 0, v ∈ interior (C : Set E) ∧
    Projectivization.mk ℝ v hv = ℓ}

end Inner

section Pairing

variable {E F : Type*}
variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- Self-duality packaged via a perfect pairing. -/
structure PairedSelfDualCone where
  pairing : E →ₗ[ℝ] F →ₗ[ℝ] ℝ
  is_perf : pairing.IsContPerfPair
  coneE : ProperCone ℝ E
  coneF : ProperCone ℝ F
  dual_eq : ProperCone.dual pairing coneE = coneF

instance (C : PairedSelfDualCone (E := E) (F := F)) : C.pairing.IsContPerfPair := C.is_perf

end Pairing

end InfoGeometry.Convex
