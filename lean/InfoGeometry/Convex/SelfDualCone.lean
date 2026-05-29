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
open scoped RealInnerProductSpace

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A proper cone equal to its inner dual (Hilbert-space self-duality). -/
structure SelfDualCone (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  cone : ProperCone ℝ E
  self_dual : ProperCone.innerDual (cone : Set E) = cone

@[simp] lemma SelfDualCone.innerDual_eq (C : SelfDualCone E) :
    ProperCone.innerDual (C.cone : Set E) = C.cone := C.self_dual

/--
Membership in a self-dual cone is exactly nonnegative inner pairing against
every element of the cone.
-/
theorem SelfDualCone.mem_iff_forall_inner_nonneg
    (C : SelfDualCone E) (x : E) :
    x ∈ C.cone ↔ ∀ y : E, y ∈ C.cone → 0 ≤ inner ℝ y x := by
  constructor
  · intro hx
    have hxDual : x ∈ ProperCone.innerDual (C.cone : Set E) := by
      rw [C.self_dual]
      exact hx
    exact (ProperCone.mem_innerDual (s := (C.cone : Set E)) (y := x)).mp hxDual
  · intro hx
    have hxDual : x ∈ ProperCone.innerDual (C.cone : Set E) :=
      (ProperCone.mem_innerDual (s := (C.cone : Set E)) (y := x)).mpr hx
    rw [C.self_dual] at hxDual
    exact hxDual

/--
Any two elements of a self-dual cone have nonnegative inner pairing.
-/
theorem SelfDualCone.inner_nonneg_of_mem
    (C : SelfDualCone E) {x y : E}
    (hx : x ∈ C.cone) (hy : y ∈ C.cone) :
    0 ≤ inner ℝ x y := by
  exact (C.mem_iff_forall_inner_nonneg y).mp hy x hx

/--
The self-dual cone is contained in its inner dual, read as a pointwise theorem.
-/
theorem SelfDualCone.mem_innerDual_of_mem
    (C : SelfDualCone E) {x : E}
    (hx : x ∈ C.cone) :
    x ∈ ProperCone.innerDual (C.cone : Set E) := by
  rw [C.self_dual]
  exact hx

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

/--
Membership in the paired dual cone is exactly nonnegative pairing against every
source-cone element.
-/
theorem PairedSelfDualCone.mem_coneF_iff_forall_pairing_nonneg
    (C : PairedSelfDualCone (E := E) (F := F)) (y : F) :
    y ∈ C.coneF ↔ ∀ x : E, x ∈ C.coneE → 0 ≤ C.pairing x y := by
  rw [← C.dual_eq]
  simp

/--
Elements of paired self-dual cones pair nonnegatively.
-/
theorem PairedSelfDualCone.pairing_nonneg_of_mem
    (C : PairedSelfDualCone (E := E) (F := F))
    {x : E} {y : F}
    (hx : x ∈ C.coneE) (hy : y ∈ C.coneF) :
    0 ≤ C.pairing x y := by
  exact (C.mem_coneF_iff_forall_pairing_nonneg y).mp hy x hx

end Pairing

end InfoGeometry.Convex
