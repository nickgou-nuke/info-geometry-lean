import InfoGeometry.Canonical.PiCylinderMathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CantorCylinderTopology

/-!
# PR-shaped Cantor product-cylinder boundary

This is the extraction boundary for the mathlib-facing product-topology facts.
It factors the former scratch surface into two owner modules:

* `PiCylinderMathlib`: general finite-coordinate cylinders in `ι → Bool`;
* `CantorCylinderTopology`: the `ℕ → Bool` specialization and initial-segment
  cylinders.

This file does not define a new topology, measure, Stone-duality theorem,
coarse-geometry theorem, or homeomorphism-group classification.  It is only a
narrow re-export surface for canonical cylinder facts that are small enough to
review independently.

#### BUCKET 1: CLOSED FINITE THEOREMS
* General product-cylinder neighborhood basis for `ι → Bool`.
* General principal-filter cylinder membership as coordinate agreement.
* Cantor-stream finite-coordinate neighborhood basis.
* Cantor-stream initial-segment cylinder neighborhoods and singleton
  intersection.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
None.  The file intentionally avoids global Stone duality, measure extension,
and coarse/homeomorphism-group classification claims.
-/

noncomputable section

namespace InfoGeometry.Canonical.StoneCantorMathlibPR

open Set Filter TopologicalSpace
open scoped Topology

namespace Pi

variable {ι : Type*}

/-- PR-facing name for the canonical finite-coordinate cylinder in `ι → Bool`. -/
abbrev cylinder (f : ι → Bool) (s : Set ι) : Set (ι → Bool) :=
  InfoGeometry.Canonical.PiCylinderMathlib.canonicalCylinder f s

@[simp] theorem mem_cylinder (f g : ι → Bool) (s : Set ι) :
    g ∈ cylinder f s ↔ ∀ i ∈ s, g i = f i :=
  Iff.rfl

/-- Product-topology neighborhoods on `ι → Bool` have the finite-coordinate cylinder basis. -/
theorem nhds_hasBasis_cylinder (f : ι → Bool) :
    (𝓝 f).HasBasis Set.Finite (cylinder f) :=
  InfoGeometry.Canonical.PiCylinderMathlib.nhds_hasBasis_canonicalCylinder f

/-- Principal-filter evaluation of a product cylinder is coordinate agreement. -/
theorem pure_mem_cylinder_iff (f g : ι → Bool) (s : Set ι) :
    cylinder f s ∈ (pure g : Filter (ι → Bool)) ↔ ∀ i ∈ s, g i = f i :=
  InfoGeometry.Canonical.PiCylinderMathlib.pure_mem_canonicalCylinder_iff f g s

/-- Intersecting all finite-coordinate cylinders through `f` isolates `f`. -/
theorem iInter_finset_cylinder (f : ι → Bool) :
    (⋂ s : Finset ι, cylinder f (s : Set ι)) = {f} :=
  InfoGeometry.Canonical.PiCylinderMathlib.iInter_finset_canonicalCylinder f

end Pi

namespace Cantor

/-- PR-facing carrier for Cantor streams. -/
abbrev Stream := InfoGeometry.Canonical.CantorCylinderTopology.CantorStream

/-- PR-facing finite-coordinate cylinder on `ℕ → Bool`. -/
abbrev finiteCoordinateCylinder (x : Stream) (s : Set ℕ) : Set Stream :=
  InfoGeometry.Canonical.CantorCylinderTopology.finiteCoordinateCylinder x s

/-- PR-facing initial-segment cylinder on `ℕ → Bool`. -/
abbrev initialSegmentCylinder (x : Stream) (n : ℕ) : Set Stream :=
  InfoGeometry.Canonical.CantorCylinderTopology.initialSegmentCylinder x n

@[simp] theorem mem_finiteCoordinateCylinder (x y : Stream) (s : Set ℕ) :
    y ∈ finiteCoordinateCylinder x s ↔ ∀ i ∈ s, y i = x i :=
  Iff.rfl

@[simp] theorem mem_initialSegmentCylinder (x y : Stream) (n : ℕ) :
    y ∈ initialSegmentCylinder x n ↔ ∀ i, i < n → y i = x i :=
  InfoGeometry.Canonical.CantorCylinderTopology.mem_initialSegmentCylinder x y n

/-- Cantor-stream neighborhoods have the finite-coordinate cylinder basis. -/
theorem nhds_hasBasis_finiteCoordinateCylinder (x : Stream) :
    (𝓝 x).HasBasis Set.Finite (finiteCoordinateCylinder x) :=
  InfoGeometry.Canonical.CantorCylinderTopology.nhds_hasBasis_finiteCoordinateCylinder x

/-- Initial-segment cylinders are neighborhoods of their base point. -/
theorem initialSegmentCylinder_mem_nhds (x : Stream) (n : ℕ) :
    initialSegmentCylinder x n ∈ 𝓝 x :=
  InfoGeometry.Canonical.CantorCylinderTopology.initialSegmentCylinder_mem_nhds x n

/-- The initial-segment cylinders through `x` have singleton intersection. -/
theorem iInter_initialSegmentCylinder (x : Stream) :
    (⋂ n : ℕ, initialSegmentCylinder x n) = {x} :=
  InfoGeometry.Canonical.CantorCylinderTopology.iInter_initialSegmentCylinder x

/-- Principal ultrafilter evaluation of initial-segment cylinders is exact membership. -/
theorem principalUltrafilter_initialSegmentCylinder_eval
    (x y : Stream) (n : ℕ) :
    initialSegmentCylinder x n ∈ (pure y : Ultrafilter Stream) ↔
      ∀ i, i < n → y i = x i :=
  InfoGeometry.Canonical.CantorCylinderTopology.principalUltrafilter_initialSegmentCylinder_eval
    x y n

/-- Principal ultrafilter evaluation of all initial-segment cylinders isolates the point. -/
theorem principalUltrafilter_all_initialSegmentCylinder_iff
    (x y : Stream) :
    (∀ n : ℕ, initialSegmentCylinder x n ∈ (pure y : Ultrafilter Stream)) ↔ y = x :=
  InfoGeometry.Canonical.CantorCylinderTopology.principalUltrafilter_all_initialSegmentCylinder_iff
    x y

end Cantor

end InfoGeometry.Canonical.StoneCantorMathlibPR
