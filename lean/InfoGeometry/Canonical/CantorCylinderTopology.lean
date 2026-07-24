import Mathlib
import InfoGeometry.Canonical.PiCylinderMathlib
import InfoGeometry.Canonical.StoneCantorMathlib

/-!
# Cantor cylinder topology

PR-shaped specialization of `PiCylinderMathlib` to the Cantor stream carrier
`ℕ → Bool` used by the UHF/Stone boundary files.

The module boundary is intentionally narrow and domain-free:

* finite coordinate cylinders in the product topology on `ℕ → Bool`;
* finite-prefix cylinders as the standard initial-segment cylinders;
* neighborhood-basis and singleton-intersection theorems;
* compatibility with the existing `BitWord`/`boundaryPrefix` notation.

No coarse geometry, homeomorphism-group classification, probability extension,
or physics interpretation is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorCylinderTopology

open Set Filter TopologicalSpace
open scoped Topology
open InfoGeometry.Canonical.PiCylinderMathlib
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.StoneCantorMathlib

/-- Domain-free name for the Cantor stream carrier. -/
abbrev CantorStream := ℕ → Bool

/-- Finite-coordinate cylinder in Cantor stream space. -/
def finiteCoordinateCylinder (x : CantorStream) (s : Set ℕ) : Set CantorStream :=
  canonicalCylinder x s

@[simp] theorem mem_finiteCoordinateCylinder
    (x y : CantorStream) (s : Set ℕ) :
    y ∈ finiteCoordinateCylinder x s ↔ ∀ i ∈ s, y i = x i :=
  Iff.rfl

/-- The finite-coordinate cylinders form a neighborhood basis at a Cantor stream. -/
theorem nhds_hasBasis_finiteCoordinateCylinder (x : CantorStream) :
    (𝓝 x).HasBasis Set.Finite (finiteCoordinateCylinder x) :=
  nhds_hasBasis_canonicalCylinder x

/-- Every finite-coordinate cylinder through `x` is a neighborhood of `x`. -/
theorem finiteCoordinateCylinder_mem_nhds
    (x : CantorStream) {s : Set ℕ} (hs : s.Finite) :
    finiteCoordinateCylinder x s ∈ 𝓝 x :=
  canonicalCylinder_mem_nhds x hs

/-- Agreement on all finite-coordinate cylinders through `x` isolates `x`. -/
theorem iInter_finset_finiteCoordinateCylinder (x : CantorStream) :
    (⋂ s : Finset ℕ, finiteCoordinateCylinder x (s : Set ℕ)) = {x} :=
  iInter_finset_canonicalCylinder x

/-- Initial segment as a finite set of natural coordinates. -/
def initialSegmentSet (n : ℕ) : Set ℕ :=
  {i | i < n}

/-- The initial segment set is finite. -/
theorem initialSegmentSet_finite (n : ℕ) : (initialSegmentSet n).Finite := by
  simpa [initialSegmentSet] using (Set.finite_lt_nat n)

/-- Initial-segment cylinder through a Cantor stream. -/
def initialSegmentCylinder (x : CantorStream) (n : ℕ) : Set CantorStream :=
  finiteCoordinateCylinder x (initialSegmentSet n)

/-- Initial-segment cylinders are neighborhoods of their base point. -/
theorem initialSegmentCylinder_mem_nhds (x : CantorStream) (n : ℕ) :
    initialSegmentCylinder x n ∈ 𝓝 x :=
  finiteCoordinateCylinder_mem_nhds x (initialSegmentSet_finite n)

@[simp] theorem mem_initialSegmentCylinder
    (x y : CantorStream) (n : ℕ) :
    y ∈ initialSegmentCylinder x n ↔ ∀ i, i < n → y i = x i := by
  rfl

/-- The initial-segment cylinders through `x` have singleton intersection. -/
theorem iInter_initialSegmentCylinder (x : CantorStream) :
    (⋂ n : ℕ, initialSegmentCylinder x n) = {x} := by
  ext y
  simp only [mem_iInter, mem_initialSegmentCylinder, mem_singleton_iff]
  constructor
  · intro h
    ext i
    exact h (i + 1) i (Nat.lt_succ_self i)
  · intro hy n i hi
    rw [hy]

/-- Initial-segment cylinder equals the existing `BitWord` prefix cylinder. -/
theorem initialSegmentCylinder_eq_prefixCylinder (x : CantorStream) (n : ℕ) :
    initialSegmentCylinder x n = prefixCylinder n (boundaryPrefix n x) := by
  ext y
  constructor
  · intro hy
    ext i
    exact hy i.1 i.2
  · intro hy i hi
    exact congrFun hy ⟨i, hi⟩

/-- The existing prefix-cylinder successor theorem, exposed under the topology module. -/
theorem initialSegmentCylinder_successor_union (x : CantorStream) (n : ℕ) :
    initialSegmentCylinder x n =
      prefixCylinder (n + 1) (extendSucc n (boundaryPrefix n x) false) ∪
        prefixCylinder (n + 1) (extendSucc n (boundaryPrefix n x) true) := by
  rw [initialSegmentCylinder_eq_prefixCylinder]
  exact prefixCylinder_successor_union n (boundaryPrefix n x)

/-- Principal ultrafilter evaluation of initial-segment cylinders is exact membership. -/
theorem principalUltrafilter_initialSegmentCylinder_eval
    (x y : CantorStream) (n : ℕ) :
    initialSegmentCylinder x n ∈ (pure y : Ultrafilter CantorStream) ↔
      ∀ i, i < n → y i = x i := by
  simp [initialSegmentCylinder, finiteCoordinateCylinder, canonicalCylinder, initialSegmentSet]

/-- Principal ultrafilter evaluation of all initial-segment cylinders isolates the point. -/
theorem principalUltrafilter_all_initialSegmentCylinder_iff
    (x y : CantorStream) :
    (∀ n : ℕ, initialSegmentCylinder x n ∈ (pure y : Ultrafilter CantorStream)) ↔ y = x := by
  constructor
  · intro h
    have hy : y ∈ ⋂ n : ℕ, initialSegmentCylinder x n := by
      simp only [mem_iInter]
      intro n
      exact (principalUltrafilter_initialSegmentCylinder_eval x y n).1 (h n)
    simpa [iInter_initialSegmentCylinder] using hy
  · intro hy n
    rw [hy]
    simp [initialSegmentCylinder, finiteCoordinateCylinder, canonicalCylinder, initialSegmentSet]

end InfoGeometry.Canonical.CantorCylinderTopology
