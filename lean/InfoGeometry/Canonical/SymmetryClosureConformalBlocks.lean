import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.SymmetryClosureConformalBlocks

Symmetry-closure interface for finite conformal-block style sectors.

This file deliberately treats the relevant structure as internal symmetry
closure, not as complex analytic continuation.  The finite theorem-owned content
is:

* sectors are linear subspaces of a larger carrier;
* generators preserve the computational and non-computational sectors;
* commutators and anticommutators of sector-preserving generators are again
  sector-preserving;
* direct-sum/block actions preserve their summands;
* no leakage means exactly preservation of the computational sector and its
  complement sector.

No analytic continuation.
No conformal-block function theory.
No hidden construction of physical Hilbert spaces.
-/

namespace SymmetryClosureConformalBlocks

/-- Commutator of two linear symmetry generators. -/
def commutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  A.comp B - B.comp A

/-- Anticommutator of two linear symmetry generators. -/
def anticommutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  A.comp B + B.comp A

/-- A subspace is invariant under a linear symmetry generator. -/
def InvariantSubspace {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : Submodule ℂ V) (A : V →ₗ[ℂ] V) : Prop :=
  ∀ v : V, v ∈ W → A v ∈ W

/-- A sector split into computational and non-computational linear subspaces. -/
structure SectorDecomposition (V : Type*) [AddCommGroup V] [Module ℂ V] where
  /-- Computational sector. -/
  computational : Submodule ℂ V
  /-- Non-computational/complement sector. -/
  noncomputational : Submodule ℂ V

namespace SectorDecomposition

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A generator preserves both sectors of a sector decomposition. -/
def PreservesSectors (D : SectorDecomposition V) (A : V →ₗ[ℂ] V) : Prop :=
  InvariantSubspace D.computational A ∧ InvariantSubspace D.noncomputational A

/-- No leakage is sector preservation of the computational sector. -/
def NoLeakage (D : SectorDecomposition V) (A : V →ₗ[ℂ] V) : Prop :=
  InvariantSubspace D.computational A

/-- Sector preservation implies no leakage. -/
theorem noLeakage_of_preservesSectors {D : SectorDecomposition V} {A : V →ₗ[ℂ] V}
    (hA : D.PreservesSectors A) :
    D.NoLeakage A :=
  hA.1

/-- The identity generator preserves every sector split. -/
theorem preservesSectors_id (D : SectorDecomposition V) :
    D.PreservesSectors LinearMap.id := by
  constructor <;> intro v hv <;> simpa using hv

/-- Composition of sector-preserving generators is sector-preserving. -/
theorem preservesSectors_comp {D : SectorDecomposition V} {A B : V →ₗ[ℂ] V}
    (hA : D.PreservesSectors A) (hB : D.PreservesSectors B) :
    D.PreservesSectors (A.comp B) := by
  constructor
  · intro v hv
    exact hA.1 (B v) (hB.1 v hv)
  · intro v hv
    exact hA.2 (B v) (hB.2 v hv)

/-- Sums of sector-preserving generators are sector-preserving. -/
theorem preservesSectors_add {D : SectorDecomposition V} {A B : V →ₗ[ℂ] V}
    (hA : D.PreservesSectors A) (hB : D.PreservesSectors B) :
    D.PreservesSectors (A + B) := by
  constructor
  · intro v hv
    exact D.computational.add_mem (hA.1 v hv) (hB.1 v hv)
  · intro v hv
    exact D.noncomputational.add_mem (hA.2 v hv) (hB.2 v hv)

/-- Negatives of sector-preserving generators are sector-preserving. -/
theorem preservesSectors_neg {D : SectorDecomposition V} {A : V →ₗ[ℂ] V}
    (hA : D.PreservesSectors A) :
    D.PreservesSectors (-A) := by
  constructor
  · intro v hv
    exact D.computational.neg_mem (hA.1 v hv)
  · intro v hv
    exact D.noncomputational.neg_mem (hA.2 v hv)

/-- Differences of sector-preserving generators are sector-preserving. -/
theorem preservesSectors_sub {D : SectorDecomposition V} {A B : V →ₗ[ℂ] V}
    (hA : D.PreservesSectors A) (hB : D.PreservesSectors B) :
    D.PreservesSectors (A - B) := by
  simpa [sub_eq_add_neg] using preservesSectors_add hA (preservesSectors_neg hB)

/-- Commutator closure of the internal symmetry algebra. -/
theorem preservesSectors_commutator {D : SectorDecomposition V} {A B : V →ₗ[ℂ] V}
    (hA : D.PreservesSectors A) (hB : D.PreservesSectors B) :
    D.PreservesSectors (commutator A B) := by
  unfold commutator
  exact preservesSectors_sub (preservesSectors_comp hA hB) (preservesSectors_comp hB hA)

/-- Anticommutator closure of the internal symmetry algebra. -/
theorem preservesSectors_anticommutator {D : SectorDecomposition V} {A B : V →ₗ[ℂ] V}
    (hA : D.PreservesSectors A) (hB : D.PreservesSectors B) :
    D.PreservesSectors (anticommutator A B) := by
  unfold anticommutator
  exact preservesSectors_add (preservesSectors_comp hA hB) (preservesSectors_comp hB hA)

end SectorDecomposition

/-- Direct-sum/block action on a product carrier. -/
def blockAction {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W) : V × W →ₗ[ℂ] V × W where
  toFun x := (A x.1, B x.2)
  map_add' x y := by simp
  map_smul' c x := by simp

/-- Left summand in a product carrier. -/
def leftSector (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : Submodule ℂ (V × W) where
  carrier := {x | x.2 = 0}
  zero_mem' := rfl
  add_mem' hx hy := by
    change _ + _ = 0
    rw [hx, hy]
    simp
  smul_mem' c x hx := by
    change c • x.2 = 0
    rw [hx]
    simp

/-- Right summand in a product carrier. -/
def rightSector (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : Submodule ℂ (V × W) where
  carrier := {x | x.1 = 0}
  zero_mem' := rfl
  add_mem' hx hy := by
    change _ + _ = 0
    rw [hx, hy]
    simp
  smul_mem' c x hx := by
    change c • x.1 = 0
    rw [hx]
    simp

/-- A block action preserves the left summand. -/
theorem blockAction_preserves_left {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W) :
    InvariantSubspace (leftSector V W) (blockAction A B) := by
  intro x hx
  change B x.2 = 0
  rw [hx]
  simp

/-- A block action preserves the right summand. -/
theorem blockAction_preserves_right {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W) :
    InvariantSubspace (rightSector V W) (blockAction A B) := by
  intro x hx
  change A x.1 = 0
  rw [hx]
  simp

/-- Product sector decomposition used by recursive block constructions. -/
def productSectorDecomposition (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : SectorDecomposition (V × W) where
  computational := leftSector V W
  noncomputational := rightSector V W

/-- Block actions preserve the product sector decomposition. -/
theorem blockAction_preserves_productSectors {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W) :
    (productSectorDecomposition V W).PreservesSectors (blockAction A B) :=
  ⟨blockAction_preserves_left A B, blockAction_preserves_right A B⟩

/-- Recursive block actions have no leakage from the left/computational summand. -/
theorem blockAction_noLeakage {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W) :
    (productSectorDecomposition V W).NoLeakage (blockAction A B) :=
  SectorDecomposition.noLeakage_of_preservesSectors (blockAction_preserves_productSectors A B)

end SymmetryClosureConformalBlocks
