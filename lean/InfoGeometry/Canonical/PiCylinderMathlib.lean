import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Product cylinders for `ι → Bool`

Mathlib-style product-topology cylinder facts for the discrete two-point space.
This file is intentionally domain-free: no physical interpretation, no custom
probability structure, and no project-specific colimit data.

#### BUCKET 1: CLOSED FINITE THEOREMS
* Set-finite coordinate cylinders in `ι → Bool`.
* Finset-indexed coordinate cylinders in `ι → Bool`.
* Mathlib's product-neighborhood cylinder basis via `nhds_pi` and
  `Filter.hasBasis_pi_pure`.
* Principal-filter membership in a cylinder is exactly coordinate agreement.
* Intersecting all finite-coordinate cylinders through a point isolates that
  point.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
None.  This file proves only the local product-topology basis facts.
-/

noncomputable section

namespace InfoGeometry.Canonical.PiCylinderMathlib

open Set Filter TopologicalSpace
open scoped Topology

variable {ι : Type*}

/-- The canonical finite-coordinate cylinder through `f`, indexed by a set of coordinates. -/
def canonicalCylinder (f : ι → Bool) (s : Set ι) : Set (ι → Bool) :=
  {g | ∀ i ∈ s, g i = f i}

@[simp] theorem mem_canonicalCylinder (f g : ι → Bool) (s : Set ι) :
    g ∈ canonicalCylinder f s ↔ ∀ i ∈ s, g i = f i :=
  Iff.rfl

/-- The canonical finite-coordinate cylinder through `f`, indexed by a `Finset`. -/
def finsetCanonicalCylinder (f : ι → Bool) (s : Finset ι) : Set (ι → Bool) :=
  {g | ∀ i ∈ s, g i = f i}

@[simp] theorem mem_finsetCanonicalCylinder (f g : ι → Bool) (s : Finset ι) :
    g ∈ finsetCanonicalCylinder f s ↔ ∀ i ∈ s, g i = f i :=
  Iff.rfl

/-- Principal-filter evaluation of a product cylinder is coordinate agreement. -/
theorem pure_mem_canonicalCylinder_iff (f g : ι → Bool) (s : Set ι) :
    canonicalCylinder f s ∈ (pure g : Filter (ι → Bool)) ↔
      ∀ i ∈ s, g i = f i := by
  simp [canonicalCylinder]

/-- Principal-filter evaluation of a Finset-indexed product cylinder is coordinate agreement. -/
theorem pure_mem_finsetCanonicalCylinder_iff (f g : ι → Bool) (s : Finset ι) :
    finsetCanonicalCylinder f s ∈ (pure g : Filter (ι → Bool)) ↔
      ∀ i ∈ s, g i = f i := by
  simp [finsetCanonicalCylinder]

/-- Product-topology neighborhoods of `f : ι → Bool` have the finite-coordinate cylinder basis. -/
theorem nhds_hasBasis_canonicalCylinder (f : ι → Bool) :
    (𝓝 f).HasBasis Set.Finite (canonicalCylinder f) := by
  rw [nhds_pi]
  simpa [nhds_discrete Bool] using Filter.hasBasis_pi_pure f

/-- Finset-indexed form of the same product-topology cylinder basis. -/
theorem nhds_hasBasis_finsetCanonicalCylinder (f : ι → Bool) :
    (𝓝 f).HasBasis (fun _ : Finset ι => True) (finsetCanonicalCylinder f) := by
  refine (nhds_hasBasis_canonicalCylinder f).to_hasBasis ?_ ?_
  · intro s hs
    refine ⟨hs.toFinset, trivial, ?_⟩
    intro g hg i hi
    exact hg i ((Set.Finite.mem_toFinset hs).2 hi)
  · intro s _
    refine ⟨(s : Set ι), Finset.finite_toSet s, ?_⟩
    intro g hg i hi
    exact hg i hi

/-- Finite-set cylinders are neighborhoods of their base point. -/
theorem canonicalCylinder_mem_nhds (f : ι → Bool) {s : Set ι} (hs : s.Finite) :
    canonicalCylinder f s ∈ 𝓝 f :=
  (nhds_hasBasis_canonicalCylinder f).mem_of_mem hs

/-- Finset-indexed cylinders are neighborhoods of their base point. -/
theorem finsetCanonicalCylinder_mem_nhds (f : ι → Bool) (s : Finset ι) :
    finsetCanonicalCylinder f s ∈ 𝓝 f :=
  (nhds_hasBasis_finsetCanonicalCylinder f).mem_of_mem trivial

/-- Intersecting all finite-coordinate cylinders through `f` isolates `f`. -/
theorem iInter_finset_canonicalCylinder (f : ι → Bool) :
    (⋂ s : Finset ι, canonicalCylinder f (s : Set ι)) = {f} := by
  ext g
  simp only [mem_iInter, mem_canonicalCylinder, mem_singleton_iff]
  constructor
  · intro h
    ext i
    exact h {i} i (by simp)
  · intro h s i hi
    rw [h]

/-- A point belongs to all finite-coordinate cylinders through `f` iff it is `f`. -/
theorem mem_all_finset_cylinders_iff (f g : ι → Bool) :
    (∀ s : Finset ι, g ∈ canonicalCylinder f (s : Set ι)) ↔ g = f := by
  simpa [Set.ext_iff] using congrArg (fun S : Set (ι → Bool) => g ∈ S)
    (iInter_finset_canonicalCylinder (ι := ι) f)

/-- A point belongs to all Finset-indexed coordinate cylinders through `f` iff it is `f`. -/
theorem mem_all_finsetCanonical_cylinders_iff (f g : ι → Bool) :
    (∀ s : Finset ι, g ∈ finsetCanonicalCylinder f s) ↔ g = f := by
  simpa [finsetCanonicalCylinder, canonicalCylinder] using
    (mem_all_finset_cylinders_iff (ι := ι) f g)

/-- Closed packet for the canonical Boolean product-cylinder topology. -/
theorem pi_bool_product_cylinder_topology_packet :
    (∀ f : ι → Bool, (𝓝 f).HasBasis Set.Finite (canonicalCylinder f)) ∧
      (∀ f : ι → Bool,
        (𝓝 f).HasBasis (fun _ : Finset ι => True) (finsetCanonicalCylinder f)) ∧
      (∀ (f g : ι → Bool) (s : Set ι),
        canonicalCylinder f s ∈ (pure g : Filter (ι → Bool)) ↔
          ∀ i ∈ s, g i = f i) ∧
      (∀ (f g : ι → Bool), (∀ s : Finset ι, g ∈ finsetCanonicalCylinder f s) ↔ g = f) := by
  exact ⟨nhds_hasBasis_canonicalCylinder,
    nhds_hasBasis_finsetCanonicalCylinder,
    pure_mem_canonicalCylinder_iff,
    mem_all_finsetCanonical_cylinders_iff⟩

end InfoGeometry.Canonical.PiCylinderMathlib
