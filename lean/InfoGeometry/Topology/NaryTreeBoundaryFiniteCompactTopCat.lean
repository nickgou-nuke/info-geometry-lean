import InfoGeometry.Topology.NaryTreeBoundaryCylinderTopology
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Compact finite-alphabet boundary spaces

For a finite discrete alphabet, the product boundary `ℕ → A` inherits native
Mathlib compactness and Hausdorff separation.  Together with the cylinder
owner, this gives compact clopen finite-prefix pieces without introducing a
metric completion or an interval identification.
-/

noncomputable section

namespace InfoGeometry.Topology.NaryTreeBoundaryFiniteCompactTopCat

open Set
open InfoGeometry.Topology.NaryTreeBoundaryInverseLimit
open InfoGeometry.Topology.NaryTreeBoundaryCylinderTopology

variable {A : Type} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]

instance boundaryCompactSpace :
    CompactSpace (Boundary (A := A)) := by
  infer_instance

instance boundaryT2Space :
    T2Space (Boundary (A := A)) := by
  infer_instance

theorem isCompact_boundary :
    IsCompact (Set.univ : Set (Boundary (A := A))) :=
  isCompact_univ

theorem isCompact_prefixCylinder
    (n : ℕ) (w : Word (A := A) n) :
    IsCompact (prefixCylinder (A := A) n w) := by
  exact IsCompact.of_isClosed_subset isCompact_boundary
    (isClosed_prefixCylinder n w) (by intro x; simp)

end InfoGeometry.Topology.NaryTreeBoundaryFiniteCompactTopCat
