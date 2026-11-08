import InfoGeometry.Topology.NaryTreeBoundaryCompactHausdorffCylinderSeparation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentBoundaryCompactTopCat

/-!
# Compact-Hausdorff cylinders on the native prefix limit

These cylinders use the general compact-Hausdorff boundary cylinder rather
than the finite-discrete cylinder owner.  The canonical boundary/limit
homeomorphism transports closedness and compactness to the categorical limit.
-/

noncomputable section

namespace InfoGeometry.Topology.SymbolicLatentCompactHausdorffPrefixLimitCylinder

open Set CategoryTheory CategoryTheory.Limits
open InfoGeometry.Topology.NaryTreeBoundaryInverseLimit
open InfoGeometry.Topology.NaryTreeBoundaryCompactHausdorffCylinder

variable {A : Type} [TopologicalSpace A] [CompactSpace A] [T2Space A]

def compactHausdorffPrefixLimitCylinder
    (length : ℕ) (w : Word (A := A) length) :
    Set ((limit (prefixDiagram (A := A)) : TopCat) : Type) :=
  (prefixBoundaryLimitIso (A := A)).inv.hom ⁻¹'
    compactPrefixCylinder (A := A) length w

theorem isClosed_compactHausdorffPrefixLimitCylinder
    (length : ℕ) (w : Word (A := A) length) :
    IsClosed (compactHausdorffPrefixLimitCylinder (A := A) length w) := by
  exact IsClosed.preimage (prefixBoundaryLimitIso (A := A)).inv.hom.continuous
    (isClosed_compactPrefixCylinder length w)

theorem isCompact_compactHausdorffPrefixLimitCylinder
    (length : ℕ) (w : Word (A := A) length) :
    IsCompact (compactHausdorffPrefixLimitCylinder (A := A) length w) := by
  exact IsCompact.of_isClosed_subset isCompact_univ
    (isClosed_compactHausdorffPrefixLimitCylinder length w)
    (by intro x; simp)

theorem compactHausdorffPrefixLimitCylinder_inter_closed
    {n m : ℕ} (w : Word (A := A) n) (v : Word (A := A) m) :
    IsClosed
      (compactHausdorffPrefixLimitCylinder (A := A) n w ∩
        compactHausdorffPrefixLimitCylinder (A := A) m v) := by
  exact (isClosed_compactHausdorffPrefixLimitCylinder n w).inter
    (isClosed_compactHausdorffPrefixLimitCylinder m v)

theorem mem_compactHausdorffPrefixLimitCylinder_iff
    (length : ℕ) (w : Word (A := A) length)
    (x : (limit (prefixDiagram (A := A)) : TopCat)) :
    x ∈ compactHausdorffPrefixLimitCylinder (A := A) length w ↔
      (prefixBoundaryLimitIso (A := A)).inv.hom x ∈
        compactPrefixCylinder (A := A) length w := by
  rfl

theorem disjoint_compactHausdorffPrefixLimitCylinder_of_ne
    {n : ℕ} {w v : Word (A := A) n} (hwv : w ≠ v) :
    Disjoint (compactHausdorffPrefixLimitCylinder (A := A) n w)
      (compactHausdorffPrefixLimitCylinder (A := A) n v) := by
  rw [Set.disjoint_left]
  intro x hx hy
  exact Set.disjoint_left.1 (disjoint_compactPrefixCylinder_of_ne hwv)
    ((mem_compactHausdorffPrefixLimitCylinder_iff n w x).mp hx)
    ((mem_compactHausdorffPrefixLimitCylinder_iff n v x).mp hy)

theorem iUnion_compactHausdorffPrefixLimitCylinder_eq_univ (n : ℕ) :
    (⋃ w : Word (A := A) n,
      compactHausdorffPrefixLimitCylinder (A := A) n w) = Set.univ := by
  apply Set.eq_univ_iff_forall.2
  intro x
  let y := (prefixBoundaryLimitIso (A := A)).inv.hom x
  have hy : y ∈ (⋃ w : Word (A := A) n,
      compactPrefixCylinder (A := A) n w) := by
    rw [iUnion_compactPrefixCylinder_eq_univ]
    exact Set.mem_univ y
  obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hy
  refine Set.mem_iUnion.2 ⟨w, ?_⟩
  exact hw

end InfoGeometry.Topology.SymbolicLatentCompactHausdorffPrefixLimitCylinder
