import InfoGeometry.Topology.NaryTreeBoundaryInverseLimit

/-!
# Prefix cylinders over compact Hausdorff alphabets

For an arbitrary compact Hausdorff alphabet, finite-prefix cylinders are
closed and compact.  Openness is intentionally not asserted: it requires the
stronger discrete-alphabet hypothesis owned by `NaryTreeBoundaryCylinderTopology`.
-/

noncomputable section

namespace InfoGeometry.Topology.NaryTreeBoundaryCompactHausdorffCylinder

open Set TopologicalSpace
open InfoGeometry.Topology.NaryTreeBoundaryInverseLimit

variable {A : Type} [TopologicalSpace A] [CompactSpace A] [T2Space A]

def compactBoundaryPrefix (n : ℕ) (x : Boundary (A := A)) :
    Word (A := A) n :=
  fun i => x i.1

def compactPrefixCylinder (n : ℕ) (w : Word (A := A) n) :
    Set (Boundary (A := A)) :=
  {x | compactBoundaryPrefix (A := A) n x = w}

theorem compactPrefixCylinder_eq_coordinate_iInter
    (n : ℕ) (w : Word (A := A) n) :
    compactPrefixCylinder (A := A) n w =
      ⋂ i : Fin n, (fun x : Boundary (A := A) => x i.1) ⁻¹'
        ({w i} : Set A) := by
  ext x
  simp only [compactPrefixCylinder, mem_setOf_eq, mem_iInter,
    mem_preimage, mem_singleton_iff]
  constructor
  · intro h i
    exact congrFun h i
  · intro h
    funext i
    exact h i

theorem isClosed_compactPrefixCylinder
    (n : ℕ) (w : Word (A := A) n) :
    IsClosed (compactPrefixCylinder (A := A) n w) := by
  rw [compactPrefixCylinder_eq_coordinate_iInter]
  apply isClosed_iInter
  intro i
  exact IsClosed.preimage (continuous_apply i.1) (isClosed_singleton)

theorem isCompact_compactPrefixCylinder
    (n : ℕ) (w : Word (A := A) n) :
    IsCompact (compactPrefixCylinder (A := A) n w) := by
  exact IsCompact.of_isClosed_subset isCompact_univ
    (isClosed_compactPrefixCylinder n w) (by intro x; simp)

theorem isClosed_compactPrefixCylinder_inter
    {n m : ℕ} (w : Word (A := A) n) (v : Word (A := A) m) :
    IsClosed (compactPrefixCylinder (A := A) n w ∩
      compactPrefixCylinder (A := A) m v) := by
  exact (isClosed_compactPrefixCylinder n w).inter
    (isClosed_compactPrefixCylinder m v)

end InfoGeometry.Topology.NaryTreeBoundaryCompactHausdorffCylinder
