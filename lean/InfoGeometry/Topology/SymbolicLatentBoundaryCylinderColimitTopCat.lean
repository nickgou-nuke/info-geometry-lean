import InfoGeometry.Topology.SymbolicLatentBoundaryCylinderReadoutTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Cylinder covers transported through the symbolic-latent colimit readout

The compatible boundary address family gives a continuous readout from the
carrier colimit to the prefix boundary.  Pulling clopen finite-prefix
cylinders back along that readout produces a clopen cover on the colimit.
No claim is made that the readout is injective, surjective, or a homeomorphism.
-/

noncomputable section

namespace InfoGeometry.Topology.SymbolicLatentBoundaryCylinderColimit

open Set Filter TopologicalSpace
open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Topology.NaryTreeBoundaryCylinderTopology
open InfoGeometry.Topology.NaryTreeBoundaryInverseLimit
open InfoGeometry.Topology.SymbolicLatentBoundaryAddress
open InfoGeometry.Topology.SymbolicLatentBoundaryCylinderReadout

variable {ι : Type} {A : Type}
  [Fintype ι] [TopologicalSpace A] [Fintype A] [DiscreteTopology A]
variable {D : SymbolicLatentSequence ι}

noncomputable def carrierColimit (D : SymbolicLatentSequence ι) : TopCat :=
  colimit (carrierDiagram D)

def colimitBoundaryCylinder
    (S : System A D) (length : ℕ)
    (w : NaryTreeBoundaryInverseLimit.Word (A := A) length) :
    Set (carrierColimit D) :=
  (boundaryReadout D S).hom ⁻¹'
    prefixCylinder (A := A) length w

theorem isOpen_colimitBoundaryCylinder
    (S : System A D) (length : ℕ)
    (w : NaryTreeBoundaryInverseLimit.Word (A := A) length) :
    IsOpen (colimitBoundaryCylinder S length w) := by
  exact (isOpen_prefixCylinder length w).preimage
    (boundaryReadout D S).hom.continuous

theorem isClosed_colimitBoundaryCylinder
    (S : System A D) (length : ℕ)
    (w : NaryTreeBoundaryInverseLimit.Word (A := A) length) :
    IsClosed (colimitBoundaryCylinder S length w) := by
  exact IsClosed.preimage (boundaryReadout D S).hom.continuous
    (isClosed_prefixCylinder length w)

theorem isClopen_colimitBoundaryCylinder
    (S : System A D) (length : ℕ)
    (w : NaryTreeBoundaryInverseLimit.Word (A := A) length) :
    IsClopen (colimitBoundaryCylinder S length w) := by
  exact ⟨isClosed_colimitBoundaryCylinder S length w,
    isOpen_colimitBoundaryCylinder S length w⟩

theorem iUnion_colimitBoundaryCylinder_eq_univ
    (S : System A D) (length : ℕ) :
    (⋃ w : NaryTreeBoundaryInverseLimit.Word (A := A) length,
      colimitBoundaryCylinder S length w) = Set.univ := by
  ext x
  constructor
  · intro
    trivial
  · intro
    exact Set.mem_iUnion.2 ⟨
      boundaryPrefix (A := A) length ((boundaryReadout D S).hom x),
      rfl⟩

theorem colimitBoundaryCylinder_disjoint_of_ne
    (S : System A D) (length : ℕ)
    {w v : NaryTreeBoundaryInverseLimit.Word (A := A) length}
    (hwv : w ≠ v) :
    Disjoint (colimitBoundaryCylinder S length w)
      (colimitBoundaryCylinder S length v) := by
  rw [Set.disjoint_left]
  intro x hx hy
  exact hwv ((show boundaryPrefix (A := A) length
      ((boundaryReadout D S).hom x) = w from hx).symm.trans hy)

theorem stageBoundaryCylinder_iUnion_eq_univ
    (S : System A D) (stage length : ℕ) :
    (⋃ w : NaryTreeBoundaryInverseLimit.Word (A := A) length,
      stageBoundaryCylinder S stage length w) = Set.univ := by
  ext x
  constructor
  · intro
    trivial
  · intro
    exact Set.mem_iUnion.2 ⟨
      boundaryPrefix (A := A) length (S.address stage x),
      rfl⟩

theorem stageBoundaryCylinder_disjoint_of_ne
    (S : System A D) (stage length : ℕ)
    {w v : NaryTreeBoundaryInverseLimit.Word (A := A) length}
    (hwv : w ≠ v) :
    Disjoint (stageBoundaryCylinder S stage length w)
      (stageBoundaryCylinder S stage length v) := by
  rw [Set.disjoint_left]
  intro x hx hy
  exact hwv ((show boundaryPrefix (A := A) length
      (S.address stage x) = w from hx).symm.trans hy)

end InfoGeometry.Topology.SymbolicLatentBoundaryCylinderColimit
