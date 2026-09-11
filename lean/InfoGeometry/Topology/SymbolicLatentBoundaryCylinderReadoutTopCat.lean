import InfoGeometry.Topology.SymbolicLatentBoundaryAddressTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.NaryTreeBoundaryCylinderTopology

/-!
# Cylinder readouts on symbolic-latent stages

An address family from the varying-carrier symbolic-latent system pulls finite
boundary cylinders back to topological loci on every stage.  Compatibility of
the addresses is recorded as equality of these loci under the stage maps.
This is a local topological bridge; it does not identify a carrier colimit
with the inverse-limit boundary.
-/

noncomputable section

namespace InfoGeometry.Topology.SymbolicLatentBoundaryCylinderReadout

open Set Filter TopologicalSpace
open CategoryTheory
open InfoGeometry.Topology.NaryTreeBoundaryCylinderTopology
open InfoGeometry.Topology.NaryTreeBoundaryInverseLimit
open InfoGeometry.Topology.SymbolicLatentBoundaryAddress

variable {ι : Type} {A : Type}
  [Fintype ι] [TopologicalSpace A] [Fintype A] [DiscreteTopology A]
variable {D : SymbolicLatentSequence ι}

def stageBoundaryCylinder
    (S : System A D) (stage length : ℕ) (w : Word (A := A) length) :
    Set (D.obj stage).carrier :=
  (S.address stage) ⁻¹' prefixCylinder (A := A) length w

theorem isOpen_stageBoundaryCylinder
    (S : System A D) (stage length : ℕ) (w : Word (A := A) length) :
    IsOpen (stageBoundaryCylinder S stage length w) := by
  exact (isOpen_prefixCylinder length w).preimage
    (S.continuous_address stage)

theorem isClosed_stageBoundaryCylinder
    (S : System A D) (stage length : ℕ) (w : Word (A := A) length) :
    IsClosed (stageBoundaryCylinder S stage length w) := by
  exact IsClosed.preimage (S.continuous_address stage)
    (isClosed_prefixCylinder length w)

theorem stageBoundaryCylinder_preimage_compat
    (S : System A D) {n m : ℕ} (h : n ≤ m)
    (length : ℕ) (w : Word (A := A) length) :
    (D.diagram.map (homOfLE h)).toFun ⁻¹'
        stageBoundaryCylinder S m length w =
      stageBoundaryCylinder S n length w := by
  ext x
  change S.address m ((D.diagram.map (homOfLE h)).toFun x) ∈
      prefixCylinder (A := A) length w ↔
    S.address n x ∈ prefixCylinder (A := A) length w
  rw [S.compatible h x]

theorem stageBoundaryCylinder_mem_nhds
    (S : System A D) (n : ℕ) (x : (D.obj n).carrier) :
    stageBoundaryCylinder S n n
        (boundaryPrefix (A := A) n (S.address n x)) ∈ nhds x := by
  apply (isOpen_stageBoundaryCylinder S n n
    (boundaryPrefix (A := A) n (S.address n x))).mem_nhds
  rfl

end InfoGeometry.Topology.SymbolicLatentBoundaryCylinderReadout
