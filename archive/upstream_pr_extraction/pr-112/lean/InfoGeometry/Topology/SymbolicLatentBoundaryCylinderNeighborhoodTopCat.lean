import InfoGeometry.Topology.SymbolicLatentBoundaryCylinderColimitTopCat

/-!
# Cylinder neighborhoods on the symbolic-latent carrier colimit

The colimit readout already transports finite-prefix cylinders and proves that
they are clopen.  This bridge records the local topological consequence that
the cylinder determined by the address of a point is a genuine neighborhood
of that point.  No injectivity, compactness, or quotient assertion is used.
-/

noncomputable section

namespace InfoGeometry.Topology.SymbolicLatentBoundaryCylinderNeighborhood

open Set Filter TopologicalSpace
open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Topology.NaryTreeBoundaryCylinderTopology
open InfoGeometry.Topology.NaryTreeBoundaryInverseLimit
open InfoGeometry.Topology.SymbolicLatentBoundaryAddress
open InfoGeometry.Topology.SymbolicLatentBoundaryCylinderColimit
open InfoGeometry.Topology.SymbolicLatentBoundaryCylinderReadout

variable {ι : Type} {A : Type}
  [Fintype ι] [TopologicalSpace A] [Fintype A] [DiscreteTopology A]
variable {D : SymbolicLatentSequence ι}

theorem colimitBoundaryCylinder_mem_nhds
    (S : System A D) (length : ℕ)
    (x : (carrierColimit D : TopCat)) :
    colimitBoundaryCylinder S length
        (boundaryPrefix (A := A) length ((boundaryReadout D S).hom x)) ∈ nhds x := by
  apply (boundaryReadout D S).hom.continuous.continuousAt.preimage_mem_nhds
  exact prefixCylinder_mem_nhds length ((boundaryReadout D S).hom x)

theorem colimitBoundaryCylinder_preimage_stage
    (S : System A D) (stage length : ℕ)
    (w : Word (A := A) length) :
    (colimit.ι (carrierDiagram D) stage).hom ⁻¹'
        colimitBoundaryCylinder S length w =
      stageBoundaryCylinder S stage length w := by
  ext x
  change ((boundaryReadout D S).hom
      ((colimit.ι (carrierDiagram D) stage).hom x) ∈
        prefixCylinder (A := A) length w) ↔
      S.address stage x ∈ prefixCylinder (A := A) length w
  have hstage := congrArg
    (fun f => f.hom.toFun) (boundaryReadout_stage D S stage)
  have hx := congrFun hstage x
  simpa using Iff.of_eq
    (congrArg (fun y => y ∈ prefixCylinder (A := A) length w) hx)

end InfoGeometry.Topology.SymbolicLatentBoundaryCylinderNeighborhood
