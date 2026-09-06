import InfoGeometry.Topology.SymbolicLatentBoundaryCylinderQuotientCompHausIso
import InfoGeometry.Topology.SymbolicLatentBoundaryCylinderColimitTopCat
import InfoGeometry.Topology.SymbolicLatentBoundaryCylinderNeighborhoodTopCat

/-!
# Finite-prefix cylinders under the compact boundary readout

This owner identifies the cylinder preimages seen through the compact
`CompHaus` readout with the native colimit cylinders.  Their clopen cover and
disjointness are then the existing topological facts about those subsets.
-/

noncomputable section

namespace InfoGeometry.Topology.SymbolicLatentBoundaryCylinderQuotientCompHaus

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Topology.NaryTreeBoundaryInverseLimit
open InfoGeometry.Topology.NaryTreeBoundaryCylinderTopology
open InfoGeometry.Topology.SymbolicLatentBoundaryAddress
open InfoGeometry.Topology.SymbolicLatentBoundaryCylinderColimit
open InfoGeometry.Topology.SymbolicLatentBoundaryCylinderReadout
open InfoGeometry.Topology.SymbolicLatentBoundaryCylinderQuotientTopCat

variable {ι : Type} {A : Type}
  [Fintype ι] [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [T2Space A]
variable {D : SymbolicLatentSequence ι}

theorem boundaryReadoutCompHausHom_preimage_prefixCylinder
    (S : System A D)
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)]
    (length : ℕ)
    (w : Word (A := A) length) :
    (compHausToTop.map (boundaryReadoutCompHausHom S)).hom ⁻¹'
        prefixCylinder (A := A) length w =
      colimitBoundaryCylinder S length w := by
  rw [boundaryReadoutCompHausHom_forget S]
  rfl

theorem boundaryReadoutCompHausHom_preimage_prefixCylinder_isClopen
    (S : System A D)
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)]
    (length : ℕ)
    (w : Word (A := A) length) :
    IsClopen
      ((compHausToTop.map (boundaryReadoutCompHausHom S)).hom ⁻¹'
        prefixCylinder (A := A) length w) := by
  rw [boundaryReadoutCompHausHom_preimage_prefixCylinder S length w]
  exact isClopen_colimitBoundaryCylinder S length w

theorem boundaryReadoutCompHausHom_preimage_prefixCylinder_iUnion_eq_univ
    (S : System A D)
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)]
    (length : ℕ) :
    (⋃ w : Word (A := A) length,
      (compHausToTop.map (boundaryReadoutCompHausHom S)).hom ⁻¹'
        prefixCylinder (A := A) length w) = Set.univ := by
  simp only [boundaryReadoutCompHausHom_preimage_prefixCylinder S]
  exact iUnion_colimitBoundaryCylinder_eq_univ S length

theorem boundaryReadoutCompHausHom_preimage_prefixCylinder_disjoint_of_ne
    (S : System A D)
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)]
    (length : ℕ)
    {w v : Word (A := A) length}
    (hwv : w ≠ v) :
    Disjoint
      ((compHausToTop.map (boundaryReadoutCompHausHom S)).hom ⁻¹'
        prefixCylinder (A := A) length w)
      ((compHausToTop.map (boundaryReadoutCompHausHom S)).hom ⁻¹'
        prefixCylinder (A := A) length v) := by
  rw [boundaryReadoutCompHausHom_preimage_prefixCylinder S length w,
    boundaryReadoutCompHausHom_preimage_prefixCylinder S length v]
  exact colimitBoundaryCylinder_disjoint_of_ne S length hwv

theorem boundaryReadoutCompHausHom_preimage_prefixCylinder_stage
    (S : System A D)
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)]
    (stage length : ℕ)
    (w : Word (A := A) length) :
    (colimit.ι (carrierDiagram D) stage).hom ⁻¹'
        ((compHausToTop.map (boundaryReadoutCompHausHom S)).hom ⁻¹'
          prefixCylinder (A := A) length w) =
      stageBoundaryCylinder S stage length w := by
  rw [boundaryReadoutCompHausHom_preimage_prefixCylinder S length w]
  exact SymbolicLatentBoundaryCylinderNeighborhood.colimitBoundaryCylinder_preimage_stage
    S stage length w

end InfoGeometry.Topology.SymbolicLatentBoundaryCylinderQuotientCompHaus

end
