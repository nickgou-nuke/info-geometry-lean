import InfoGeometry.Topology.SymbolicLatentBoundaryCylinderColimitTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentBoundaryCylinderPushoutTopCat
import InfoGeometry.Topology.SymbolicLatentBoundaryCylinderReadoutTopCat

/-!
# Symbolic-latent boundary-cylinder synthesis

This module is a thin theorem-honest hub for the existing boundary-cylinder
owners. It packages the local stage readout, the colimit readout, and the
pushout descent facts without introducing any new topological claims.
-/

noncomputable section

namespace InfoGeometry.Topology.SymbolicLatentBoundaryCylinderSynthesis

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Topology.NaryTreeBoundaryCylinderTopology
open InfoGeometry.Topology.NaryTreeBoundaryInverseLimit
open InfoGeometry.Topology.SymbolicLatentBoundaryAddress
open InfoGeometry.Topology.SymbolicLatentBoundaryCylinderReadout
open InfoGeometry.Topology.SymbolicLatentBoundaryCylinderColimit
open InfoGeometry.Topology.SymbolicLatentBoundaryCylinderPushoutData

variable {ι : Type} {A : Type}
  [Fintype ι] [TopologicalSpace A] [Fintype A] [DiscreteTopology A]
variable {D : SymbolicLatentSequence ι}

/-- Local and colimit boundary-cylinder regularity packaged as a single hub. -/
theorem boundary_cylinder_regular_synthesis
    (S : System A D)
    (stage length : ℕ)
    (w : Word (A := A) length) :
    IsOpen (stageBoundaryCylinder S stage length w) ∧
    IsClosed (stageBoundaryCylinder S stage length w) ∧
    IsClopen (colimitBoundaryCylinder S length w) := by
  refine ⟨?_, ?_, ?_⟩
  · exact isOpen_stageBoundaryCylinder S stage length w
  · exact isClosed_stageBoundaryCylinder S stage length w
  · exact isClopen_colimitBoundaryCylinder S length w

/-- The boundary-cylinder cover and separation data on the colimit side. -/
theorem boundary_cylinder_cover_synthesis
    (S : System A D)
    (length : ℕ) :
    (⋃ w : Word (A := A) length, colimitBoundaryCylinder S length w) = Set.univ ∧
    ∀ {w v : Word (A := A) length}, w ≠ v →
      Disjoint (colimitBoundaryCylinder S length w)
        (colimitBoundaryCylinder S length v) := by
  refine ⟨?_, ?_⟩
  · exact iUnion_colimitBoundaryCylinder_eq_univ S length
  · intro w v hwv
    exact colimitBoundaryCylinder_disjoint_of_ne S length hwv

/-- Pushout commutation and descent packaged as a single hub. -/
theorem boundary_cylinder_pushout_synthesis
    {SymbolicBoundary ContinuousBulk BoundaryCylinder : TopCat}
    {cylinderToBoundary : BoundaryCylinder ⟶ SymbolicBoundary}
    {cylinderToBulk : BoundaryCylinder ⟶ ContinuousBulk}
    (cocone : PushoutCocone cylinderToBoundary cylinderToBulk)
    (hc : IsColimit cocone)
    (Y : TopCat)
    (boundaryToY : SymbolicBoundary ⟶ Y)
    (bulkToY : ContinuousBulk ⟶ Y)
    (h : cylinderToBoundary ≫ boundaryToY = cylinderToBulk ≫ bulkToY) :
    ((cylinderToBoundary ≫ cocone.inl = cylinderToBulk ≫ cocone.inr) ∧
      (cocone.inl ≫ descend cocone hc Y boundaryToY bulkToY h = boundaryToY)) ∧
    (cocone.inr ≫ descend cocone hc Y boundaryToY bulkToY h = bulkToY) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact latent_holographic_commutation cocone
  · exact descend_inl cocone hc Y boundaryToY bulkToY h
  · exact descend_inr cocone hc Y boundaryToY bulkToY h

end InfoGeometry.Topology.SymbolicLatentBoundaryCylinderSynthesis
