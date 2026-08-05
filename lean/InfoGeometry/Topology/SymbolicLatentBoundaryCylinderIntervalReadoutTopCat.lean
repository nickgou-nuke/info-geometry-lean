import InfoGeometry.Topology.SymbolicLatentBoundaryCylinderPushoutTopCat
import Mathlib

/-!
# Interval-valued readout for the symbolic-latent boundary cylinder

The interval readout is expressed directly over a native pushout cocone and
its `IsColimit` witness.  No readout or pushout evidence packet is needed.
-/

noncomputable section

namespace InfoGeometry.Topology.SymbolicLatentBoundaryCylinderIntervalReadoutTopCat

open CategoryTheory CategoryTheory.Limits

abbrev UnitInterval := Set.Icc (0 : ℝ) 1

noncomputable def intervalReadout
    {SymbolicBoundary ContinuousBulk BoundaryCylinder : TopCat}
    {cylinderToBoundary : BoundaryCylinder ⟶ SymbolicBoundary}
    {cylinderToBulk : BoundaryCylinder ⟶ ContinuousBulk}
    (cocone : PushoutCocone cylinderToBoundary cylinderToBulk)
    (hc : IsColimit cocone)
    (boundaryToInterval : SymbolicBoundary ⟶ TopCat.of UnitInterval)
    (bulkToInterval : ContinuousBulk ⟶ TopCat.of UnitInterval)
    (compat : cylinderToBoundary ≫ boundaryToInterval =
      cylinderToBulk ≫ bulkToInterval) :
    cocone.pt ⟶ TopCat.of UnitInterval :=
  InfoGeometry.Topology.SymbolicLatentBoundaryCylinderPushoutData.descend
    cocone hc (TopCat.of UnitInterval) boundaryToInterval bulkToInterval compat

theorem intervalReadout_inl
    {SymbolicBoundary ContinuousBulk BoundaryCylinder : TopCat}
    {cylinderToBoundary : BoundaryCylinder ⟶ SymbolicBoundary}
    {cylinderToBulk : BoundaryCylinder ⟶ ContinuousBulk}
    (cocone : PushoutCocone cylinderToBoundary cylinderToBulk)
    (hc : IsColimit cocone)
    (boundaryToInterval : SymbolicBoundary ⟶ TopCat.of UnitInterval)
    (bulkToInterval : ContinuousBulk ⟶ TopCat.of UnitInterval)
    (compat : cylinderToBoundary ≫ boundaryToInterval =
      cylinderToBulk ≫ bulkToInterval) :
    cocone.inl ≫ intervalReadout cocone hc boundaryToInterval bulkToInterval compat =
      boundaryToInterval := by
  simpa [intervalReadout] using
    InfoGeometry.Topology.SymbolicLatentBoundaryCylinderPushoutData.descend_inl
      cocone hc (TopCat.of UnitInterval) boundaryToInterval bulkToInterval compat

theorem intervalReadout_inr
    {SymbolicBoundary ContinuousBulk BoundaryCylinder : TopCat}
    {cylinderToBoundary : BoundaryCylinder ⟶ SymbolicBoundary}
    {cylinderToBulk : BoundaryCylinder ⟶ ContinuousBulk}
    (cocone : PushoutCocone cylinderToBoundary cylinderToBulk)
    (hc : IsColimit cocone)
    (boundaryToInterval : SymbolicBoundary ⟶ TopCat.of UnitInterval)
    (bulkToInterval : ContinuousBulk ⟶ TopCat.of UnitInterval)
    (compat : cylinderToBoundary ≫ boundaryToInterval =
      cylinderToBulk ≫ bulkToInterval) :
    cocone.inr ≫ intervalReadout cocone hc boundaryToInterval bulkToInterval compat =
      bulkToInterval := by
  simpa [intervalReadout] using
    InfoGeometry.Topology.SymbolicLatentBoundaryCylinderPushoutData.descend_inr
      cocone hc (TopCat.of UnitInterval) boundaryToInterval bulkToInterval compat

theorem intervalReadout_unique
    {SymbolicBoundary ContinuousBulk BoundaryCylinder : TopCat}
    {cylinderToBoundary : BoundaryCylinder ⟶ SymbolicBoundary}
    {cylinderToBulk : BoundaryCylinder ⟶ ContinuousBulk}
    (cocone : PushoutCocone cylinderToBoundary cylinderToBulk)
    (hc : IsColimit cocone)
    (boundaryToInterval : SymbolicBoundary ⟶ TopCat.of UnitInterval)
    (bulkToInterval : ContinuousBulk ⟶ TopCat.of UnitInterval)
    (compat : cylinderToBoundary ≫ boundaryToInterval =
      cylinderToBulk ≫ bulkToInterval)
    (m : cocone.pt ⟶ TopCat.of UnitInterval)
    (hm_inl : cocone.inl ≫ m = boundaryToInterval)
    (hm_inr : cocone.inr ≫ m = bulkToInterval) :
    m = intervalReadout cocone hc boundaryToInterval bulkToInterval compat := by
  apply InfoGeometry.Topology.SymbolicLatentBoundaryCylinderPushoutData.descend_unique
    cocone hc (TopCat.of UnitInterval) boundaryToInterval bulkToInterval compat m
  · exact hm_inl
  · exact hm_inr

end InfoGeometry.Topology.SymbolicLatentBoundaryCylinderIntervalReadoutTopCat
