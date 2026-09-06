import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Symbolic-latent boundary cylinder as a `TopCat` pushout

The pushout carrier and its universal property are supplied directly by
Mathlib's `PushoutCocone` and `IsColimit` APIs.  This file adds only the
domain-specific readout lemmas; it does not package a second colimit datum.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory CategoryTheory.Limits

namespace SymbolicLatentBoundaryCylinderPushoutData

variable {SymbolicBoundary ContinuousBulk BoundaryCylinder : TopCat}
variable {cylinderToBoundary : BoundaryCylinder ⟶ SymbolicBoundary}
variable {cylinderToBulk : BoundaryCylinder ⟶ ContinuousBulk}
variable (cocone : PushoutCocone cylinderToBoundary cylinderToBulk)
variable (hc : IsColimit cocone)

theorem latent_holographic_commutation :
    cylinderToBoundary ≫ cocone.inl = cylinderToBulk ≫ cocone.inr := by
  simpa using cocone.condition

noncomputable def descend
    (Y : TopCat)
    (boundaryToY : SymbolicBoundary ⟶ Y)
    (bulkToY : ContinuousBulk ⟶ Y)
    (h : cylinderToBoundary ≫ boundaryToY = cylinderToBulk ≫ bulkToY) :
    cocone.pt ⟶ Y :=
  PushoutCocone.IsColimit.desc hc boundaryToY bulkToY h

theorem descend_inl
    (Y : TopCat)
    (boundaryToY : SymbolicBoundary ⟶ Y)
    (bulkToY : ContinuousBulk ⟶ Y)
    (h : cylinderToBoundary ≫ boundaryToY = cylinderToBulk ≫ bulkToY) :
    cocone.inl ≫ descend cocone hc Y boundaryToY bulkToY h = boundaryToY := by
  simpa [descend] using
    PushoutCocone.IsColimit.inl_desc hc boundaryToY bulkToY h

theorem descend_inr
    (Y : TopCat)
    (boundaryToY : SymbolicBoundary ⟶ Y)
    (bulkToY : ContinuousBulk ⟶ Y)
    (h : cylinderToBoundary ≫ boundaryToY = cylinderToBulk ≫ bulkToY) :
    cocone.inr ≫ descend cocone hc Y boundaryToY bulkToY h = bulkToY := by
  simpa [descend] using
    PushoutCocone.IsColimit.inr_desc hc boundaryToY bulkToY h

theorem descend_unique
    (Y : TopCat)
    (boundaryToY : SymbolicBoundary ⟶ Y)
    (bulkToY : ContinuousBulk ⟶ Y)
    (h : cylinderToBoundary ≫ boundaryToY = cylinderToBulk ≫ bulkToY)
    (m : cocone.pt ⟶ Y)
    (hm_inl : cocone.inl ≫ m = boundaryToY)
    (hm_inr : cocone.inr ≫ m = bulkToY) :
    m = descend cocone hc Y boundaryToY bulkToY h := by
  apply PushoutCocone.IsColimit.hom_ext hc
  · rw [hm_inl, descend_inl cocone hc Y boundaryToY bulkToY h]
  · rw [hm_inr, descend_inr cocone hc Y boundaryToY bulkToY h]

theorem descend_postcomp
    (Y Z : TopCat)
    (boundaryToY : SymbolicBoundary ⟶ Y)
    (bulkToY : ContinuousBulk ⟶ Y)
    (h : cylinderToBoundary ≫ boundaryToY = cylinderToBulk ≫ bulkToY)
    (f : Y ⟶ Z)
    (hpost : cylinderToBoundary ≫ (boundaryToY ≫ f) =
      cylinderToBulk ≫ (bulkToY ≫ f)) :
    descend cocone hc Z (boundaryToY ≫ f) (bulkToY ≫ f) hpost =
      descend cocone hc Y boundaryToY bulkToY h ≫ f := by
  symm
  apply descend_unique cocone hc Z (boundaryToY ≫ f) (bulkToY ≫ f) hpost
    (descend cocone hc Y boundaryToY bulkToY h ≫ f)
  · simpa only [Category.assoc] using
      congrArg (fun q => q ≫ f) (descend_inl cocone hc Y boundaryToY bulkToY h)
  · simpa only [Category.assoc] using
      congrArg (fun q => q ≫ f) (descend_inr cocone hc Y boundaryToY bulkToY h)

end SymbolicLatentBoundaryCylinderPushoutData

end InfoGeometry.Topology
