import InfoGeometry.Topology.SymbolicLatentBoundaryReadoutInverseLimitCompHaus
import InfoGeometry.Topology.SymbolicLatentBoundaryCylinderColimitTopCat
import InfoGeometry.Topology.NaryTreeBoundaryCylinderTopology

/-!
# Finite-prefix cylinders on the compact prefix inverse limit

The prefix-limit cylinder is transported from the native sequence-space
cylinder through the canonical boundary/inverse-limit isomorphism.  This
keeps the inverse-limit object as the owner and records its compatibility
with the compact symbolic-latent readout.
-/

noncomputable section

namespace InfoGeometry.Topology.SymbolicLatentBoundaryPrefixLimitCylinderCompHaus

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Topology.NaryTreeBoundaryCylinderTopology
open InfoGeometry.Topology.NaryTreeBoundaryInverseLimit
open InfoGeometry.Topology.SymbolicLatentBoundaryAddress
open InfoGeometry.Topology.SymbolicLatentBoundaryCylinderColimit
open InfoGeometry.Topology.SymbolicLatentBoundaryReadoutInverseLimit

variable {ι A : Type} [Fintype ι] [TopologicalSpace A]
variable {D : SymbolicLatentSequence ι}

def prefixLimitCylinder
    (length : ℕ) (w : Word (A := A) length) :
    Set ((limit (prefixDiagram (A := A)) : TopCat) : Type) :=
  (prefixBoundaryLimitIso (A := A)).inv.hom ⁻¹'
    prefixCylinder (A := A) length w

theorem isClopen_prefixLimitCylinder
    [Fintype A] [DiscreteTopology A]
    (length : ℕ) (w : Word (A := A) length) :
    IsClopen (prefixLimitCylinder (A := A) length w) := by
  exact ⟨
    IsClosed.preimage (prefixBoundaryLimitIso (A := A)).inv.hom.continuous
      (isClosed_prefixCylinder length w),
    (isOpen_prefixCylinder length w).preimage
      (prefixBoundaryLimitIso (A := A)).inv.hom.continuous⟩

theorem iUnion_prefixLimitCylinder_eq_univ
    [Fintype A] [DiscreteTopology A]
    (length : ℕ) :
    (⋃ w : Word (A := A) length,
      prefixLimitCylinder (A := A) length w) = Set.univ := by
  ext x
  constructor
  · intro
    trivial
  · intro
    exact Set.mem_iUnion.2 ⟨
      boundaryPrefix (A := A) length
        ((prefixBoundaryLimitIso (A := A)).inv.hom x),
      rfl⟩

theorem prefixLimitCylinder_disjoint_of_ne
    [Fintype A] [DiscreteTopology A]
    (length : ℕ)
    {w v : Word (A := A) length}
    (hwv : w ≠ v) :
    Disjoint (prefixLimitCylinder (A := A) length w)
      (prefixLimitCylinder (A := A) length v) := by
  rw [Set.disjoint_left]
  intro x hx hy
  apply hwv
  exact ((show boundaryPrefix (A := A) length
      ((prefixBoundaryLimitIso (A := A)).inv.hom x) = w from hx).symm.trans hy)

theorem boundaryReadoutToPrefixLimitCompHausHom_preimage_prefixLimitCylinder
    (S : SymbolicLatentBoundaryAddress.System A D)
    [CompactSpace A] [T2Space A]
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)]
    (length : ℕ) (w : Word (A := A) length) :
  (compHausToTop.map
      (boundaryReadoutToPrefixLimitCompHausHom D S)).hom ⁻¹'
        prefixLimitCylinder (A := A) length w =
      colimitBoundaryCylinder S length w := by
  rw [boundaryReadoutToPrefixLimitCompHausHom_forget]
  ext x
  change
    (prefixBoundaryLimitIso (A := A)).inv.hom
        ((boundaryReadoutToPrefixLimit D S).hom x) ∈
          prefixCylinder (A := A) length w ↔
      (boundaryReadout D S).hom x ∈
        prefixCylinder (A := A) length w
  change
    (prefixBoundaryLimitIso (A := A)).inv.hom
        ((prefixBoundaryLimitIso (A := A)).hom
          ((boundaryReadout D S).hom x)) ∈
          prefixCylinder (A := A) length w ↔
      (boundaryReadout D S).hom x ∈
        prefixCylinder (A := A) length w
  have hIso := congrArg
    (fun f => f.hom ((boundaryReadout D S).hom x))
    (prefixBoundaryLimitIso (A := A)).hom_inv_id
  have hIso' :
      (prefixBoundaryLimitIso (A := A)).inv.hom
          ((prefixBoundaryLimitIso (A := A)).hom
            ((boundaryReadout D S).hom x)) =
        (boundaryReadout D S).hom x := by
    simpa using hIso
  rw [hIso']

theorem boundaryReadoutToPrefixLimitCompHausHom_preimage_prefixLimitCylinder_iUnion_eq_univ
    (S : SymbolicLatentBoundaryAddress.System A D)
    [Fintype A] [DiscreteTopology A]
    [CompactSpace A] [T2Space A]
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)]
    (length : ℕ) :
    (⋃ w : Word (A := A) length,
      (compHausToTop.map
        (boundaryReadoutToPrefixLimitCompHausHom D S)).hom ⁻¹'
          prefixLimitCylinder (A := A) length w) = Set.univ := by
  simp only [boundaryReadoutToPrefixLimitCompHausHom_preimage_prefixLimitCylinder
    (D := D) S]
  exact iUnion_colimitBoundaryCylinder_eq_univ S length

theorem boundaryReadoutToPrefixLimitCompHausHom_preimage_prefixLimitCylinder_disjoint_of_ne
    (S : SymbolicLatentBoundaryAddress.System A D)
    [Fintype A] [DiscreteTopology A]
    [CompactSpace A] [T2Space A]
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)]
    (length : ℕ)
    {w v : Word (A := A) length}
    (hwv : w ≠ v) :
    Disjoint
      ((compHausToTop.map
        (boundaryReadoutToPrefixLimitCompHausHom D S)).hom ⁻¹'
          prefixLimitCylinder (A := A) length w)
      ((compHausToTop.map
        (boundaryReadoutToPrefixLimitCompHausHom D S)).hom ⁻¹'
          prefixLimitCylinder (A := A) length v) := by
  rw [boundaryReadoutToPrefixLimitCompHausHom_preimage_prefixLimitCylinder
      (D := D) S length w,
    boundaryReadoutToPrefixLimitCompHausHom_preimage_prefixLimitCylinder
      (D := D) S length v]
  exact colimitBoundaryCylinder_disjoint_of_ne S length hwv

end InfoGeometry.Topology.SymbolicLatentBoundaryPrefixLimitCylinderCompHaus
