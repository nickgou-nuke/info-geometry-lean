import InfoGeometry.Topology.SymbolicLatentBoundaryReadoutInverseLimitTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentCompatiblePrefixFamily

/-!
# Prefix-cone packaging of a symbolic-latent boundary address

The varying-carrier address system already has a canonical readout into the
prefix inverse limit.  This owner packages that map as an explicit compatible
prefix cone, so that the universal property is visible at the cone level.
No new limit or quotient is introduced.
-/

noncomputable section

namespace InfoGeometry.Topology.SymbolicLatentBoundaryAddressPrefixCone

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Topology.SymbolicLatentBoundaryAddress
open InfoGeometry.Topology.SymbolicLatentBoundaryReadoutInverseLimit
open InfoGeometry.Topology.NaryTreeBoundaryInverseLimit

variable {ι : Type} {A : Type}
  [Fintype ι] [TopologicalSpace A]
variable {D : SymbolicLatentSequence ι}

noncomputable def boundaryAddressPrefixCone
    (D : SymbolicLatentSequence ι)
    (S : System A D) :
    Cone (prefixDiagram (A := A)) where
  pt := colimit (carrierDiagram D)
  π :=
    { app := fun n =>
        boundaryReadoutToPrefixLimit D S ≫
          limit.π (prefixDiagram (A := A)) n
      naturality := by
        intro X Y f
        change
          boundaryReadoutToPrefixLimit D S ≫
              limit.π (prefixDiagram (A := A)) Y =
            boundaryReadoutToPrefixLimit D S ≫
              (limit.π (prefixDiagram (A := A)) X ≫
                (prefixDiagram (A := A)).map f)
        rw [limit.w]
    }

theorem boundaryAddressPrefixCone_stage
    (D : SymbolicLatentSequence ι)
    (S : System A D) (n : ℕ) :
    (boundaryAddressPrefixCone D S).π.app (Opposite.op n) =
      boundaryReadoutToPrefixLimit D S ≫
        limit.π (prefixDiagram (A := A)) (Opposite.op n) := by
  rfl

theorem boundaryAddressPrefixCone_lift_eq_boundaryReadout
    (D : SymbolicLatentSequence ι)
    (S : System A D) :
    prefixLimitLift (boundaryAddressPrefixCone D S) =
      boundaryReadout D S := by
  apply (prefixConeIsLimit (A := A)).hom_ext
  intro j
  rcases j with ⟨n⟩
  calc
    prefixLimitLift (boundaryAddressPrefixCone D S) ≫
        prefixCone.π.app (Opposite.op n) =
      (boundaryAddressPrefixCone D S).π.app (Opposite.op n) :=
        (prefixConeIsLimit (A := A)).fac
          (boundaryAddressPrefixCone D S) (Opposite.op n)
    _ = boundaryReadout D S ≫ prefixCone.π.app (Opposite.op n) := by
      simp [boundaryAddressPrefixCone, boundaryReadoutToPrefixLimit,
        Category.assoc, prefixBoundaryLimitIso_hom_comp]

theorem boundaryAddressPrefixCone_to_limit_eq_readout
    (D : SymbolicLatentSequence ι)
    (S : System A D) :
    compatiblePrefixFamilyToLimit (boundaryAddressPrefixCone D S) =
      boundaryReadoutToPrefixLimit D S := by
  change
    prefixLimitLift (boundaryAddressPrefixCone D S) ≫
        prefixBoundaryLimitIso (A := A).hom =
      boundaryReadout D S ≫ prefixBoundaryLimitIso (A := A).hom
  rw [boundaryAddressPrefixCone_lift_eq_boundaryReadout]

theorem boundaryAddressPrefixCone_stage_apply
    (D : SymbolicLatentSequence ι)
    (S : System A D) (n : ℕ) (x : (D.obj n).carrier) (i : Fin n) :
    (limit.π (prefixDiagram (A := A)) (Opposite.op n)).hom
        ((boundaryReadoutToPrefixLimit D S).hom
          ((colimit.ι (carrierDiagram D) n).hom x)) i =
      S.address n x i.1 := by
  exact boundaryReadoutToPrefixLimit_stage_apply D S n x i

end InfoGeometry.Topology.SymbolicLatentBoundaryAddressPrefixCone
