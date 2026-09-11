import InfoGeometry.Topology.SymbolicLatentBoundaryReadoutInverseLimitCompHaus
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Stage projections of the compact boundary readout

The finite-prefix compatibility law is owned by the native `TopCat`
inverse-limit readout.  This owner transports it to the forgetful image of
the compact-Hausdorff readout, without pretending that the stage colimit and
prefix projections are themselves `CompHaus` morphisms.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory CategoryTheory.Limits
open SymbolicLatentBoundaryAddress
open SymbolicLatentBoundaryReadoutInverseLimit
open NaryTreeBoundaryInverseLimit

variable {ι A : Type} [Fintype ι] [TopologicalSpace A]
variable {D : SymbolicLatentSequence ι}

theorem boundaryReadoutToPrefixLimitCompHausHom_stage
    (D : SymbolicLatentSequence ι)
    (S : SymbolicLatentBoundaryAddress.System A D)
    [CompactSpace A] [T2Space A]
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)]
    (n : ℕ) :
    colimit.ι (carrierDiagram D) n ≫
        compHausToTop.map (boundaryReadoutToPrefixLimitCompHausHom D S) ≫
          limit.π (prefixDiagram (A := A)) (Opposite.op n) =
      (boundaryAddressCocone D S).ι.app n ≫
        (prefixCone (A := A)).π.app (Opposite.op n) := by
  rw [boundaryReadoutToPrefixLimitCompHausHom_forget]
  exact boundaryReadoutToPrefixLimit_stage D S n

theorem boundaryReadoutToPrefixLimitCompHausHom_stage_apply
    (D : SymbolicLatentSequence ι)
    (S : SymbolicLatentBoundaryAddress.System A D)
    [CompactSpace A] [T2Space A]
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)]
    (n : ℕ) (x : (D.obj n).carrier) (i : Fin n) :
    (limit.π (prefixDiagram (A := A)) (Opposite.op n)).hom
        ((compHausToTop.map (boundaryReadoutToPrefixLimitCompHausHom D S)).hom
          ((colimit.ι (carrierDiagram D) n).hom x)) i =
      S.address n x i.1 := by
  rw [boundaryReadoutToPrefixLimitCompHausHom_forget]
  exact boundaryReadoutToPrefixLimit_stage_apply D S n x i

end InfoGeometry.Topology
