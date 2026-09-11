import InfoGeometry.Topology.SymbolicLatentBoundaryCylinderQuotientTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Conditional `CompHaus` bridge for the boundary-cylinder readout

The carrier colimit readout already has a native `TopCat` quotient-map
theorem under explicit compactness and surjectivity hypotheses.  This file
packages that same morphism in `CompHaus` only when the symbolic alphabet is
finite and discrete, so the sequence boundary is compact Hausdorff as well.
No compactness or quotient property is asserted for the unrestricted carrier.
-/

noncomputable section

namespace InfoGeometry.Topology.SymbolicLatentBoundaryCylinderQuotientCompHaus

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Topology.SymbolicLatentBoundaryAddress
open InfoGeometry.Topology.SymbolicLatentBoundaryCylinderQuotientTopCat

variable {ι : Type} {A : Type}
  [Fintype ι] [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [T2Space A]
variable {D : SymbolicLatentSequence ι}

noncomputable def boundaryReadoutCompHausHom
    (S : System A D)
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)] :
    CompHaus.of ((colimit (carrierDiagram D) : TopCat) : Type) ⟶
      CompHaus.of (ℕ → A) := by
  change CompHaus.of ((colimit (carrierDiagram D) : TopCat) : Type) ⟶
    CompHaus.of (ℕ → A)
  exact ⟨boundaryReadout D S⟩

theorem boundaryReadoutCompHausHom_forget
    (S : System A D)
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)] :
    compHausToTop.map (boundaryReadoutCompHausHom S) =
      boundaryReadout D S := by
  rfl

theorem boundaryReadoutCompHausHom_isQuotientMap
    (S : System A D)
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)]
    (h_surj : Function.Surjective (boundaryReadout D S).hom) :
    Topology.IsQuotientMap
      (compHausToTop.map (boundaryReadoutCompHausHom S)).hom := by
  rw [boundaryReadoutCompHausHom_forget S]
  exact boundaryReadout_isQuotientMap_of_compactSpace S h_surj


end InfoGeometry.Topology.SymbolicLatentBoundaryCylinderQuotientCompHaus
