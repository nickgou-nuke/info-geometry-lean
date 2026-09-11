import InfoGeometry.Topology.SymbolicLatentModularOrbitClosureFlowTopCatIso
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# `TopCat` readout of compact orbit-closure flow isomorphisms

The compact flow iso and the existing `TopCat` flow morphism have the same
underlying restriction of the ambient action.  This owner records that
forgetful compatibility without introducing new orbit-space data.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

theorem SymbolicLatentModularFlow.orbitClosureFlowCompHausIso_hom_forget
    {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (Φ : SymbolicLatentModularFlow X) (x : X) (t : ℝ) :
    compHausToTop.map (Φ.orbitClosureFlowCompHausIso x t).hom =
      Φ.orbitClosureFlowTopCatHom t x := by
  rfl

end InfoGeometry.Topology
