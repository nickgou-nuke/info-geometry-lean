import InfoGeometry.Topology.SymbolicLatentBoundaryInverseLimitCompHaus

/-!
# `TopCat` readout of the compact boundary inverse-limit comparison

The compact boundary owner lifts the native prefix-limit comparison to
`CompHaus`.  These lemmas record that both directions remain the original
`TopCat` comparison after applying the forgetful functor.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory
open NaryTreeBoundaryInverseLimit

universe u

variable {A : Type u} [TopologicalSpace A] [CompactSpace A] [T2Space A]

theorem symbolicBoundaryPrefixLimitCompHausHom_forget :
    compHausToTop.map (symbolicBoundaryPrefixLimitCompHausHom (A := A)) =
      prefixBoundaryLimitIso (A := A).hom := by
  rfl

theorem symbolicBoundaryPrefixLimitCompHausInv_forget :
    compHausToTop.map (symbolicBoundaryPrefixLimitCompHausInv (A := A)) =
      prefixBoundaryLimitIso (A := A).inv := by
  rfl

theorem symbolicBoundaryPrefixLimitCompHausIso_hom_forget :
    compHausToTop.map (symbolicBoundaryPrefixLimitCompHausIso (A := A)).hom =
      prefixBoundaryLimitIso (A := A).hom := by
  rfl

theorem symbolicBoundaryPrefixLimitCompHausIso_inv_forget :
    compHausToTop.map (symbolicBoundaryPrefixLimitCompHausIso (A := A)).inv =
      prefixBoundaryLimitIso (A := A).inv := by
  rfl

end InfoGeometry.Topology

end
