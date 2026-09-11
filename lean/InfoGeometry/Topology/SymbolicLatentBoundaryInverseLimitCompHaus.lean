import InfoGeometry.Topology.SymbolicLatentBoundaryCompactTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Category.CompHaus.Basic

namespace InfoGeometry.Topology

open CategoryTheory CategoryTheory.Limits
open NaryTreeBoundaryInverseLimit

noncomputable section

universe u

variable {A : Type u} [TopologicalSpace A] [CompactSpace A] [T2Space A]

/-- Compact-Hausdorff packaging of the sequence-space boundary. -/
noncomputable def symbolicBoundaryCompHaus : CompHaus :=
  CompHaus.of (Boundary (A := A))

/-- Compact-Hausdorff packaging of the native prefix inverse-limit object. -/
noncomputable def symbolicBoundaryPrefixLimitCompHaus : CompHaus :=
  CompHaus.of ((limit (prefixDiagram (A := A)) : TopCat) : Type u)

/-- The native boundary-to-limit comparison, lifted from `TopCat` to
`CompHaus` using the already-proved compact/Hausdorff instances. -/
noncomputable def symbolicBoundaryPrefixLimitCompHausHom :
    symbolicBoundaryCompHaus (A := A) ⟶
      symbolicBoundaryPrefixLimitCompHaus (A := A) := by
  change CompHaus.of (Boundary (A := A)) ⟶
    CompHaus.of ((limit (prefixDiagram (A := A)) : TopCat) : Type u)
  exact ⟨prefixBoundaryLimitIso (A := A).hom⟩

noncomputable def symbolicBoundaryPrefixLimitCompHausInv :
    symbolicBoundaryPrefixLimitCompHaus (A := A) ⟶
      symbolicBoundaryCompHaus (A := A) := by
  change CompHaus.of ((limit (prefixDiagram (A := A)) : TopCat) : Type u) ⟶
    CompHaus.of (Boundary (A := A))
  exact ⟨prefixBoundaryLimitIso (A := A).inv⟩

/-- The inverse-limit comparison is an isomorphism in `CompHaus`, not merely
an isomorphism after forgetting compact-Hausdorff structure. -/
noncomputable def symbolicBoundaryPrefixLimitCompHausIso :
    symbolicBoundaryCompHaus (A := A) ≅
      symbolicBoundaryPrefixLimitCompHaus (A := A) where
  hom := symbolicBoundaryPrefixLimitCompHausHom (A := A)
  inv := symbolicBoundaryPrefixLimitCompHausInv (A := A)
  hom_inv_id := by
    apply ConcreteCategory.hom_ext
    intro x
    change (TopCat.Hom.hom (prefixBoundaryLimitIso (A := A)).inv)
        ((TopCat.Hom.hom (prefixBoundaryLimitIso (A := A)).hom) x) = x
    have h := congrArg
      (fun q => (TopCat.Hom.hom q) x)
      (prefixBoundaryLimitIso (A := A)).hom_inv_id
    exact h
  inv_hom_id := by
    apply ConcreteCategory.hom_ext
    intro x
    change (TopCat.Hom.hom (prefixBoundaryLimitIso (A := A)).hom)
        ((TopCat.Hom.hom (prefixBoundaryLimitIso (A := A)).inv) x) = x
    have h := congrArg
      (fun q => (TopCat.Hom.hom q) x)
      (prefixBoundaryLimitIso (A := A)).inv_hom_id
    exact h

end

end InfoGeometry.Topology
