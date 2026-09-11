import InfoGeometry.Topology.SymbolicLatentQuotientOrbitClosureFlowCompHaus
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentQuotientOrbitClosureFlowTopCatIso

/-!
# Naturality of compact quotient orbit-closure flow

The restricted orbit-closure flow is a compact-Hausdorff isomorphism whose
underlying map is the ambient quotient flow.  This owner records the
corresponding naturality square in the faithful `TopCat` readout.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

theorem SymbolicLatentFlowQuotient.orbitClosureFlowCompHausIso_hom_natural
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    [CompactSpace Q] [T2Space Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (q : Q) (t : ℝ) :
    compHausToTop.map (K.orbitClosureFlowCompHausIso q t).hom ≫
        symbolicLatentOrbitClosureInclusion K (K.act t q) =
      symbolicLatentOrbitClosureInclusion K q ≫ K.actTopCatHom t := by
  change K.orbitClosureFlowTopCatHom q t ≫
      symbolicLatentOrbitClosureInclusion K (K.act t q) =
    symbolicLatentOrbitClosureInclusion K q ≫ K.actTopCatHom t
  exact K.orbitClosureFlowTopCatHom_natural q t


end InfoGeometry.Topology
