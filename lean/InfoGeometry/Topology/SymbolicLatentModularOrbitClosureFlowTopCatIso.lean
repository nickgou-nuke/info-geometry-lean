import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentModularOrbitClosureFlowCompHaus

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` isomorphism for modular-flow orbit closures

The orbit-closure transport map already exists as a `TopCat` morphism.  This
file records that its underlying continuous map is a genuine homeomorphism,
so the categorical map is an isomorphism.  No new orbit or closure notion is
introduced.
-/

theorem SymbolicLatentModularFlow.orbitClosureFlowTopCatHom_isIso
    {X : Type} [TopologicalSpace X] [T2Space X]
    (Φ : SymbolicLatentModularFlow X) (x : X) (t : ℝ) :
    IsIso (Φ.orbitClosureFlowTopCatHom t x) := by
  exact (TopCat.isIso_iff_isHomeomorph
    (Φ.orbitClosureFlowTopCatHom t x)).2
      (Φ.orbitClosureFlowHomeomorph x t).isHomeomorph

end InfoGeometry.Topology
