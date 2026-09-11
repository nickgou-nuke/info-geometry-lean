import InfoGeometry.Topology.SymbolicLatentModularReversalOrbitClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentModularOrbitClosureFlowCompHaus
import InfoGeometry.Topology.SymbolicLatentModularReversalOrbitClosureCompHaus

/-!
# Flow--reversal naturality on modular orbit closures

The ambient reversal law is transported to the closed-orbit carriers.  The
statement compares values in the ambient space, so it remains honest when the
two subtype codomains are propositionally, rather than definitionally, equal.
-/

namespace InfoGeometry.Topology

noncomputable section

theorem SymbolicLatentModularReversal.orbitClosureFlow_naturality
    {X : Type} [TopologicalSpace X] [T2Space X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X) (t : ℝ)
    (y : SymbolicLatentModularOrbitClosure Φ x) :
    ((R.orbitClosureHomeomorph (Φ.act t x))
      (Φ.orbitClosureFlowHomeomorph x t y)).1 =
      ((Φ.orbitClosureFlowHomeomorph (R.involution x) (-t))
        (R.orbitClosureHomeomorph x y)).1 := by
  change R.involution (Φ.act t y.1) =
    Φ.act (-t) (R.involution y.1)
  exact R.reverses_flow t y.1

theorem SymbolicLatentModularReversal.orbitClosureFlowCompHaus_naturality
    {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X) (t : ℝ)
    (y : symbolicLatentModularOrbitClosureCompHaus Φ x) :
    ((R.orbitClosureCompHausIso (Φ.act t x)).hom
        ((Φ.orbitClosureFlowCompHausIso x t).hom y)).1 =
      ((Φ.orbitClosureFlowCompHausIso (R.involution x) (-t)).hom
        ((R.orbitClosureCompHausIso x).hom y)).1 := by
  change R.involution (Φ.act t y.1) =
    Φ.act (-t) (R.involution y.1)
  exact R.reverses_flow t y.1

end
end InfoGeometry.Topology
