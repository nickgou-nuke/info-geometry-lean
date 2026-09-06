import InfoGeometry.Topology.SymbolicLatentModularReversalOrbitClosure
import InfoGeometry.Topology.SymbolicLatentModularReversalOrbitClosureCompHaus

/-!
# Involutive reversal on modular orbit closures

The ambient reversal is involutive.  This owner records the corresponding
two-step law on the closed-orbit carriers, both as a homeomorphism-valued
statement and as its compact-Hausdorff packaging.  The equalities compare
ambient values, which avoids identifying propositionally equal subtype
predicates by definitional equality.
-/

namespace InfoGeometry.Topology

noncomputable section

theorem SymbolicLatentModularReversal.orbitClosureHomeomorph_involutive_apply
    {X : Type} [TopologicalSpace X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X)
    (y : SymbolicLatentModularOrbitClosure Φ x) :
    ((R.orbitClosureHomeomorph (R.involution x))
      (R.orbitClosureHomeomorph x y)).1 = y.1 := by
  change R.involution (R.involution y.1) = y.1
  exact R.involution.involutive y.1

theorem SymbolicLatentModularReversal.orbitClosureCompHausIso_involutive_apply
    {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X)
    (y : symbolicLatentModularOrbitClosureCompHaus Φ x) :
    (((R.orbitClosureCompHausIso (R.involution x)).hom)
      ((R.orbitClosureCompHausIso x).hom y)).1 = y.1 := by
  change R.involution (R.involution y.1) = y.1
  exact R.involution.involutive y.1

end
end InfoGeometry.Topology
