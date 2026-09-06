import InfoGeometry.Topology.SymbolicLatentModularReversalOrbitClosure
import InfoGeometry.Topology.SymbolicLatentModularOrbitClosureCompHaus
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff packaging of general modular reversal

The reversal homeomorphism between orbit closures is promoted to `CompHaus`
when the ambient latent space is compact Hausdorff.  The fixed-point case is
owned separately; this file handles the general pair of reversed base points.
-/

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable section

noncomputable def SymbolicLatentModularReversal.orbitClosureCompHausIso
    {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X) :
    symbolicLatentModularOrbitClosureCompHaus Φ x ≅
      symbolicLatentModularOrbitClosureCompHaus Φ (R.involution x) := by
  letI : CompactSpace (SymbolicLatentModularOrbitClosure Φ x) :=
    isCompact_iff_compactSpace.mp (Φ.isCompact_orbitClosure x)
  letI : CompactSpace
      (SymbolicLatentModularOrbitClosure Φ (R.involution x)) :=
    isCompact_iff_compactSpace.mp
      (Φ.isCompact_orbitClosure (R.involution x))
  dsimp [symbolicLatentModularOrbitClosureCompHaus]
  change CompHaus.of (SymbolicLatentModularOrbitClosure Φ x) ≅
    CompHaus.of (SymbolicLatentModularOrbitClosure Φ (R.involution x))
  let e := R.orbitClosureHomeomorph x
  exact
    { hom := ⟨TopCat.ofHom
        { toFun := e
          continuous_toFun := e.continuous_toFun }⟩
      inv := ⟨TopCat.ofHom
        { toFun := e.symm
          continuous_toFun := e.symm.continuous_toFun }⟩
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro y
        change e.symm (e y) = y
        exact e.symm_apply_apply y
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro y
        change e (e.symm y) = y
        exact e.apply_symm_apply y }

@[simp] theorem SymbolicLatentModularReversal.orbitClosureCompHausIso_hom_apply
    {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X)
    (y : symbolicLatentModularOrbitClosureCompHaus Φ x) :
    (R.orbitClosureCompHausIso x).hom y =
      R.orbitClosureMap x y :=
  rfl

end
end InfoGeometry.Topology
