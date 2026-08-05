import InfoGeometry.Topology.SymbolicLatentModularOrbitClosureTopCat
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff packaging of modular orbit closures

The modular orbit-closure owner already supplies the native closed-subspace
embedding and compactness theorem.  This bridge packages that same subtype in
`CompHaus`, without introducing a second closure or a synthetic compactness
axiom.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]

noncomputable def symbolicLatentModularOrbitClosureCompHaus
    (Φ : SymbolicLatentModularFlow X) (x : X) : CompHaus := by
  letI : CompactSpace (SymbolicLatentModularOrbitClosure Φ x) :=
    isCompact_iff_compactSpace.mp (Φ.isCompact_orbitClosure x)
  exact CompHaus.of (SymbolicLatentModularOrbitClosure Φ x)

noncomputable def symbolicLatentModularOrbitClosureCompHausTopCatHom
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    compHausToTop.obj (symbolicLatentModularOrbitClosureCompHaus Φ x) ⟶
      TopCat.of X := by
  dsimp [symbolicLatentModularOrbitClosureCompHaus]
  change TopCat.of (SymbolicLatentModularOrbitClosure Φ x) ⟶ TopCat.of X
  exact Φ.orbitClosureInclusionTopCatHom x

noncomputable def symbolicLatentModularOrbitClosureCompHausHom
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    symbolicLatentModularOrbitClosureCompHaus Φ x ⟶ CompHaus.of X := by
  letI : CompactSpace (SymbolicLatentModularOrbitClosure Φ x) :=
    isCompact_iff_compactSpace.mp (Φ.isCompact_orbitClosure x)
  dsimp [symbolicLatentModularOrbitClosureCompHaus]
  change CompHaus.of (SymbolicLatentModularOrbitClosure Φ x) ⟶ CompHaus.of X
  exact ⟨Φ.orbitClosureInclusionTopCatHom x⟩

@[simp] theorem symbolicLatentModularOrbitClosureCompHausTopCatHom_apply
    (Φ : SymbolicLatentModularFlow X) (x : X)
    (y : symbolicLatentModularOrbitClosureCompHaus Φ x) :
    symbolicLatentModularOrbitClosureCompHausTopCatHom Φ x y = y.1 :=
  rfl

theorem symbolicLatentModularOrbitClosureCompHausHom_forget
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    compHausToTop.map (symbolicLatentModularOrbitClosureCompHausHom Φ x) =
      Φ.orbitClosureInclusionTopCatHom x := by
  rfl

theorem symbolicLatentModularOrbitClosureCompHausTopCatHom_isClosedEmbedding
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    Topology.IsClosedEmbedding
      (symbolicLatentModularOrbitClosureCompHausTopCatHom Φ x) := by
  dsimp [symbolicLatentModularOrbitClosureCompHausTopCatHom]
  simpa [symbolicLatentModularOrbitClosureCompHaus] using
    (Φ.orbitClosure_isClosedEmbedding x)

end InfoGeometry.Topology

end
