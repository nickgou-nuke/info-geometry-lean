import Mathlib
import InfoGeometry.Topology.SymbolicLatentModularOrbitClosureTopCat
import InfoGeometry.Topology.SymbolicLatentReversalOrbitTopological

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` transport of modular reversal on orbits and closures

The set-level reversal equalities are already native.  This owner packages
their continuous subtype maps and the ambient naturality squares.
-/

def SymbolicLatentModularReversal.orbitTopCatHom
    {X : Type} [TopologicalSpace X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X) :
    TopCat.of (Φ.orbit x) ⟶
      TopCat.of (Φ.orbit (R.involution x)) :=
  TopCat.ofHom
    { toFun := fun y =>
        ⟨R.involution y.1, by
          rw [← R.orbit_image_eq x]
          exact ⟨y.1, y.2, rfl⟩⟩
      continuous_toFun :=
        (R.involution.continuous.comp continuous_subtype_val).subtype_mk _ }

def SymbolicLatentModularReversal.orbitClosureTopCatHom
    {X : Type} [TopologicalSpace X] [T2Space X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X) :
    TopCat.of (SymbolicLatentModularOrbitClosure Φ x) ⟶
      TopCat.of (SymbolicLatentModularOrbitClosure Φ (R.involution x)) :=
  TopCat.ofHom
    { toFun := fun y =>
        ⟨R.involution y.1, by
          change R.involution y.1 ∈ closure (Φ.orbit (R.involution x))
          rw [← R.orbitClosure_image_eq x]
          exact ⟨y.1, y.2, rfl⟩⟩
      continuous_toFun :=
        (R.involution.continuous.comp continuous_subtype_val).subtype_mk _ }

theorem SymbolicLatentModularReversal.orbitTopCatHom_natural
    {X : Type} [TopologicalSpace X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X) :
    R.orbitTopCatHom x ≫ Φ.orbitInclusionTopCatHom (R.involution x) =
      Φ.orbitInclusionTopCatHom x ≫ R.involution.toTopCatHom := by
  ext y
  rfl

theorem SymbolicLatentModularReversal.orbitClosureTopCatHom_natural
    {X : Type} [TopologicalSpace X] [T2Space X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X) :
    R.orbitClosureTopCatHom x ≫
        Φ.orbitClosureInclusionTopCatHom (R.involution x) =
      Φ.orbitClosureInclusionTopCatHom x ≫ R.involution.toTopCatHom := by
  ext y
  rfl

end InfoGeometry.Topology
