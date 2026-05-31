import Mathlib.Data.Real.Basic

set_option autoImplicit false

/-!
# InfoGeometry.Physics.FermionicAndreevReflection

A finite two-coordinate BdG/Andreev reflection atom.

The map `andreevReflection (e,h) = (-h,e)` is the real `90°` rotation on the
finite electron/hole coordinate plane, so its square is `-id` and its fourth
power is `id`.

This file proves only that finite coordinate algebra.  It does not prove a
spin-statistics theorem, topological edge protection, a DIII classification
result, or a superconducting event-horizon theorem.
-/

namespace InfoGeometry.Physics.FermionicAndreevReflection

/-- Two real coordinates for a finite electron/hole BdG amplitude. -/
@[ext]
structure BdGQuasiparticle where
  /-- Electron-like coordinate. -/
  e : ℝ
  /-- Hole-like coordinate. -/
  h : ℝ

instance : Neg BdGQuasiparticle where
  neg p := ⟨-p.e, -p.h⟩

instance : Zero BdGQuasiparticle where
  zero := ⟨0, 0⟩

/-- Finite Andreev reflection atom `(e,h) ↦ (-h,e)`. -/
def andreevReflection (p : BdGQuasiparticle) : BdGQuasiparticle :=
  ⟨-p.h, p.e⟩

/-- Applying the finite Andreev reflection twice gives the negative amplitude. -/
theorem andreevReflection_sq (p : BdGQuasiparticle) :
    andreevReflection (andreevReflection p) = -p := by
  rfl

/-- Pasted-snippet-compatible name for the finite Andreev square law. -/
theorem andreev_reflection_fermionic (p : BdGQuasiparticle) :
    andreevReflection (andreevReflection p) = -p :=
  andreevReflection_sq p

/-- Applying the finite Andreev reflection four times returns the amplitude. -/
theorem andreevReflection_fourth (p : BdGQuasiparticle) :
    andreevReflection (andreevReflection (andreevReflection (andreevReflection p))) = p := by
  ext <;> simp [andreevReflection]

/-- The finite Andreev reflection fixes the zero amplitude. -/
theorem andreevReflection_zero :
    andreevReflection 0 = 0 := by
  change andreevReflection (⟨0, 0⟩ : BdGQuasiparticle) =
    (⟨0, 0⟩ : BdGQuasiparticle)
  ext <;> norm_num [andreevReflection]

end InfoGeometry.Physics.FermionicAndreevReflection
