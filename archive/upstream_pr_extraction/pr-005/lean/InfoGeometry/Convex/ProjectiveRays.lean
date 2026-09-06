import InfoGeometry.Clifford.Cl11
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Projective Rays (Doubled Space)

Mathlib-native projectivization of doubled states:
physical states are rays in `DoubledSpace E`, i.e. `ℙ ℝ (DoubledSpace E)`.
-/

namespace InfoGeometry.Convex

open scoped LinearAlgebra.Projectivization

variable {E : Type} [AddCommGroup E] [Module ℝ E]

/-- “Physical states” as rays in the doubled space (excluding `0` by construction). -/
abbrev ProjectiveState : Type _ := ℙ ℝ (DoubledSpace E)

/-- Nonzero doubled states (representatives of physical rays). -/
abbrev NonzeroDoubledState : Type _ := { v : DoubledSpace E // v ≠ 0 }

/-- Canonical projection from a nonzero doubled state to its projective ray. -/
noncomputable def projectivize (v : DoubledSpace E) (hv : v ≠ 0) : ProjectiveState (E := E) :=
  Projectivization.mk ℝ v hv

/-- Canonical projection from a nonzero doubled-state subtype to its projective ray. -/
noncomputable def projectivize' (v : NonzeroDoubledState (E := E)) : ProjectiveState (E := E) :=
  Projectivization.mk' ℝ v

@[simp] lemma projectivize'_eq_projectivize (v : NonzeroDoubledState (E := E)) :
    projectivize' (E := E) v = projectivize (E := E) v.1 v.2 := by
  simp [projectivize', projectivize, Projectivization.mk'_eq_mk]

section ScaleInvariant

/-- Ray invariance under nonzero scalar multiplication of representatives. -/
lemma projectivize_smul
    (a : ℝ) (ha : a ≠ 0) (v : DoubledSpace E) (hv : v ≠ 0) :
    projectivize (E := E) (a • v) (smul_ne_zero ha hv)
      = projectivize (E := E) v hv := by
  exact
    (Projectivization.mk_eq_mk_iff (K := ℝ) (v := a • v) (w := v)
      (hv := smul_ne_zero ha hv) (hw := hv)).2
      ⟨Units.mk0 a ha, by simp [Units.smul_def]⟩

/-- Subtype version of ray invariance under nonzero scalar multiplication. -/
lemma projectivize'_smul
    (a : ℝ) (ha : a ≠ 0) (v : NonzeroDoubledState (E := E)) :
    projectivize' (E := E) ⟨a • v.1, smul_ne_zero ha v.2⟩ = projectivize' (E := E) v := by
  simpa [projectivize'_eq_projectivize] using
    (projectivize_smul (E := E) a ha v.1 v.2)

end ScaleInvariant

end InfoGeometry.Convex
