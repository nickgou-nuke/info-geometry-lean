import Mathlib.LinearAlgebra.Projectivization.Action
import InfoGeometry.Canonical.LocalSL2ProjectivizationAction

namespace InfoGeometry.Canonical

open scoped LinearAlgebra.Projectivization MatrixGroups

/-!
Affine and infinite representatives for the native real projective line.
The definitions are homogeneous, so no denominator or affine chart
assumption is introduced at this layer.
-/

noncomputable def affineRealProjectivePoint
    (x : ℝ) : RealProjectiveLine :=
  Projectivization.mk ℝ ![x, 1] (by
    intro h
    have h₁ := congrFun h (1 : Fin 2)
    simp at h₁)

noncomputable def infinityRealProjectivePoint : RealProjectiveLine :=
  Projectivization.mk ℝ ![1, 0] (by
    intro h
    have h₀ := congrFun h (0 : Fin 2)
    simp at h₀)

@[simp] theorem localSL2ProjectiveAction_affine_mk
    (ρ : RealSpinorRepresentation) (g : RealSL2) (x : ℝ) :
    representedSL2ProjectiveAction ρ g (affineRealProjectivePoint x) =
      Projectivization.mk ℝ
        (ρ g ![x, 1])
        ((ρ g).map_ne_zero_iff.mpr (by
          intro h
          have h₁ := congrFun h (1 : Fin 2)
          simp at h₁)) := by
  rfl

@[simp] theorem localSL2ProjectiveAction_infinity_mk
    (ρ : RealSpinorRepresentation) (g : RealSL2) :
    representedSL2ProjectiveAction ρ g infinityRealProjectivePoint =
      Projectivization.mk ℝ
        (ρ g ![1, 0])
        ((ρ g).map_ne_zero_iff.mpr (by
          intro h
          have h₀ := congrFun h (0 : Fin 2)
          simp at h₀)) := by
  rfl

theorem localSL2_projective_fixed_of_scalar
    (ρ : RealSpinorRepresentation) (g : RealSL2)
    (v : Fin 2 → ℝ) (hv : v ≠ 0)
    (c : ℝ)
    (hcv : ρ g v = c • v) :
    IsRepresentedSL2ProjectiveFixed ρ g (Projectivization.mk ℝ v hv) := by
  rw [IsRepresentedSL2ProjectiveFixed, representedSL2ProjectiveAction_mk]
  rw [Projectivization.mk_eq_mk_iff' ℝ]
  exact ⟨c, hcv.symm⟩

end InfoGeometry.Canonical
