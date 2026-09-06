import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import InfoGeometry.Canonical.ProjectiveFoundation

namespace InfoGeometry.Canonical

open scoped LinearAlgebra.Projectivization MatrixGroups

/-!
## The local projective boundary API

The ambient Zorn algebra is nonassociative, so it is not used as a global
group acting on a projective line.  This file packages the exact associative
input needed for a projective action: a genuine linear representation of
`SL₂(ℝ)`.  The action is then obtained from Mathlib's projectivization map;
fixed points are equality in projective space, not a determinant-zero
surrogate over an arbitrary ring.
-/

abbrev RealProjectiveLine := ℙ ℝ (Fin 2 → ℝ)

abbrev RealSL2 := Matrix.SpecialLinearGroup (Fin 2) ℝ

abbrev RealSpinorRepresentation :=
  RealSL2 →* ((Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ))

def representedSL2ProjectiveAction (ρ : RealSpinorRepresentation) :
    RealSL2 →* Function.End RealProjectiveLine :=
  { toFun := fun g =>
      Projectivization.map (ρ g).toLinearMap (ρ g).injective
    map_one' := by
      funext p
      have h_id : (ρ 1).toLinearMap = LinearMap.id := by
        ext x
        simp
      simpa only [h_id] using
        (congrFun
          (Projectivization.map_id
            (K := ℝ) (V := Fin 2 → ℝ)) p)
    map_mul' := by
      intro g h
      change Projectivization.map (ρ (g * h)).toLinearMap _ =
        Projectivization.map (ρ g).toLinearMap _ ∘
          Projectivization.map (ρ h).toLinearMap _
      have hcomp :
          (ρ (g * h)).toLinearMap =
            (ρ g).toLinearMap.comp (ρ h).toLinearMap := by
        ext x
        simp [ρ.map_mul, LinearMap.comp_apply]
      funext p
      induction p using Projectivization.ind with
      | h v hv =>
          change
            Projectivization.map (ρ (g * h)).toLinearMap _
                (Projectivization.mk ℝ v hv) =
              Projectivization.map (ρ g).toLinearMap _
                (Projectivization.map (ρ h).toLinearMap _
                  (Projectivization.mk ℝ v hv))
          rw [Projectivization.map_mk, Projectivization.map_mk,
            Projectivization.map_mk]
          congr 1
          simpa [ρ.map_mul, LinearMap.comp_apply] using congrArg
            (fun e => e v) hcomp }

@[simp] theorem representedSL2ProjectiveAction_one
    (ρ : RealSpinorRepresentation) :
    representedSL2ProjectiveAction ρ 1 = 1 := by
  exact (representedSL2ProjectiveAction ρ).map_one

theorem representedSL2ProjectiveAction_mul
    (ρ : RealSpinorRepresentation) (g h : RealSL2) :
    representedSL2ProjectiveAction ρ (g * h) =
      representedSL2ProjectiveAction ρ g ∘ representedSL2ProjectiveAction ρ h := by
  exact (representedSL2ProjectiveAction ρ).map_mul g h

@[simp] theorem representedSL2ProjectiveAction_mk
    (ρ : RealSpinorRepresentation) (g : RealSL2)
    (v : Fin 2 → ℝ) (hv : v ≠ 0) :
    representedSL2ProjectiveAction ρ g (Projectivization.mk ℝ v hv) =
      Projectivization.mk ℝ (ρ g v)
        ((ρ g).map_ne_zero_iff.mpr hv) := by
  exact Projectivization.map_mk (ρ g).toLinearMap (ρ g).injective v hv

def IsRepresentedSL2ProjectiveFixed
    (ρ : RealSpinorRepresentation) (g : RealSL2)
    (p : RealProjectiveLine) : Prop :=
  representedSL2ProjectiveAction ρ g p = p

theorem representedSL2ProjectiveFixed_iff
    (ρ : RealSpinorRepresentation) (g : RealSL2)
    (p : RealProjectiveLine) :
    IsRepresentedSL2ProjectiveFixed ρ g p ↔
      representedSL2ProjectiveAction ρ g p = p :=
  Iff.rfl

theorem representedSL2ProjectiveAction_iterate
    (ρ : RealSpinorRepresentation) (g : RealSL2)
    (n : ℕ) (p : RealProjectiveLine) :
    (representedSL2ProjectiveAction ρ g)^[n] p =
      representedSL2ProjectiveAction ρ (g ^ n) p := by
  induction n generalizing p with
  | zero =>
      rw [pow_zero, representedSL2ProjectiveAction_one]
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih]
      change
        (representedSL2ProjectiveAction ρ (g ^ n) ∘
            representedSL2ProjectiveAction ρ g) p =
          representedSL2ProjectiveAction ρ (g ^ (n + 1)) p
      rw [← representedSL2ProjectiveAction_mul, pow_succ]

end InfoGeometry.Canonical
