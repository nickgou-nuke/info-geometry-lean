import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Tactic

/-!
# Complex Penrose incidence

This owner supplies the missing complex-spinor incidence layer.  It uses the
native `Projectivization` quotient and keeps the distinction between the
linear incidence plane and its projectivization explicit.
-/

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Twistor.PenroseIncidence

abbrev Spinor2 := Fin 2 → ℂ
abbrev Twistor4 := Spinor2 × Spinor2
abbrev ComplexSpacetime := Matrix (Fin 2) (Fin 2) ℂ
abbrev ProjectiveSpinorLine := ℙ ℂ Spinor2
abbrev ProjectiveTwistor3 := ℙ ℂ Twistor4

def omegaLinearMap (x : ComplexSpacetime) : Spinor2 →ₗ[ℂ] Spinor2 :=
  Matrix.toLin' x

@[simp] theorem omegaLinearMap_apply (x : ComplexSpacetime) (π : Spinor2) :
    omegaLinearMap x π = Matrix.mulVec x π := by
  rfl

def incidenceLinearMap (x : ComplexSpacetime) :
    Spinor2 →ₗ[ℂ] Twistor4 where
  toFun π := (Complex.I • omegaLinearMap x π, π)
  map_add' π ρ := by
    simp [map_add, smul_add]
  map_smul' c π := by
    simp [map_smul, smul_smul, mul_comm]

@[simp] theorem incidenceLinearMap_apply (x : ComplexSpacetime) (π : Spinor2) :
    incidenceLinearMap x π = (Complex.I • omegaLinearMap x π, π) := rfl

theorem incidenceLinearMap_injective (x : ComplexSpacetime) :
    Function.Injective (incidenceLinearMap x) := by
  intro π ρ h
  exact congrArg Prod.snd h

def incidencePlane (x : ComplexSpacetime) : Submodule ℂ Twistor4 :=
  LinearMap.range (incidenceLinearMap x)

def projectiveIncidence
    (x : ComplexSpacetime) (π : Spinor2) (hπ : π ≠ 0) :
    ProjectiveTwistor3 :=
  Projectivization.mk ℂ (incidenceLinearMap x π) (by
    intro h
    apply hπ
    exact congrArg Prod.snd h)

@[simp] theorem projectiveIncidence_mk
    (x : ComplexSpacetime) (π : Spinor2) (hπ : π ≠ 0) :
    projectiveIncidence x π hπ =
      Projectivization.mk ℂ (incidenceLinearMap x π) (by
        intro h
        apply hπ
        exact congrArg Prod.snd h) := rfl

theorem incidencePlane_exists_unique_spinor
    (x : ComplexSpacetime) (Z : Twistor4)
    (hZ : Z ∈ incidencePlane x) :
    ∃! π : Spinor2, incidenceLinearMap x π = Z := by
  rcases hZ with ⟨π, rfl⟩
  refine ⟨π, rfl, ?_⟩
  intro ρ hρ
  exact incidenceLinearMap_injective x hρ

/- The linear incidence plane projectivizes to the Penrose line in projective
twistor space.  This uses Mathlib's quotient-level projectivization map. -/
def projectiveIncidenceMap
    (x : ComplexSpacetime) :
    ProjectiveSpinorLine → ProjectiveTwistor3 :=
  Projectivization.map (incidenceLinearMap x)
    (incidenceLinearMap_injective x)

@[simp] theorem projectiveIncidenceMap_mk
    (x : ComplexSpacetime) (π : Spinor2) (hπ : π ≠ 0) :
    projectiveIncidenceMap x (Projectivization.mk ℂ π hπ) =
      projectiveIncidence x π hπ := rfl

theorem projectiveIncidenceMap_injective (x : ComplexSpacetime) :
    Function.Injective (projectiveIncidenceMap x) := by
  exact Projectivization.map_injective (incidenceLinearMap x)
    (incidenceLinearMap_injective x)

end InfoGeometry.Twistor.PenroseIncidence
