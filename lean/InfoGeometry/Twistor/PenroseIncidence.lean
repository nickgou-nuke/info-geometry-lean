import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Tactic

/-!
# Complex Penrose twistor incidence

This owner introduces the classical complex four-component twistor carrier
`ℂ² ⊕ ℂ²` and the linear incidence map

`π ↦ (i x π, π)`

for a fixed complex `2 × 2` spacetime matrix `x`.

It deliberately does not construct the Penrose transform, sheaf cohomology,
or identify this carrier with the repository's real split-octonion carrier.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Twistor.PenroseIncidence

abbrev Spinor2 := Fin 2 → ℂ
abbrev Twistor4 := Spinor2 × Spinor2
abbrev ComplexSpacetime := Matrix (Fin 2) (Fin 2) ℂ
abbrev ProjectiveTwistor3 := ℙ ℂ Twistor4

/-- The `ω`-spinor in the Penrose incidence relation `ω = i x π`. -/
def omegaLinearMap (x : ComplexSpacetime) : Spinor2 →ₗ[ℂ] Spinor2 where
  toFun π := fun a => Complex.I * (x a 0 * π 0 + x a 1 * π 1)
  map_add' π ρ := by
    funext a
    simp
    ring
  map_smul' c π := by
    funext a
    simp
    ring

@[simp] theorem omegaLinearMap_apply
    (x : ComplexSpacetime) (π : Spinor2) (a : Fin 2) :
    omegaLinearMap x π a =
      Complex.I * (x a 0 * π 0 + x a 1 * π 1) := rfl

/-- The linear Penrose incidence embedding `π ↦ (i x π, π)`. -/
def incidenceLinearMap (x : ComplexSpacetime) : Spinor2 →ₗ[ℂ] Twistor4 where
  toFun π := (omegaLinearMap x π, π)
  map_add' π ρ := by
    ext a <;> simp
  map_smul' c π := by
    ext a <;> simp

@[simp] theorem incidenceLinearMap_fst
    (x : ComplexSpacetime) (π : Spinor2) :
    (incidenceLinearMap x π).1 = omegaLinearMap x π := rfl

@[simp] theorem incidenceLinearMap_snd
    (x : ComplexSpacetime) (π : Spinor2) :
    (incidenceLinearMap x π).2 = π := rfl

/-- The incidence map is injective because the second twistor spinor is `π` itself. -/
theorem incidenceLinearMap_injective (x : ComplexSpacetime) :
    Function.Injective (incidenceLinearMap x) := by
  intro π ρ h
  exact congrArg Prod.snd h

/-- A nonzero spinor gives a nonzero incident twistor. -/
theorem incidenceLinearMap_ne_zero
    (x : ComplexSpacetime) {π : Spinor2} (hπ : π ≠ 0) :
    incidenceLinearMap x π ≠ 0 := by
  intro h
  apply hπ
  exact congrArg Prod.snd h

/-- The affine incidence plane at a fixed spacetime point. -/
def incidencePlane (x : ComplexSpacetime) : Submodule ℂ Twistor4 :=
  LinearMap.range (incidenceLinearMap x)

@[simp] theorem mem_incidencePlane_iff
    (x : ComplexSpacetime) (Z : Twistor4) :
    Z ∈ incidencePlane x ↔ ∃ π : Spinor2, incidenceLinearMap x π = Z := by
  rfl

/-- A nonzero incident twistor determines a point of projective twistor space. -/
def projectiveIncidence
    (x : ComplexSpacetime) (π : Spinor2) (hπ : π ≠ 0) :
    ProjectiveTwistor3 :=
  Projectivization.mk ℂ (incidenceLinearMap x π)
    (incidenceLinearMap_ne_zero x hπ)

/-- The Penrose incidence relation holds literally on the representative used
by `projectiveIncidence`. -/
theorem projectiveIncidence_relation
    (x : ComplexSpacetime) (π : Spinor2) (hπ : π ≠ 0) :
    incidenceLinearMap x π = (omegaLinearMap x π, π) := rfl

/-- Every vector in the incidence plane satisfies the spinor incidence relation
for a unique `π`. -/
theorem incidencePlane_exists_unique_spinor
    (x : ComplexSpacetime) {Z : Twistor4} (hZ : Z ∈ incidencePlane x) :
    ∃! π : Spinor2, incidenceLinearMap x π = Z := by
  rcases hZ with ⟨π, rfl⟩
  refine ⟨π, rfl, ?_⟩
  intro ρ hρ
  exact incidenceLinearMap_injective x hρ

end InfoGeometry.Twistor.PenroseIncidence
