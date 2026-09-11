import InfoGeometry.Projective.KleinQuadricLogDeRhamClass
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The multiplicative character carried by logarithmic winding

The winding parameter is additive, while its exponential holonomy is
multiplicative.  This file packages that already-proved law as the native
Mathlib homomorphism `Multiplicative ℤ →* ℂ`; it introduces no new carrier or
unproven assumptions.
-/

namespace InfoGeometry.Projective.KleinQuadric.LogDeRhamClass

noncomputable section

open Complex

def windingCharacterMonoidHom (α : ℝ) : Multiplicative ℤ →* ℂ where
  toFun n := windingCharacter α n
  map_one' := windingCharacter_zero α
  map_mul' := by
    intro m n
    exact windingCharacter_add α m n

def unitCircleUnits : Subgroup ℂˣ where
  carrier := {z | ‖(z : ℂ)‖ = 1}
  one_mem' := by simp
  mul_mem' := by
    intro z w hz hw
    change ‖((z * w : ℂˣ) : ℂ)‖ = 1
    change ‖(z : ℂ)‖ = 1 at hz
    change ‖(w : ℂ)‖ = 1 at hw
    rw [Units.val_mul, norm_mul, hz, hw]
    norm_num
  inv_mem' := by
    intro z hz
    change ‖((z⁻¹ : ℂˣ) : ℂ)‖ = 1
    change ‖(z : ℂ)‖ = 1 at hz
    have hprod :
        ‖(z : ℂ)‖ * ‖((z⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
      rw [← norm_mul]
      simp
    rw [hz] at hprod
    simpa using hprod

def windingCharacterUnitHom (α : ℝ) : Multiplicative ℤ →* ℂˣ where
  toFun n :=
    Units.mk0 (windingCharacterMonoidHom α n)
      (Complex.exp_ne_zero _)
  map_one' := by
    apply Units.ext
    change windingCharacterMonoidHom α (1 : Multiplicative ℤ) = 1
    exact map_one (windingCharacterMonoidHom α)
  map_mul' := by
    intro m n
    apply Units.ext
    change windingCharacterMonoidHom α (m * n) =
      windingCharacterMonoidHom α m * windingCharacterMonoidHom α n
    exact map_mul (windingCharacterMonoidHom α) m n

def windingCharacterCircleHom (α : ℝ) :
    Multiplicative ℤ →* unitCircleUnits :=
  (windingCharacterUnitHom α).codRestrict unitCircleUnits (by
    intro n
    change ‖((windingCharacterUnitHom α n : ℂˣ) : ℂ)‖ = 1
    change ‖windingCharacter α n‖ = 1
    exact windingCharacter_norm α n)

theorem windingCharacterCircleHom_val (α : ℝ) (n : ℤ) :
    (((windingCharacterCircleHom α (Multiplicative.ofAdd n) :
      unitCircleUnits) : ℂˣ) : ℂ) =
      windingCharacter α n := by
  rfl

theorem windingCharacterCircleHom_neg (α : ℝ) (n : ℤ) :
    windingCharacterCircleHom α (Multiplicative.ofAdd (-n)) =
      (windingCharacterCircleHom α (Multiplicative.ofAdd n))⁻¹ := by
  simpa using
    (map_inv (windingCharacterCircleHom α) (Multiplicative.ofAdd n))

/-- Multiple winding is carried to the corresponding integer power in the
unit-circle subgroup. -/
theorem windingCharacterCircleHom_mul_winding
    (α : ℝ) (k n : ℤ) :
    windingCharacterCircleHom α (Multiplicative.ofAdd (k * n)) =
      (windingCharacterCircleHom α (Multiplicative.ofAdd n)) ^ k := by
  have hsource :
      Multiplicative.ofAdd (k * n) =
        (Multiplicative.ofAdd n) ^ k := by
    change k * n = k • n
    simp
  rw [hsource]
  exact MonoidHom.map_zpow (windingCharacterCircleHom α)
    (Multiplicative.ofAdd n) k

/-- A character of the cyclic winding source is determined by its value on
the primitive winding `1`. -/
theorem windingCharacterCircleHom_eq_generator_zpow
    (α : ℝ) (n : ℤ) :
    windingCharacterCircleHom α (Multiplicative.ofAdd n) =
      (windingCharacterCircleHom α (Multiplicative.ofAdd 1)) ^ n := by
  simpa using windingCharacterCircleHom_mul_winding α n 1

@[simp] theorem windingCharacterMonoidHom_apply (α : ℝ) (n : ℤ) :
    windingCharacterMonoidHom α (Multiplicative.ofAdd n) = windingCharacter α n := by
  rfl

theorem windingCharacterMonoidHom_mul (α : ℝ) (m n : ℤ) :
    windingCharacterMonoidHom α (Multiplicative.ofAdd (m + n)) =
      windingCharacterMonoidHom α (Multiplicative.ofAdd m) *
        windingCharacterMonoidHom α (Multiplicative.ofAdd n) := by
  simpa using (map_mul (windingCharacterMonoidHom α)
    (Multiplicative.ofAdd m) (Multiplicative.ofAdd n))

/-- Complex-valued readout of the cyclic-generator classification. -/
theorem windingCharacter_eq_one_zpow (α : ℝ) (n : ℤ) :
    windingCharacter α n = windingCharacter α 1 ^ n := by
  have h := congrArg
    (fun z : unitCircleUnits => (((z : unitCircleUnits) : ℂˣ) : ℂ))
    (windingCharacterCircleHom_eq_generator_zpow α n)
  simpa [windingCharacterCircleHom_val] using h

end

end InfoGeometry.Projective.KleinQuadric.LogDeRhamClass
