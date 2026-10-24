/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ReflexiveNilpotentFlows

/-! The existing diagonal flows form a homomorphism of native unit groups.
The existing Weyl unit conjugates this homomorphism to its group inverse.
The active support need not equal the ambient identity.
-/
namespace InfoGeometry.Canonical.ReflexiveNilpotentFlows

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable {d B : A} (hd : d * d = 0) (hB : B * B = 0)
  (hr : d * B * d = d) (hs : B * d * B = B)

def diagonalUnit (λ : Rˣ) : Aˣ where
  val := diagonal (λ : R) (↑(λ⁻¹) : R) d B
  inv := diagonal (↑(λ⁻¹) : R) (λ : R) d B
  val_inv := diagonal_inverse hd hB hr hs _ _ (by simp)
  inv_val := diagonal_inverse hd hB hr hs _ _ (by simp)

@[simp] theorem diagonalUnit_val (λ : Rˣ) :
    (diagonalUnit hd hB hr hs λ : A) = diagonal (λ : R) (↑(λ⁻¹) : R) d B := rfl

@[simp] theorem diagonalUnit_inv_val (λ : Rˣ) :
    (↑((diagonalUnit hd hB hr hs λ)⁻¹) : A) =
      diagonal (↑(λ⁻¹) : R) (λ : R) d B := rfl

def diagonalUnitsHom : Rˣ →* Aˣ where
  toFun := diagonalUnit hd hB hr hs
  map_one' := by
    apply Units.ext
    simp [diagonalUnit, diagonal, complement, support]
  map_mul' λ μ := by
    apply Units.ext
    change diagonal (↑(λ * μ) : R) (↑((λ * μ)⁻¹) : R) d B =
      diagonal (λ : R) (↑(λ⁻¹) : R) d B *
        diagonal (μ : R) (↑(μ⁻¹) : R) d B
    rw [diagonal_mul hd hB hr hs]
    simp [mul_comm]

@[simp] theorem diagonalUnitsHom_apply (λ : Rˣ) :
    diagonalUnitsHom hd hB hr hs λ = diagonalUnit hd hB hr hs λ := rfl

theorem weylUnit_conjugates_diagonalUnit (λ : Rˣ) :
    weylUnit hd hB hr hs * diagonalUnit hd hB hr hs λ *
      (weylUnit hd hB hr hs)⁻¹ = (diagonalUnit hd hB hr hs λ)⁻¹ := by
  apply Units.ext
  change weyl d B * diagonal (λ : R) (↑(λ⁻¹) : R) d B * weylInv d B =
    diagonal (↑(λ⁻¹) : R) (λ : R) d B
  exact weyl_diagonal hd hB hr hs _ _

theorem weylUnit_conjugates_diagonalUnitsHom (λ : Rˣ) :
    weylUnit hd hB hr hs * diagonalUnitsHom hd hB hr hs λ *
      (weylUnit hd hB hr hs)⁻¹ = diagonalUnitsHom hd hB hr hs (λ⁻¹) := by
  rw [map_inv]
  exact weylUnit_conjugates_diagonalUnit hd hB hr hs λ

end InfoGeometry.Canonical.ReflexiveNilpotentFlows
