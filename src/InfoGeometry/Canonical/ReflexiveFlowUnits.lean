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

def diagonalUnit (t : Rˣ) : Aˣ where
  val := diagonal (t : R) (↑(t⁻¹) : R) d B
  inv := diagonal (↑(t⁻¹) : R) (t : R) d B
  val_inv := diagonal_inverse hd hB hr hs _ _ (by simp)
  inv_val := diagonal_inverse hd hB hr hs _ _ (by simp)

@[simp] theorem diagonalUnit_val (t : Rˣ) :
    (diagonalUnit hd hB hr hs t : A) = diagonal (t : R) (↑(t⁻¹) : R) d B := rfl

@[simp] theorem diagonalUnit_inv_val (t : Rˣ) :
    (↑((diagonalUnit hd hB hr hs t)⁻¹) : A) =
      diagonal (↑(t⁻¹) : R) (t : R) d B := rfl

def diagonalUnitsHom : Rˣ →* Aˣ where
  toFun := diagonalUnit hd hB hr hs
  map_one' := by
    apply Units.ext
    simp [diagonalUnit, diagonal, complement, support]
  map_mul' t u := by
    apply Units.ext
    change diagonal (↑(t * u) : R) (↑((t * u)⁻¹) : R) d B =
      diagonal (t : R) (↑(t⁻¹) : R) d B *
        diagonal (u : R) (↑(u⁻¹) : R) d B
    rw [diagonal_mul hd hB hr hs]
    simp [mul_comm]

@[simp] theorem diagonalUnitsHom_apply (t : Rˣ) :
    diagonalUnitsHom hd hB hr hs t = diagonalUnit hd hB hr hs t := rfl

theorem weylUnit_conjugates_diagonalUnit (t : Rˣ) :
    weylUnit hd hB hr * diagonalUnit hd hB hr hs t *
      (weylUnit hd hB hr)⁻¹ = (diagonalUnit hd hB hr hs t)⁻¹ := by
  apply Units.ext
  change weyl d B * diagonal (t : R) (↑(t⁻¹) : R) d B * weylInv d B =
    diagonal (↑(t⁻¹) : R) (t : R) d B
  exact weyl_diagonal hd hB hr hs _ _

theorem weylUnit_conjugates_diagonalUnitsHom (t : Rˣ) :
    weylUnit hd hB hr * diagonalUnitsHom hd hB hr hs t *
      (weylUnit hd hB hr)⁻¹ = diagonalUnitsHom hd hB hr hs (t⁻¹) := by
  rw [map_inv]
  exact weylUnit_conjugates_diagonalUnit hd hB hr hs t

end InfoGeometry.Canonical.ReflexiveNilpotentFlows
