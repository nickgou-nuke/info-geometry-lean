import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.Cl44QuaternionSplit

noncomputable section

namespace InfoGeometry.Projective.QuaternionicMöbius

open InfoGeometry.Projective

abbrev H := Quaternion ℝ

structure BlockOperator where
  a : H
  b : H
  c : H
  d : H

abbrev Spinor := H × H

def blockAction (G : BlockOperator) (ψ : Spinor) : Spinor :=
  (G.a * ψ.1 + G.b * ψ.2, G.c * ψ.1 + G.d * ψ.2)

noncomputable def projectiveCoordinate (ψ : Spinor) : H :=
  ψ.1 * ψ.2⁻¹

noncomputable def mobiusAction (G : BlockOperator) (q : H) : H :=
  (G.a * q + G.b) * (G.c * q + G.d)⁻¹

theorem projective_blockAction_eq_mobius
    (G : BlockOperator) (ψ : Spinor)
    (hv : IsUnit ψ.2)
    (hden : IsUnit (G.c * projectiveCoordinate ψ + G.d)) :
    projectiveCoordinate (blockAction G ψ) =
      mobiusAction G (projectiveCoordinate ψ) := by
  let q : H := projectiveCoordinate ψ
  have hv0 : ψ.2 ≠ 0 := hv.ne_zero
  have hden0 : G.c * q + G.d ≠ 0 := by
    exact hden.ne_zero
  have hqv : q * ψ.2 = ψ.1 := by
    dsimp [q, projectiveCoordinate]
    rw [mul_assoc, inv_mul_cancel₀ hv0, mul_one]
  have hnum : G.a * ψ.1 + G.b * ψ.2 =
      (G.a * q + G.b) * ψ.2 := by
    rw [← hqv]
    noncomm_ring
  have hden' : G.c * ψ.1 + G.d * ψ.2 =
      (G.c * q + G.d) * ψ.2 := by
    rw [← hqv]
    noncomm_ring
  have hinv : ((G.c * q + G.d) * ψ.2)⁻¹ =
      ψ.2⁻¹ * (G.c * q + G.d)⁻¹ := by
    symm
    apply eq_inv_of_mul_eq_one_right
    calc
      (G.c * q + G.d) * ψ.2 *
          (ψ.2⁻¹ * (G.c * q + G.d)⁻¹) =
          (G.c * q + G.d) * (ψ.2 * ψ.2⁻¹) *
            (G.c * q + G.d)⁻¹ := by noncomm_ring
      _ = (G.c * q + G.d) * 1 * (G.c * q + G.d)⁻¹ := by
        rw [mul_inv_cancel₀ hv0]
      _ = 1 := by rw [mul_one, mul_inv_cancel₀ hden0]
  change
    (G.a * ψ.1 + G.b * ψ.2) *
        (G.c * ψ.1 + G.d * ψ.2)⁻¹ =
      (G.a * q + G.b) * (G.c * q + G.d)⁻¹
  rw [hnum, hden']
  rw [hinv]
  calc
    (G.a * q + G.b) * ψ.2 *
        (ψ.2⁻¹ * (G.c * q + G.d)⁻¹) =
        (G.a * q + G.b) * (ψ.2 * ψ.2⁻¹) *
          (G.c * q + G.d)⁻¹ := by noncomm_ring
    _ = (G.a * q + G.b) * (G.c * q + G.d)⁻¹ := by
      rw [mul_inv_cancel₀ hv0, mul_one]

end InfoGeometry.Projective.QuaternionicMöbius
