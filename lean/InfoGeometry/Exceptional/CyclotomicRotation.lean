import InfoGeometry.Canonical.TwelveFoldGaussSum
import InfoGeometry.Exceptional.CyclotomicIntegerClock
import InfoGeometry.Exceptional.CyclotomicNeutralBoundary

noncomputable section

namespace InfoGeometry.Exceptional.CyclotomicRotation

open InfoGeometry.Canonical.TwelveFoldAdditiveCharacter
open InfoGeometry.Canonical.TwelveFoldGaussSum
open InfoGeometry.Exceptional.CyclotomicIntegerClock
open InfoGeometry.Exceptional.CyclotomicNeutralBoundary

def rotation : Matrix (Fin 2) (Fin 2) ℝ :=
  Algebra.leftMulMatrix Complex.basisOneI zeta12

theorem rotation_entries :
    rotation = !![Real.sqrt 3 / 2, -(1 / 2); 1 / 2, Real.sqrt 3 / 2] := by
  ext row column
  simp only [rotation, Algebra.leftMulMatrix_eq_repr_mul,
    Complex.coe_basisOneI, Complex.coe_basisOneI_repr, zeta12_algebraic]
  fin_cases row <;> fin_cases column <;> simp

theorem rotation_trigonometric :
    rotation = !![Real.cos (Real.pi / 6), -Real.sin (Real.pi / 6);
      Real.sin (Real.pi / 6), Real.cos (Real.pi / 6)] := by
  rw [Real.cos_pi_div_six, Real.sin_pi_div_six, rotation_entries]

theorem rotation_trace : Matrix.trace rotation = Real.sqrt 3 := by
  rw [rotation_entries]
  simp [Matrix.trace, Fin.sum_univ_two]

theorem rotation_det : rotation.det = 1 := by
  rw [rotation_entries, Matrix.det_fin_two]
  norm_num
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

theorem rotation_order : orderOf rotation = 12 := by
  change orderOf (Algebra.leftMulMatrix Complex.basisOneI zeta12) = 12
  exact (orderOf_injective (Algebra.leftMulMatrix Complex.basisOneI).toMonoidHom
    (Algebra.leftMulMatrix Complex.basisOneI).injective zeta12).trans
      zeta12_primitive.eq_orderOf.symm

theorem rotation_power_eq_one_iff (exponent : ℕ) :
    rotation ^ exponent = 1 ↔ 12 ∣ exponent := by
  rw [← orderOf_dvd_iff_pow_eq_one, rotation_order]

theorem rotation_quartic : rotation ^ 4 - rotation ^ 2 + 1 = 0 := by
  have root_equation := IsPrimitiveRoot.isRoot_cyclotomic
    (by norm_num : 0 < 12) zeta12_primitive
  rw [cyclotomic_twelve] at root_equation
  have scalar_quartic : zeta12 ^ 4 - zeta12 ^ 2 + 1 = 0 := by
    simpa [Polynomial.IsRoot] using root_equation
  simpa only [rotation, map_add, map_sub, map_pow, map_one, map_zero] using
    congrArg (Algebra.leftMulMatrix Complex.basisOneI) scalar_quartic

theorem rotation_half_period : rotation ^ 6 = -1 :=
  pow_six_of_quartic rotation rotation_quartic

theorem rotation_period : rotation ^ 12 = 1 :=
  (rotation_power_eq_one_iff 12).mpr (dvd_refl 12)

theorem rotation_discriminant : Matrix.trace rotation ^ 2 - 4 = -1 := by
  rw [rotation_trace]
  exact square_root_three_discriminant

theorem integer_clock_trace_ne_rotation_trace :
    ((Matrix.trace clock : ℤ) : ℝ) ≠ Matrix.trace rotation := by
  rw [clock_trace, rotation_trace]
  simpa only [Int.cast_zero] using
    (ne_of_lt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)))

end InfoGeometry.Exceptional.CyclotomicRotation
