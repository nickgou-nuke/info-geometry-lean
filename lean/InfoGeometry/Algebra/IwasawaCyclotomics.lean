import InfoGeometry.Algebra.MatrixCyclotomics

noncomputable section

namespace InfoGeometry.Algebra.IwasawaCyclotomics

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.GrandUnification.Matrix2KANPauliChain
open InfoGeometry.Algebra.MatrixCyclotomics

def traceDiscriminant (matrix : Mat2) : ℝ :=
  Matrix.trace matrix ^ 2 - 4 * matrix.det

theorem shearRoot_discriminant (parameter : ℝ) :
    traceDiscriminant (shearRoot parameter) = -4 :=
  shearRoot_trace_discriminant parameter

theorem KPart_discriminant (angle : ℝ) :
    traceDiscriminant (KPart angle) = -4 * Real.sin angle ^ 2 := by
  unfold traceDiscriminant
  rw [KPart_det]
  simp only [KPart, Matrix.trace, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  nlinarith [Real.cos_sq_add_sin_sq angle]

theorem KPart_discriminant_neg_iff (angle : ℝ) :
    traceDiscriminant (KPart angle) < 0 ↔ Real.sin angle ≠ 0 := by
  rw [KPart_discriminant]
  constructor
  · intro hnegative hzero
    simp [hzero] at hnegative
  · intro hnonzero
    nlinarith [sq_pos_of_ne_zero hnonzero]

theorem NPart_discriminant (parameter : ℝ) :
    traceDiscriminant (NPart parameter) = 0 := by
  simp [traceDiscriminant, NPart_det, NPart, Matrix.trace, Fin.sum_univ_two]

theorem APart_discriminant (parameter : ℝ) :
    traceDiscriminant (APart parameter) =
      (Real.exp parameter - Real.exp (-parameter)) ^ 2 := by
  have hexp : Real.exp parameter * Real.exp (-parameter) = 1 := by
    rw [← Real.exp_add]
    simp
  unfold traceDiscriminant
  rw [APart_det]
  simp only [APart, Matrix.trace, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  nlinarith

theorem APart_discriminant_pos_iff (parameter : ℝ) :
    0 < traceDiscriminant (APart parameter) ↔ parameter ≠ 0 := by
  rw [APart_discriminant, sq_pos_iff]
  constructor
  · intro hnonzero hzero
    simp [hzero] at hnonzero
  · intro hnonzero hequal
    apply hnonzero
    have hparameter := Real.exp_injective (sub_eq_zero.mp hequal)
    linarith

theorem identity_has_zero_discriminant : traceDiscriminant (1 : Mat2) = 0 := by
  norm_num [traceDiscriminant, Matrix.trace, Fin.sum_univ_two]

end InfoGeometry.Algebra.IwasawaCyclotomics
