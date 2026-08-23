import InfoGeometry.Algebra.JordanInnerDerivations

namespace InfoGeometry.Algebra

open H3Zorn

noncomputable section

theorem scratch_traceBilin_jordanLmul_assoc (a x y : H3Zorn ℝ) :
    traceBilin (a * x) y = traceBilin x (a * y) := by
  rw [← candidateJordanMul_eq_mul, ← candidateJordanMul_eq_mul]
  simp only [candidateJordanMul, traceBilin_smul_left, traceBilin_smul_right,
    T_outer_formula]
  rw [traceBilin_crossProduct_assoc]
  rw [traceBilin_crossProduct_assoc]
  rw [traceBilin_symm x y]
  ring

end

end InfoGeometry.Algebra
