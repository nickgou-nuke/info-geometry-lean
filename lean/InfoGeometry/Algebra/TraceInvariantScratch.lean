import InfoGeometry.Algebra.JordanInnerDerivations

namespace InfoGeometry.Algebra

open H3Zorn

noncomputable section

theorem scratch_traceBilin_jordanLmul_assoc (a x y : H3Zorn ℝ) :
    traceBilin (a * x) y = traceBilin x (a * y) := by
  rw [← candidateJordanMul_eq_mul, ← candidateJordanMul_eq_mul]
  simp only [candidateJordanMul, T_outer_formula, traceBilin_smul_left,
    traceBilin_smul_right]
  rw [crossProduct_one, crossProduct_one]
  simp only [traceBilin_sub_left, traceBilin_sub_right, traceBilin_add_left,
    traceBilin_add_right, traceBilin_smul_left, traceBilin_smul_right,
    traceBilin_one, linearTrace_crossProduct]
  rw [traceBilin_crossProduct_assoc a x y]
  rw [traceBilin_symm x (crossProduct a y)]
  rw [traceBilin_crossProduct_assoc a y x]
  rw [crossProduct_symm y x]
  rw [traceBilin_symm (1 : H3Zorn ℝ) y, traceBilin_one]
  rw [traceBilin_symm a x]
  ring

end

end InfoGeometry.Algebra

