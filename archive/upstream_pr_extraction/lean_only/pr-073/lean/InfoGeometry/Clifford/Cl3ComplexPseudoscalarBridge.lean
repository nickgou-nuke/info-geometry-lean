import InfoGeometry.Clifford.Cl3ComplexMatrixProduct

open scoped Matrix

namespace InfoGeometry.Clifford.Cl3ComplexPseudoscalarBridge

open InfoGeometry.Clifford.Cl3ComplexMatrixProduct

theorem cl3ToProd_volume :
    cl3ToProd volume =
      (Complex.I • (1 : Mat2C), -Complex.I • (1 : Mat2C)) := by
  rw [volume]
  simp only [map_mul, cl3ToProd_e1, cl3ToProd_e2, cl3ToProd_e3]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [s1, s2, s3, Matrix.smul_apply]

theorem volume_sq_neg_one :
    volume * volume = -(1 : CliffordAlgebra q3) := by
  apply cl3ToProd_injective
  rw [map_mul, cl3ToProd_volume]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply]

end InfoGeometry.Clifford.Cl3ComplexPseudoscalarBridge
