import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.FinCases
import InfoGeometry.Physics.ZornMatrixSU3.Vector3
import sandbox.ZornMatrixCore_subagent

namespace InfoGeometry.Physics.ZornMatrixSU3

theorem test_add_mul (M N P : ZornMatrix) : (M + N) * P = M * P + N * P := by
  ext
  · simp [dotProduct, add_mul, mul_add, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]; ring
  · simp [dotProduct, add_mul, mul_add, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]; ring
  · intro i; fin_cases i <;> simp [crossProduct, add_smul, smul_add, add_mul, mul_add, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;> ring
  · intro i; fin_cases i <;> simp [crossProduct, add_smul, smul_add, add_mul, mul_add, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;> ring

end InfoGeometry.Physics.ZornMatrixSU3
