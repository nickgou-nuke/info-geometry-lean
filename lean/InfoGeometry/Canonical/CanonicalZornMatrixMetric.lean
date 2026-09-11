import InfoGeometry.Algebra.SplitMetricSpace
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CanonicalZornFiveGradedClosure
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Data.Matrix.Basis

namespace CanonicalZornFiveGradedClosure

noncomputable section

open scoped BigOperators

def tracePairing : ConformalMatrix → ConformalMatrix → ℂ :=
  fun A B => Matrix.trace (A * B)

theorem tracePairing_add_left (A B C : ConformalMatrix) :
    tracePairing (A + B) C = tracePairing A C + tracePairing B C := by
  simp [tracePairing, add_mul, Matrix.trace_add]

theorem tracePairing_smul_left (c : ℂ) (A B : ConformalMatrix) :
    tracePairing (c • A) B = c • tracePairing A B := by
  simp [tracePairing, Matrix.smul_mul, Matrix.trace_smul]

theorem tracePairing_add_right (A B C : ConformalMatrix) :
    tracePairing A (B + C) = tracePairing A B + tracePairing A C := by
  simp [tracePairing, mul_add, Matrix.trace_add]

theorem tracePairing_smul_right (c : ℂ) (A B : ConformalMatrix) :
    tracePairing A (c • B) = c • tracePairing A B := by
  simp [tracePairing, mul_smul, Matrix.trace_smul]

theorem tracePairing_symm (A B : ConformalMatrix) :
    tracePairing A B = tracePairing B A := by
  exact Matrix.trace_mul_comm A B

def canonicalZornMetric : InfoGeometry.Algebra.SplitMetricSpace ℂ where
  V := ConformalMatrix
  beta := LinearMap.mk₂ ℂ tracePairing
    tracePairing_add_left tracePairing_smul_left
    tracePairing_add_right tracePairing_smul_right
  beta_symm := ⟨tracePairing_symm⟩
  beta_nondegenerate := by
    constructor
    · intro A hA
      apply (Matrix.ext_iff_trace_mul_right).2
      intro B
      simpa [tracePairing] using hA B
    · intro A hA
      apply (Matrix.ext_iff_trace_mul_left).2
      intro B
      simpa [tracePairing] using hA B

theorem conformalMatrix_finrank : Module.finrank ℂ ConformalMatrix = 100 := by
  rw [Module.finrank_matrix]
  simp only [Module.finrank_self]
  have hcard : Fintype.card ConformalIndex = 10 := by
    classical
    change (1 + 8 + 1) = 10
    norm_num
  rw [hcard]

end
end CanonicalZornFiveGradedClosure
