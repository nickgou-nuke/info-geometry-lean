import InfoGeometry.Algebra.CuntzFibonacciBraidInclusion
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.FibonacciGrothendieckRing
import InfoGeometry.Algebra.GoldenMeanShift
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.RingTheory.PowerBasis
import Mathlib.Analysis.Matrix.Spectrum
import InfoGeometry.Algebra.CuntzTensorQuotient
open Matrix
open Complex
open InfoGeometry.Algebra.CuntzTensorQuotient
open CuntzFibonacciBraidInclusion
open InfoGeometry.Algebra.FibonacciGrothendieckRing

namespace Hypothesis1

/-- The golden ratio φ = (1 + √5)/2 -/
noncomputable def φ : ℂ := (1 + Complex.sqrt 5) / 2

/-- The conjugate ψ = (1 - √5)/2 = -φ⁻¹ -/
noncomputable def ψ : ℂ := (1 - Complex.sqrt 5) / 2

/-- The Fibonacci transfer matrix A = [[1, 1], [1, 0]] -/
def A : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, 0]

/-- The canonical embedding ι = matrixToCuntz : M₂(ℂ) → O₂ -/
noncomputable def X : CuntzAlg 2 := matrixToCuntz 2 A

/-- The golden transfer matrix satisfies A² = A + 1. -/
theorem A_sq : A * A = A + 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A, Matrix.one_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The noncommutative lift X = ι(A) satisfies X² = X + 1. -/
theorem X_sq : X * X = X + 1 := by
  dsimp [X]
  rw [← matrixToCuntz_mul, A_sq, InfoGeometry.Algebra.GoldenMeanShift.matrixToCuntz_add, InfoGeometry.Algebra.GoldenMeanShift.matrixToCuntz_one]

end Hypothesis1
