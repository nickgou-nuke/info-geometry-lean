import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Real.Basic

/-!
# Split Quadratic Form `(1,1)`

Canonical split quadratic form on `ℝ × ℝ`, reused across Clifford modules.
-/

namespace InfoGeometry.Clifford

/-- Split quadratic form of signature `(1,1)` on `ℝ × ℝ`: `x₁² - x₂²`. -/
noncomputable def splitQ11 : QuadraticForm ℝ (ℝ × ℝ) :=
  QuadraticMap.linMulLin (LinearMap.fst ℝ ℝ ℝ) (LinearMap.fst ℝ ℝ ℝ)
    - QuadraticMap.linMulLin (LinearMap.snd ℝ ℝ ℝ) (LinearMap.snd ℝ ℝ ℝ)

@[simp] lemma splitQ11_apply (x : ℝ × ℝ) :
    splitQ11 x = x.1 * x.1 - x.2 * x.2 := by
  simp [splitQ11]

end InfoGeometry.Clifford
