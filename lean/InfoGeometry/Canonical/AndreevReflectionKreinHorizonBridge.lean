import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

noncomputable section

open Matrix Complex

namespace AndreevReflectionKreinHorizonBridge

/-- Fundamental Krein Space Metric J Matrix: J = ![![1, 0], ![0, -1]]. -/
def kreinJ : Matrix (Fin 2) (Fin 2) ℂ := ![![1, 0], ![0, -1]]

/-- The displayed diagonal matrix is an involution under native matrix multiplication. -/
theorem krein_J_squared_is_identity : kreinJ * kreinJ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kreinJ, Matrix.mul_apply, Fin.sum_univ_two]

/-- Horizon Null Vector Condition:
    The Hermitian form for diag(1,-1) vanishes on vectors (x,x). -/
def kreinNullNorm (x y : ℂ) : ℂ := star x * x - star y * y

/-- Every vector of the form `(x,x)` is null for the stated Hermitian form. -/
theorem krein_diagonal_is_null (x : ℂ) :
    kreinNullNorm x x = 0 := by
  dsimp [kreinNullNorm]
  ring

namespace Andreev

/-- Nambu particle-hole channel exchange matrix. -/
def particleHoleC : Matrix (Fin 2) (Fin 2) ℂ := ![![0, 1], ![1, 0]]

/-- Exchanging particle-hole channels twice acts as the identity. -/
theorem particle_hole_C_squared_is_identity : particleHoleC * particleHoleC = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [particleHoleC, Matrix.mul_apply, Fin.sum_univ_two]

/-- Two-channel reflection block, with normal and Andreev amplitudes in its first column. -/
def reflectionScatteringMatrix (r_N r_A t_N t_A : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![r_N, t_N; r_A, t_A]

/-- Unitarity of the two-channel scattering block forces the incoming column's
normal and Andreev reflection probabilities to sum to one. This is the
finite-dimensional statement; identifying the block with a physical interface
requires a model of that interface. -/
theorem andreev_reflection_unitarity_conservation
    (r_N r_A t_N t_A : ℂ)
    (hunit : (reflectionScatteringMatrix r_N r_A t_N t_A)ᴴ *
      reflectionScatteringMatrix r_N r_A t_N t_A = 1) :
    Complex.normSq r_N + Complex.normSq r_A = 1 := by
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hunit
  have hcomplex : (Complex.normSq r_N : ℂ) + Complex.normSq r_A = 1 := by
    simpa [reflectionScatteringMatrix, Matrix.conjTranspose_apply,
      Matrix.mul_apply, Fin.sum_univ_two, ← Complex.normSq_eq_conj_mul_self] using hentry
  exact_mod_cast hcomplex

end Andreev

namespace ImageCharge

/-- Image-charge coefficient `-q * (R / d)`. The lemma below only treats the
specialization `d = R`; it does not assert boundary-potential cancellation. -/
def imageChargeMagnitude (q R d : ℝ) : ℝ := -q * (R / d)

/-- At the special parameter value `d = R ≠ 0`, the coefficient is `-q`. -/
theorem boundary_image_charge_compensation (q R : ℝ) (hR : R ≠ 0) :
    imageChargeMagnitude q R R = -q := by
  dsimp [imageChargeMagnitude]
  have h_div : R / R = 1 := div_self hR
  rw [h_div]
  ring

end ImageCharge

end AndreevReflectionKreinHorizonBridge
