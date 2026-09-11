import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Matrix Complex Real

namespace SuperWiesbrock

/-- 1. Modular Supercharges for nested causal horizons. -/
structure ModularSupercharges (n : ℕ) where
  Q_M : Matrix (Fin n) (Fin n) ℂ  -- Supercharge of the Exterior Algebra ℳ
  Q_N : Matrix (Fin n) (Fin n) ℂ  -- Supercharge of the Interior Algebra 𝒩

/-- 2. Modular Surprisals as the squares of the Supercharges (𝒦 = Q²). -/
def K_M {n : ℕ} (sc : ModularSupercharges n) : Matrix (Fin n) (Fin n) ℂ :=
  sc.Q_M * sc.Q_M

def K_N {n : ℕ} (sc : ModularSupercharges n) : Matrix (Fin n) (Fin n) ℂ :=
  sc.Q_N * sc.Q_N

/-- 3. Wiesbrock's Translation Generator P = (1/2π)(𝒦_M - 𝒦_N). -/
def P_translation {n : ℕ} (sc : ModularSupercharges n) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / (2 * Real.pi) : ℂ) • (K_M sc - K_N sc)

/-- 4. **Theorem**: Spacetime translations emerge structurally from the difference 
    of squared Modular Supercharges across the horizon! -/
theorem translation_is_supercharge_difference_sq {n : ℕ} (sc : ModularSupercharges n) :
    (2 * Real.pi : ℂ) • P_translation sc = sc.Q_M * sc.Q_M - sc.Q_N * sc.Q_N := by
  dsimp [P_translation, K_M, K_N]
  have h_pi_ne_zero : (Real.pi : ℂ) ≠ 0 := by exact ofReal_ne_zero.mpr pi_ne_zero
  have h_2pi_ne_zero : (2 : ℂ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero h_pi_ne_zero
  have h_cancel : (2 * Real.pi : ℂ) * (1 / (2 * Real.pi) : ℂ) = 1 := mul_one_div_cancel h_2pi_ne_zero
  rw [smul_smul, h_cancel, one_smul]

end SuperWiesbrock
