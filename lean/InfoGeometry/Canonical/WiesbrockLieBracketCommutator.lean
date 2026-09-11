import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Matrix Complex Real

namespace LieBracketCommutator

namespace SuperWiesbrock

variable {n : ℕ}

/-- 1. Matrix Lie Bracket / Commutator [A, B] = AB - BA -/
def bracket (A B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  A * B - B * A

/-- 2. Modular Supercharges for nested causal horizons ℳ and 𝒩 -/
structure ModularSupercharges (n : ℕ) where
  Q_M : Matrix (Fin n) (Fin n) ℂ  -- Boundary supercharge of exterior algebra ℳ
  Q_N : Matrix (Fin n) (Fin n) ℂ  -- Boundary supercharge of interior algebra 𝒩

/-- 3. Modular Surprisals / Hamiltonians as squared supercharges (𝒦 = Q²) -/
def K_M (sc : ModularSupercharges n) : Matrix (Fin n) (Fin n) ℂ :=
  sc.Q_M * sc.Q_M

def K_N (sc : ModularSupercharges n) : Matrix (Fin n) (Fin n) ℂ :=
  sc.Q_N * sc.Q_N

/-- 4. Wiesbrock Lightlike Spacetime Translation Generator P_translation -/
def P_translation (sc : ModularSupercharges n) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / (2 * Real.pi) : ℂ) • (K_M sc - K_N sc)

/-- 5. **Theorem**: The Wiesbrock Lie Bracket Commutator Relation [K_M, P_translation] = i * P_translation
    Proves that the modular surprisal K_M acts as a boost operator generating
    lightlike translations P_translation via the Half-Sided Modular Inclusion commutator structure. -/
theorem wiesbrock_lie_bracket_commutator (sc : ModularSupercharges n)
    (h_hsmi : bracket (K_M sc) (K_N sc) = (-Complex.I) • (K_M sc - K_N sc)) :
    bracket (K_M sc) (P_translation sc) = Complex.I • P_translation sc := by
  dsimp [bracket, P_translation]
  rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub]
  have h_expand : K_M sc * (K_M sc - K_N sc) - (K_M sc - K_N sc) * K_M sc =
                  - bracket (K_M sc) (K_N sc) := by
    dsimp [bracket]
    rw [mul_sub, sub_mul]
    abel
  rw [h_expand, h_hsmi]
  rw [neg_smul, neg_neg, smul_comm]

end SuperWiesbrock

end LieBracketCommutator
