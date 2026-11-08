import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import InfoGeometry.Canonical.SouriauKKSForm
import InfoGeometry.Canonical.SouriauCoadjointFisherRaoEquivalence

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open Matrix

namespace SouriauKahler

/-- 1. Complex Structure Matrix J₀ on 𝔤 ≅ ℝ² (90-degree rotation J₀² = -I₂) -/
def complexStructureJ0 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -1;
     1, 0]

/-- 🏆 THEOREM 1: Almost Complex Structure Property: J₀² = -I₂ -/
theorem complexStructureJ0_sq_neg_one :
    complexStructureJ0 * complexStructureJ0 = -1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [complexStructureJ0, mul_apply, Fin.sum_univ_two]

/-- 🏆 THEOREM 2: Anti-Symmetry of the Complex Structure Matrix: J₀ᵀ = -J₀ -/
theorem complexStructureJ0_transpose :
    complexStructureJ0.transpose = -complexStructureJ0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [complexStructureJ0, transpose]

/-- 2. Action of Complex Structure J₀ on Tangent Vectors v ∈ ℝ² -/
def applyJ0 (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  complexStructureJ0 *ᵥ v

/-- 🏆 THEOREM 3: Involution of Complex Structure Action: J₀(J₀(v)) = -v -/
theorem applyJ0_sq (v : Fin 2 → ℝ) :
    applyJ0 (applyJ0 v) = -v := by
  change complexStructureJ0 *ᵥ (complexStructureJ0 *ᵥ v) = -v
  rw [Matrix.mulVec_mulVec]
  rw [complexStructureJ0_sq_neg_one]
  rw [Matrix.neg_mulVec, Matrix.one_mulVec]

/-- 🏆 THEOREM 4: Hermitian Invariance of the Poincaré Metric under Complex Structure J₀:
    g(J₀ X, J₀ Y) = g(X, Y) -/
theorem poincareMetric_j0_hermitian (rho u v : ℝ) (X Y : Fin 2 → ℝ) :
    dotProduct (applyJ0 X) ((SouriauPoincare.poincareFisherMetric rho u v) *ᵥ (applyJ0 Y)) =
      dotProduct X ((SouriauPoincare.poincareFisherMetric rho u v) *ᵥ Y) := by
  dsimp [applyJ0, SouriauPoincare.poincareFisherMetric, dotProduct, mulVec, complexStructureJ0]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero, zero_add, zero_mul]
  ring

/-- 🏆 THEOREM 5: Kähler Compatibility between Poincaré Metric, Complex Structure J₀, and Symplectic Form:
    g(X, J₀ Y) = -g(J₀ X, Y) -/
theorem poincareMetric_j0_skew (rho u v : ℝ) (X Y : Fin 2 → ℝ) :
    dotProduct X ((SouriauPoincare.poincareFisherMetric rho u v) *ᵥ (applyJ0 Y)) =
      - dotProduct (applyJ0 X) ((SouriauPoincare.poincareFisherMetric rho u v) *ᵥ Y) := by
  dsimp [applyJ0, SouriauPoincare.poincareFisherMetric, dotProduct, mulVec, complexStructureJ0]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero, zero_add, zero_mul]
  ring

end SouriauKahler
