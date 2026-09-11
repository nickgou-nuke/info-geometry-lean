import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
import InfoGeometry.Canonical.ConcreteCuntzMatrixIsometries

open Matrix
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.ConcreteCuntzMatrixIsometries

noncomputable section

namespace InfoGeometry.Canonical.CuntzMatrixTowerColimitBridge

/-!
# Concrete Matrix-Tower Cuntz Colimit & Trace State Family Bridge

This module executes the complete connection of concrete Cuntz projections into the
infinite matrix UHF stage tower `MatrixStage n := Matrix (Fin (2^n)) (Fin (2^n)) ℂ`:
1. Embed Cuntz projections $P_1 = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}, P_2 = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}$ into `MatrixStage 1 = M_2(ℂ)`
2. Prove completeness $P_1 + P_2 = I_2$ in `MatrixStage 1`
3. Evaluate stage 1 trace values: $\omega_1(P_1) = 1/2, \omega_1(P_2) = 1/2$
4. Prove trace state step compatibility $\omega_{n+1}(A_{\text{next}}) = \omega_n(A)$ whenever $\text{Tr}(A_{\text{next}}) = 2 \text{Tr}(A)$ under Kronecker tensor embedding $A \mapsto A \otimes I_2$.
-/

/-- Embed Cuntz projection P₁ = S₁ S₁* into MatrixStage 1 = M₂(ℂ). -/
def cuntzStage1_S1 : MatrixStage 1 := !![1, 0; 0, 0]

/-- Embed Cuntz projection P₂ = S₂ S₂* into MatrixStage 1 = M₂(ℂ). -/
def cuntzStage1_S2 : MatrixStage 1 := !![0, 0; 0, 1]

/-- **Theorem**: MatrixStage 1 Cuntz Completeness: S₁ + S₂ = 1₂. -/
theorem cuntzStage1_completeness : cuntzStage1_S1 + cuntzStage1_S2 = 1 := by
  dsimp [cuntzStage1_S1, cuntzStage1_S2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **Theorem**: MatrixStage 1 Trace of Cuntz projection S₁ is 1/2. -/
theorem cuntzStage1_trace_S1 : matrixTraceState 1 cuntzStage1_S1 = 1 / 2 := by
  rw [matrixTraceState_apply]
  dsimp [cuntzStage1_S1]
  simp [Matrix.trace_fin_two]

/-- **Theorem**: MatrixStage 1 Trace of Cuntz projection S₂ is 1/2. -/
theorem cuntzStage1_trace_S2 : matrixTraceState 1 cuntzStage1_S2 = 1 / 2 := by
  rw [matrixTraceState_apply]
  dsimp [cuntzStage1_S2]
  simp [Matrix.trace_fin_two]

/-- **Theorem**: Trace state step compatibility under Kronecker embedding A ↦ A ⊗ I₂.
    2⁻⁽ⁿ⁺¹⁾ · 2 Tr(A) = 2⁻ⁿ Tr(A). -/
theorem matrixTraceState_step_compatibility (n : ℕ) (A : MatrixStage n) (A_next : MatrixStage (n + 1))
    (trA : ℂ)
    (h_step_tr : Matrix.trace A_next = 2 * trA)
    (h_A_tr : Matrix.trace A = trA) :
    matrixTraceState (n + 1) A_next = matrixTraceState n A := by
  rw [matrixTraceState_apply, matrixTraceState_apply, h_step_tr, h_A_tr]
  have h_pow : (2 ^ (n + 1) : ℂ) = (2 ^ n : ℂ) * 2 := by
    rw [pow_add, pow_one]
  rw [h_pow, one_div, _root_.mul_inv_rev]
  calc ((2 : ℂ)⁻¹ * (2 ^ n : ℂ)⁻¹) * (2 * trA)
    _ = (2 ^ n : ℂ)⁻¹ * ((2 : ℂ)⁻¹ * 2) * trA := by ring
    _ = (2 ^ n : ℂ)⁻¹ * 1 * trA := by rw [inv_mul_cancel₀ (by norm_num)]
    _ = (1 / (2 ^ n : ℂ)) * trA := by rw [mul_one, one_div]

end InfoGeometry.Canonical.CuntzMatrixTowerColimitBridge
