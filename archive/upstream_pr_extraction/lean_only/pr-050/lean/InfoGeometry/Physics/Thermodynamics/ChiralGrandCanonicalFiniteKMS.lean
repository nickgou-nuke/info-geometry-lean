import InfoGeometry.Physics.Thermodynamics.ChiralSimilarityKMSBridge
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Finite grand-canonical chiral KMS state

This is the concrete finite-dimensional state layer for the two-sheet
similarity flow.  The state is a normalized matrix trace against the positive
diagonal Gibbs density.  The KMS identity is proved by cyclicity of
`Matrix.trace`; no constant functional or analytic continuation is used.
-/

namespace InfoGeometry.Physics.Thermodynamics

open InfoGeometry.Physics
open Matrix

noncomputable section

/-! The positive normalization factor for the two chiral weights. -/

def chiralGibbsPartition (μ : ℝ) : ℝ :=
  Real.exp μ + Real.exp (-μ)

def chiralGibbsDensity (μ : ℝ) : BdGBlock ℝ :=
  (chiralGibbsPartition μ)⁻¹ • gibbsFactor μ

def chiralGibbsState (μ : ℝ) (X : BdGBlock ℝ) : ℝ :=
  Matrix.trace (chiralGibbsDensity μ * X)

lemma chiralGibbsPartition_pos (μ : ℝ) :
    0 < chiralGibbsPartition μ := by
  unfold chiralGibbsPartition
  exact add_pos (Real.exp_pos _) (Real.exp_pos _)

theorem chiralGibbsDensity_trace (μ : ℝ) :
    Matrix.trace (chiralGibbsDensity μ) = 1 := by
  unfold chiralGibbsDensity chiralGibbsPartition gibbsFactor
  rw [Matrix.trace_smul]
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  have h : Real.exp μ + Real.exp (-μ) ≠ 0 :=
    ne_of_gt (chiralGibbsPartition_pos μ)
  field_simp [h]

theorem chiralGibbsState_one (μ : ℝ) :
    chiralGibbsState μ (1 : BdGBlock ℝ) = 1 := by
  unfold chiralGibbsState
  rw [mul_one, chiralGibbsDensity_trace]

theorem chiralGibbsDensity_posSemidef (μ : ℝ) :
    (chiralGibbsDensity μ).PosSemidef := by
  let c : ℝ := (chiralGibbsPartition μ)⁻¹
  have hc : 0 ≤ c := by
    dsimp [c]
    exact inv_nonneg.mpr (le_of_lt (chiralGibbsPartition_pos μ))
  have hdiag : chiralGibbsDensity μ =
      Matrix.diagonal (fun i : Fin 2 =>
        if i = 0 then c * Real.exp μ else c * Real.exp (-μ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [chiralGibbsDensity, chiralGibbsPartition, gibbsFactor, c,
        Matrix.diagonal]
  rw [hdiag]
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> positivity

theorem chiralGibbsDensity_isHermitian (μ : ℝ) :
    (chiralGibbsDensity μ).IsHermitian :=
  (chiralGibbsDensity_posSemidef μ).isHermitian

theorem chiralGibbsState_nonneg_of_posSemidef
    (μ : ℝ) (X : BdGBlock ℝ) (hX : X.PosSemidef) :
    0 ≤ chiralGibbsState μ X := by
  unfold chiralGibbsState chiralGibbsDensity chiralGibbsPartition
    gibbsFactor
  rw [Matrix.smul_mul, Matrix.trace_smul]
  simp [Matrix.trace, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  change 0 ≤ (Real.exp μ + Real.exp (-μ))⁻¹ *
      (Real.exp μ * X 0 0 + Real.exp (-μ) * X 1 1)
  have h00 : 0 ≤ X 0 0 := hX.diag_nonneg
  have h11 : 0 ≤ X 1 1 := hX.diag_nonneg
  positivity

theorem chiralGibbsState_kms (μ : ℝ) (X Y : BdGBlock ℝ) :
    chiralGibbsState μ (X * chiralSimilarityFlow μ Y) =
      chiralGibbsState μ (Y * X) := by
  unfold chiralGibbsState chiralGibbsDensity chiralSimilarityFlow
  dsimp [chiralGibbsPartition]
  simp only [smul_mul_assoc, Matrix.trace_smul]
  calc
    (Real.exp μ + Real.exp (-μ))⁻¹ •
        Matrix.trace (gibbsFactor μ * (X *
          (gibbsFactor μ * Y * gibbsFactor (-μ)))) =
      (Real.exp μ + Real.exp (-μ))⁻¹ •
        Matrix.trace ((gibbsFactor μ * X * gibbsFactor μ * Y) *
          gibbsFactor (-μ)) := by
            congr 1
            simp only [Matrix.mul_assoc]
    _ = (Real.exp μ + Real.exp (-μ))⁻¹ •
        Matrix.trace (gibbsFactor (-μ) *
          (gibbsFactor μ * X * gibbsFactor μ * Y)) := by
            congr 1
            simpa using Matrix.trace_mul_comm
              (gibbsFactor μ * X * gibbsFactor μ * Y)
              (gibbsFactor (-μ))
    _ = (Real.exp μ + Real.exp (-μ))⁻¹ •
        Matrix.trace ((X * gibbsFactor μ) * Y) := by
            congr 1
            rw [show gibbsFactor (-μ) *
                (gibbsFactor μ * X * gibbsFactor μ * Y) =
                (gibbsFactor (-μ) * gibbsFactor μ) *
                  (X * (gibbsFactor μ * Y)) by
              simp only [Matrix.mul_assoc]]
            rw [gibbsFactor_neg_mul, one_mul]
            simp only [Matrix.mul_assoc]
    _ = (Real.exp μ + Real.exp (-μ))⁻¹ •
        Matrix.trace (Y * (X * gibbsFactor μ)) := by
            congr 1
            simpa using Matrix.trace_mul_comm (X * gibbsFactor μ) Y
    _ = (Real.exp μ + Real.exp (-μ))⁻¹ •
        Matrix.trace (gibbsFactor μ * (Y * X)) := by
            congr 1
            calc
              Matrix.trace (Y * (X * gibbsFactor μ)) =
                  Matrix.trace ((Y * X) * gibbsFactor μ) := by
                    simp only [Matrix.mul_assoc]
              _ = Matrix.trace (gibbsFactor μ * (Y * X)) := by
                    simpa using Matrix.trace_mul_comm (Y * X) (gibbsFactor μ)

end

end InfoGeometry.Physics.Thermodynamics
