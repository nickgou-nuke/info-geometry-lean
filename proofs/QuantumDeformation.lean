import Mathlib
import proofs.BogoliubovRindler

open Matrix

/-!
# Quantum Deformation of the Rindler Flow

This module explores the introduction of a block scaling parameter `q` 
to the Bogoliubov transformation. 

We mathematically define two versions:
1. `scaledBogoliubovTransform`: A naive block scaling of the second sector.
2. `qDeformedBogoliubovTransform`: A true Lie algebraic deformation via conjugation 
   that preserves a q-weighted Krein metric and the O(2,2) group structure.
-/

/-- Block scaling of the second two-dimensional sector. -/
def sectorScaling (q : ℝ) : Matrix4x4 :=
  fromBlocks 
    (1 : Patch2x2) 0
    0 (q • (1 : Patch2x2))

/-- A Bogoliubov boost preceded by block scaling. -/
def scaledBogoliubovTransform (q θ : ℝ) : Matrix4x4 :=
  bogoliubovTransform θ * sectorScaling q

@[simp]
theorem scaledBogoliubov_mulVec_zero
    (q θ : ℝ) :
    scaledBogoliubovTransform q θ *ᵥ (0 : Spinor) = 0 := by
  exact Matrix.mulVec_zero _

def qWeightedKreinMetric (q : ℝ) : Matrix4x4 :=
  fromBlocks 
    (1 : Patch2x2) 0
    0 (-(q ^ 2) • (1 : Patch2x2))

theorem scaledBogoliubov_pullback_metric
    (q θ : ℝ) :
    (scaledBogoliubovTransform q θ)ᵀ * 
        kreinMetric * 
        scaledBogoliubovTransform q θ = 
      qWeightedKreinMetric q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scaledBogoliubovTransform, qWeightedKreinMetric, kreinMetric, sectorScaling, bogoliubovTransform, fromBlocks, Matrix.mul_apply]
  all_goals {
    have h_cosh_sinh := Real.cosh_sq_sub_sinh_sq θ
    nlinarith
  }

theorem scaledBogoliubov_preserves_standard_metric
    (q θ : ℝ)
    (hq : q ^ 2 = 1) :
    (scaledBogoliubovTransform q θ)ᵀ * 
        kreinMetric * 
        scaledBogoliubovTransform q θ = 
      kreinMetric := by
  rw [scaledBogoliubov_pullback_metric]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qWeightedKreinMetric, kreinMetric, fromBlocks, hq]

/-!
## True q-Deformation (Conjugated Flow)
-/

/-- 
The q-deformed Bogoliubov Transformation.
Constructed by conjugation: B_q(θ) = D_q⁻¹ B(θ) D_q
-/
def qDeformedBogoliubovTransform (q θ : ℝ) : Matrix4x4 :=
  sectorScaling q⁻¹ * bogoliubovTransform θ * sectorScaling q

theorem qDeformedBogoliubovTransform_zero (q : ℝ) (hq : q ≠ 0) :
    qDeformedBogoliubovTransform q 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qDeformedBogoliubovTransform, sectorScaling, bogoliubovTransform, fromBlocks, Matrix.mul_apply]
  all_goals {
    have hinv : q⁻¹ * q = 1 := inv_mul_cancel₀ hq
    have hinv2 : q * q⁻¹ = 1 := mul_inv_cancel₀ hq
    nlinarith
  }

theorem qDeformedBogoliubovTransform_add (q θ φ : ℝ) (hq : q ≠ 0) :
    qDeformedBogoliubovTransform q (θ + φ) = 
      qDeformedBogoliubovTransform q θ * qDeformedBogoliubovTransform q φ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qDeformedBogoliubovTransform, sectorScaling, bogoliubovTransform, fromBlocks, Matrix.mul_apply, Real.cosh_add, Real.sinh_add]
  all_goals {
    have hinv : q⁻¹ * q = 1 := inv_mul_cancel₀ hq
    have hinv2 : q * q⁻¹ = 1 := mul_inv_cancel₀ hq
    nlinarith
  }

theorem qDeformedBogoliubovTransform_neg_mul (q θ : ℝ) (hq : q ≠ 0) :
    qDeformedBogoliubovTransform q (-θ) * qDeformedBogoliubovTransform q θ = 1 := by
  rw [← qDeformedBogoliubovTransform_add q (-θ) θ hq]
  have hz : -θ + θ = 0 := add_left_neg θ
  rw [hz, qDeformedBogoliubovTransform_zero q hq]

theorem qDeformedBogoliubov_pullback_metric (q θ : ℝ) (hq : q ≠ 0) :
    (qDeformedBogoliubovTransform q θ)ᵀ * 
      qWeightedKreinMetric q * 
      qDeformedBogoliubovTransform q θ = 
    qWeightedKreinMetric q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qDeformedBogoliubovTransform, qWeightedKreinMetric, sectorScaling, bogoliubovTransform, fromBlocks, Matrix.mul_apply]
  all_goals {
    have h_cosh_sinh := Real.cosh_sq_sub_sinh_sq θ
    have hinv : q⁻¹ * q = 1 := inv_mul_cancel₀ hq
    have hinv2 : q * q⁻¹ = 1 := mul_inv_cancel₀ hq
    nlinarith
  }
