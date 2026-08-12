import Mathlib
import proofs.BogoliubovRindler

open Matrix

noncomputable section

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

/-- Conjugation transports a bilinear metric through an explicitly supplied
    two-sided inverse.  This is the noncommutative core of the q-flow proof. -/
theorem conjugation_pullback_metric
    (D Dinv B J : Matrix4x4)
    (hleft : Dinv * D = 1) (hright : D * Dinv = 1)
    (hB : Bᵀ * J * B = J) :
    (Dinv * B * D)ᵀ * (Dᵀ * J * D) * (Dinv * B * D) = Dᵀ * J * D := by
  have ht : Dinvᵀ * Dᵀ = (1 : Matrix4x4) := by
    rw [← Matrix.transpose_mul, hright, Matrix.transpose_one]
  calc
    (Dinv * B * D)ᵀ * (Dᵀ * J * D) * (Dinv * B * D) =
        Dᵀ * Bᵀ * (Dinvᵀ * Dᵀ) * J * (D * Dinv) * B * D := by
          simp only [Matrix.transpose_mul]
          noncomm_ring
    _ = Dᵀ * Bᵀ * J * B * D := by
          rw [ht, hright]
          simp
    _ = Dᵀ * J * D := by
          calc
            Dᵀ * Bᵀ * J * B * D = Dᵀ * (Bᵀ * J * B) * D := by
              noncomm_ring
            _ = Dᵀ * J * D := by rw [hB]

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
  all_goals field_simp [hq] <;> ring

theorem qDeformedBogoliubovTransform_add (q θ φ : ℝ) (hq : q ≠ 0) :
    qDeformedBogoliubovTransform q (θ + φ) = 
      qDeformedBogoliubovTransform q θ * qDeformedBogoliubovTransform q φ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qDeformedBogoliubovTransform, sectorScaling, bogoliubovTransform, fromBlocks, Matrix.mul_apply, Real.cosh_add, Real.sinh_add]
  all_goals field_simp [hq] <;> ring

theorem qDeformedBogoliubovTransform_neg_mul (q θ : ℝ) (hq : q ≠ 0) :
    qDeformedBogoliubovTransform q (-θ) * qDeformedBogoliubovTransform q θ = 1 := by
  rw [← qDeformedBogoliubovTransform_add q (-θ) θ hq]
  have hz : -θ + θ = 0 := neg_add_cancel θ
  rw [hz, qDeformedBogoliubovTransform_zero q hq]

theorem qDeformedBogoliubov_pullback_metric (q θ : ℝ) (hq : q ≠ 0) :
    (qDeformedBogoliubovTransform q θ)ᵀ * 
      qWeightedKreinMetric q * 
      qDeformedBogoliubovTransform q θ = 
    qWeightedKreinMetric q := by
  have hDleft : sectorScaling q⁻¹ * sectorScaling q = (1 : Matrix4x4) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      simp [sectorScaling, fromBlocks, Matrix.mul_apply, Fin.sum_univ_two,
        inv_mul_cancel₀ hq]
  have hDright : sectorScaling q * sectorScaling q⁻¹ = (1 : Matrix4x4) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      simp [sectorScaling, fromBlocks, Matrix.mul_apply, Fin.sum_univ_two,
        mul_inv_cancel₀ hq]
  have hB : (bogoliubovTransform θ)ᵀ * kreinMetric * bogoliubovTransform θ =
      kreinMetric := by
    dsimp [bogoliubovTransform, kreinMetric]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      simp [fromBlocks, Matrix.mul_apply, Fin.sum_univ_two] <;>
      nlinarith [Real.cosh_sq_sub_sinh_sq θ]
  have hmetric : (sectorScaling q)ᵀ * kreinMetric * sectorScaling q =
      qWeightedKreinMetric q := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      simp [sectorScaling, qWeightedKreinMetric, kreinMetric, fromBlocks,
        Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  rw [qDeformedBogoliubovTransform, ← hmetric]
  exact conjugation_pullback_metric (D := sectorScaling q)
    (Dinv := sectorScaling q⁻¹) (B := bogoliubovTransform θ)
    (J := kreinMetric) hDleft hDright hB

end
