import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace InfoGeometry.EmergentVacuum.KreinMetricStabilizer

variable {Index : Type*} [Fintype Index] [DecidableEq Index]

def metricStabilizer (metric : Matrix Index Index ℂ) :
    Subgroup (Matrix.GeneralLinearGroup Index ℂ) where
  carrier := {transform | (transform : Matrix Index Index ℂ).conjTranspose * metric *
    (transform : Matrix Index Index ℂ) = metric}
  one_mem' := by simp
  mul_mem' := by
    intro first second firstPreserves secondPreserves
    change (first : Matrix Index Index ℂ).conjTranspose * metric * ↑first = metric
      at firstPreserves
    change (second : Matrix Index Index ℂ).conjTranspose * metric * ↑second = metric
      at secondPreserves
    change ((first : Matrix Index Index ℂ) * ↑second).conjTranspose * metric *
      (↑first * ↑second) = metric
    rw [Matrix.conjTranspose_mul]
    calc
      (second : Matrix Index Index ℂ).conjTranspose *
          (first : Matrix Index Index ℂ).conjTranspose * metric * (↑first * ↑second) =
          (second : Matrix Index Index ℂ).conjTranspose *
            ((first : Matrix Index Index ℂ).conjTranspose * metric * ↑first) * ↑second := by
              simp only [mul_assoc]
      _ = metric := by rw [firstPreserves, secondPreserves]
  inv_mem' := by
    intro transform preserves
    change (transform : Matrix Index Index ℂ).conjTranspose * metric * ↑transform = metric
      at preserves
    change (↑transform⁻¹ : Matrix Index Index ℂ).conjTranspose * metric * ↑transform⁻¹ = metric
    have adjointInverse : (↑transform⁻¹ : Matrix Index Index ℂ).conjTranspose *
        (transform : Matrix Index Index ℂ).conjTranspose = 1 := by
      rw [← Matrix.conjTranspose_mul, transform.mul_inv, Matrix.conjTranspose_one]
    calc
      (↑transform⁻¹ : Matrix Index Index ℂ).conjTranspose * metric * ↑transform⁻¹ =
          (↑transform⁻¹ : Matrix Index Index ℂ).conjTranspose *
            ((transform : Matrix Index Index ℂ).conjTranspose * metric * ↑transform) *
              ↑transform⁻¹ := by rw [preserves]
      _ = ((↑transform⁻¹ : Matrix Index Index ℂ).conjTranspose *
          (transform : Matrix Index Index ℂ).conjTranspose) * metric *
            ((transform : Matrix Index Index ℂ) * ↑transform⁻¹) := by
              simp only [mul_assoc]
      _ = metric := by rw [adjointInverse, transform.mul_inv, one_mul, mul_one]

def specialMetricStabilizer (metric : Matrix Index Index ℂ) :
    Subgroup (Matrix.GeneralLinearGroup Index ℂ) :=
  metricStabilizer metric ⊓ (Matrix.GeneralLinearGroup.det (n := Index) (R := ℂ)).ker

theorem mem_specialMetricStabilizer (metric : Matrix Index Index ℂ)
    (transform : Matrix.GeneralLinearGroup Index ℂ) :
    transform ∈ specialMetricStabilizer metric ↔
      (transform : Matrix Index Index ℂ).conjTranspose * metric * ↑transform = metric ∧
        Matrix.det (transform : Matrix Index Index ℂ) = 1 := by
  change (_ ∧ Matrix.GeneralLinearGroup.det transform = 1) ↔ _
  constructor
  · rintro ⟨preserves, determinant⟩
    exact ⟨preserves, congrArg Units.val determinant⟩
  · rintro ⟨preserves, determinant⟩
    exact ⟨preserves, Units.ext determinant⟩

theorem special_le_metricStabilizer (metric : Matrix Index Index ℂ) :
    specialMetricStabilizer metric ≤ metricStabilizer metric := inf_le_left

def splitMetric (size : ℕ) : Matrix (Fin size ⊕ Fin size) (Fin size ⊕ Fin size) ℂ :=
  Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1))

theorem splitMetric_square (size : ℕ) : splitMetric size * splitMetric size = 1 := by
  rw [splitMetric, Matrix.diagonal_mul_diagonal]
  ext row column
  rcases row with row | row <;> rcases column with column | column <;>
    simp [Matrix.diagonal_apply, Matrix.one_apply]

abbrev pseudoUnitary (size : ℕ) := metricStabilizer (splitMetric size)

abbrev specialPseudoUnitary (size : ℕ) := specialMetricStabilizer (splitMetric size)

end InfoGeometry.EmergentVacuum.KreinMetricStabilizer
