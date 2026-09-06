import Mathlib

noncomputable section

namespace InfoGeometry.Canonical.DrazinSupergradedWeyl

theorem scaledProjector_candidate_mul
    {Obs : Type*} [Semiring Obs] [Algebra ℂ Obs]
    (P : Obs) (lambda : ℂ) (hlambda : lambda ≠ 0)
    (hP : P * P = lambda • P) :
    P * (((lambda)⁻¹ * (lambda)⁻¹) • P) = (lambda)⁻¹ • P ∧
      (((lambda)⁻¹ * (lambda)⁻¹) • P) * P = (lambda)⁻¹ • P := by
  have hscalar : (lambda)⁻¹ * (lambda)⁻¹ * lambda = (lambda)⁻¹ := by
    field_simp [hlambda]
  constructor
  · calc
      P * (((lambda)⁻¹ * (lambda)⁻¹) • P) =
          ((lambda)⁻¹ * (lambda)⁻¹) • (P * P) := by
            rw [mul_smul_comm]
      _ = ((lambda)⁻¹ * (lambda)⁻¹) • (lambda • P) := by rw [hP]
      _ = (((lambda)⁻¹ * (lambda)⁻¹) * lambda) • P := by rw [smul_smul]
      _ = (lambda)⁻¹ • P := by rw [hscalar]
  · calc
      (((lambda)⁻¹ * (lambda)⁻¹) • P) * P =
          ((lambda)⁻¹ * (lambda)⁻¹) • (P * P) := by
            rw [smul_mul_assoc]
      _ = ((lambda)⁻¹ * (lambda)⁻¹) • (lambda • P) := by rw [hP]
      _ = (((lambda)⁻¹ * (lambda)⁻¹) * lambda) • P := by rw [smul_smul]
      _ = (lambda)⁻¹ • P := by rw [hscalar]

end InfoGeometry.Canonical.DrazinSupergradedWeyl
