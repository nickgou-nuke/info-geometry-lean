import Mathlib.Tactic
import InfoGeometry.Algebra.CuntzTensorQuotient

/-!
# Conjugation invariance for cyclic Cuntz-valued functionals

The scalar-valued `trace` arguments below are abstract cyclic functionals.
This owner asserts no positivity, normalization, continuity, faithfulness, or
existence theorem for a canonical tracial state on a Cuntz algebra.
-/

namespace InfoGeometry.Algebra.CuntzTraceSocketConjugation

open InfoGeometry.Algebra.CuntzTensorQuotient
open Matrix

variable {n : ℕ}

noncomputable section

def conjug (P M : Matrix (Fin n) (Fin n) ℂ) [Invertible P] :
    Matrix (Fin n) (Fin n) ℂ :=
  ⅟P * M * P

end

section MatrixConjugation

instance inv_conjug (P M : Matrix (Fin n) (Fin n) ℂ) [Invertible P] [Invertible M] :
    Invertible (conjug P M) :=
  have h1 : Invertible (⅟P * M) := Invertible.mul invertibleInvOf (inferInstance)
  Invertible.mul h1 (inferInstance)

theorem invOf_conjug_eq (P M : Matrix (Fin n) (Fin n) ℂ) [Invertible P] [Invertible M] :
    ⅟(conjug P M) = conjug P (⅟M) := by
  have h_right : (conjug P M) * (conjug P (⅟M)) = 1 := by
    unfold conjug
    calc
      (⅟P * M * P) * (⅟P * ⅟M * P) =
          ⅟P * M * (P * ⅟P) * ⅟M * P := by simp only [mul_assoc]
      _ = ⅟P * M * ⅟M * P := by simp only [mul_invOf_self P, mul_one]
      _ = ⅟P * (M * ⅟M) * P := by simp only [mul_assoc]
      _ = ⅟P * P := by simp only [mul_invOf_self M, mul_one]
      _ = 1 := invOf_mul_self P
  exact invOf_eq_right_inv h_right

theorem invOf_eq_inv_matrix (A : Matrix (Fin n) (Fin n) ℂ) [Invertible A] :
    ⅟A = A⁻¹ := by
  have h_mul : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (Matrix.isUnit_det_of_invertible A)
  exact invOf_eq_right_inv h_mul

theorem trace_conjug
    (trace : CuntzAlg n → ℝ)
    (image : Matrix (Fin n) (Fin n) ℂ → CuntzAlg n)
    (image_cyclic : ∀ {A B : Matrix (Fin n) (Fin n) ℂ},
      trace (image (A * B)) = trace (image (B * A)))
    (P M : Matrix (Fin n) (Fin n) ℂ) [Invertible P] :
    trace (image (conjug P M)) = trace (image M) := by
  unfold conjug
  have h_cycle :
      trace (image (⅟P * (M * P))) =
        trace (image ((M * P) * ⅟P)) := by
    exact image_cyclic (A := ⅟P) (B := M * P)
  have h_lhs_norm :
      trace (image (⅟P * M * P)) =
        trace (image (⅟P * (M * P))) := by
    exact congrArg (trace ∘ image) (Matrix.mul_assoc _ _ _)
  have h_rhs_norm :
      trace (image ((M * P) * ⅟P)) = trace (image M) := by
    have h_raw : (M * P) * ⅟P = M := by
      rw [Matrix.mul_assoc, mul_invOf_self, Matrix.mul_one]
    rw [← congrArg image h_raw]
  exact (h_lhs_norm.trans h_cycle).trans h_rhs_norm

theorem conjug_preserves_inv_pair
    (trace : CuntzAlg n → ℝ)
    (image : Matrix (Fin n) (Fin n) ℂ → CuntzAlg n)
    (image_cyclic : ∀ {A B : Matrix (Fin n) (Fin n) ℂ},
      trace (image (A * B)) = trace (image (B * A)))
    (P S T : Matrix (Fin n) (Fin n) ℂ)
    [Invertible P] [Invertible S] [Invertible T] :
    trace (image (S⁻¹ * T)) =
      trace (image ((conjug P S)⁻¹ * conjug P T)) := by
  have h_prod : (conjug P S)⁻¹ * conjug P T = conjug P (S⁻¹ * T) := by
    have h_lhs : (conjug P S)⁻¹ = ⅟P * ⅟S * P := by
      rw [← invOf_eq_inv_matrix (conjug P S)]
      rw [invOf_conjug_eq P S]
      rw [invOf_eq_inv_matrix S]
      rfl
    rw [h_lhs]
    unfold conjug
    calc
      (⅟P * ⅟S * P) * (⅟P * T * P) =
          ⅟P * ⅟S * (P * ⅟P) * T * P := by simp only [mul_assoc]
      _ = ⅟P * ⅟S * T * P := by simp only [mul_invOf_self P, mul_one]
      _ = ⅟P * (⅟S * T) * P := by simp only [mul_assoc]
      _ = ⅟P * (S⁻¹ * T) * P := by rw [invOf_eq_inv_matrix S]
  rw [h_prod]
  exact (trace_conjug trace image image_cyclic P (S⁻¹ * T)).symm

end MatrixConjugation

section OperatorConjugation

noncomputable def opConj
    (ι : CuntzAlg n) [Invertible ι] (X : CuntzAlg n) : CuntzAlg n :=
  ⅟ι * X * ι

theorem opConj_trace_conserved
    (trace : CuntzAlg n → ℝ)
    (trace_cyclic : ∀ X Y : CuntzAlg n, trace (X * Y) = trace (Y * X))
    (ι : CuntzAlg n) [Invertible ι] (X : CuntzAlg n) :
    trace (opConj ι X) = trace X := by
  unfold opConj
  have h1 : trace (⅟ι * X * ι) = trace (ι * (⅟ι * X)) := by
    exact trace_cyclic _ _
  have h2 : ι * (⅟ι * X) = X := by
    rw [← mul_assoc, mul_invOf_self, one_mul]
  rw [h1, h2]

end OperatorConjugation

end InfoGeometry.Algebra.CuntzTraceSocketConjugation
