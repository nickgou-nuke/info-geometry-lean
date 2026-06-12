import Mathlib

variable {F : Type*} [Field F] (A : F)
variable {A_alg : Type*} [Ring A_alg] [Algebra F A_alg]
variable (ei ej : A_alg)

lemma alg_comm (c : F) (x : A_alg) : x * algebraMap F A_alg c = algebraMap F A_alg c * x :=
  (Algebra.commutes c x).symm

lemma test_simp (hA : A ≠ 0) :
    (algebraMap F A_alg A + algebraMap F A_alg A⁻¹ * ei) *
      (algebraMap F A_alg A + algebraMap F A_alg A⁻¹ * ej) =
      algebraMap F A_alg (A^2) + algebraMap F A_alg 1 * ei +
        algebraMap F A_alg 1 * ej + algebraMap F A_alg (A⁻¹^2) * ei * ej := by
  have hmul : (algebraMap F A_alg A) * (algebraMap F A_alg A⁻¹) = 1 := by
    calc
      (algebraMap F A_alg A) * (algebraMap F A_alg A⁻¹)
        = algebraMap F A_alg (A * A⁻¹) := by rw [map_mul]
      _ = 1 := by simp [hA]
  have hmul' : (algebraMap F A_alg A⁻¹) * (algebraMap F A_alg A) = 1 := by
    calc
      (algebraMap F A_alg A⁻¹) * (algebraMap F A_alg A)
        = algebraMap F A_alg (A⁻¹ * A) := by rw [map_mul]
      _ = 1 := by simp [hA]
  have hAA : (algebraMap F A_alg A) * (algebraMap F A_alg A) = algebraMap F A_alg (A^2) := by
    rw [show (A^2 : F) = A * A by simp [pow_two], map_mul]
  have hAinvAinv :
      (algebraMap F A_alg A⁻¹) * (algebraMap F A_alg A⁻¹) =
        algebraMap F A_alg (A⁻¹^2) := by
    rw [show (A⁻¹ ^ 2 : F) = A⁻¹ * A⁻¹ by simp [pow_two], map_mul]
  have hAEj : (algebraMap F A_alg A) * (algebraMap F A_alg A⁻¹ * ej) = ej := by
    rw [← mul_assoc, hmul]
    simp
  have hEiA : (algebraMap F A_alg A⁻¹ * ei) * (algebraMap F A_alg A) = ei := by
    rw [mul_assoc, alg_comm (c := A), ← mul_assoc, hmul']
    simp
  have hEiEj :
      (algebraMap F A_alg A⁻¹ * ei) * (algebraMap F A_alg A⁻¹ * ej) =
        (algebraMap F A_alg A⁻¹ * algebraMap F A_alg A⁻¹) * (ei * ej) := by
    calc
      (algebraMap F A_alg A⁻¹ * ei) * (algebraMap F A_alg A⁻¹ * ej)
        = algebraMap F A_alg A⁻¹ * (ei * (algebraMap F A_alg A⁻¹ * ej)) := by
            simp [mul_assoc]
      _ = algebraMap F A_alg A⁻¹ * ((ei * algebraMap F A_alg A⁻¹) * ej) := by
            simp [mul_assoc]
      _ = algebraMap F A_alg A⁻¹ * ((algebraMap F A_alg A⁻¹ * ei) * ej) := by
            rw [alg_comm (c := A⁻¹)]
      _ = algebraMap F A_alg A⁻¹ * (algebraMap F A_alg A⁻¹ * (ei * ej)) := by
            simp [mul_assoc]
      _ = (algebraMap F A_alg A⁻¹ * algebraMap F A_alg A⁻¹) * (ei * ej) := by
            simp [mul_assoc]
  rw [add_mul, mul_add, mul_add, hAA, hAEj, hEiA]
  simpa [hAinvAinv, mul_assoc, add_comm, add_left_comm, add_assoc] using hEiEj
