import InfoGeometry.Clifford.SplitQuaternion

namespace InfoGeometry.Exceptional.CuntzArchimedeanColimit

theorem cross_eq_zero_of_partition {Algebra : Type*} [Ring Algebra]
    (first firstInv second secondInv : Algebra)
    (first_inverse : firstInv * first = 1)
    (second_inverse : secondInv * second = 1)
    (partition : first * firstInv + second * secondInv = 1) :
    firstInv * second = 0 := by
  have cancellation : firstInv + firstInv * second * secondInv = firstInv := by
    calc
      firstInv + firstInv * second * secondInv =
          (firstInv * first) * firstInv + firstInv * second * secondInv := by
        rw [first_inverse, one_mul]
      _ = firstInv * (first * firstInv + second * secondInv) := by
        simp only [mul_add, mul_assoc]
      _ = firstInv := by rw [partition, mul_one]
  have cross_zero : firstInv * second * secondInv = 0 :=
    add_left_cancel (cancellation.trans (add_zero firstInv).symm)
  calc
    firstInv * second = firstInv * second * (secondInv * second) := by
      rw [second_inverse, mul_one]
    _ = (firstInv * second * secondInv) * second := by simp only [mul_assoc]
    _ = 0 := by rw [cross_zero, zero_mul]

theorem cuntz_branches_orthogonal {Algebra : Type*} [Ring Algebra] [StarRing Algebra]
    (first second : Algebra)
    (first_isometry : star first * first = 1)
    (second_isometry : star second * second = 1)
    (partition : first * star first + second * star second = 1) :
    star first * second = 0 ∧ star second * first = 0 := by
  constructor
  · exact cross_eq_zero_of_partition first (star first) second (star second)
      first_isometry second_isometry partition
  · exact cross_eq_zero_of_partition second (star second) first (star first)
      second_isometry first_isometry (by simpa only [add_comm] using partition)

theorem no_normalized_real_trace {Algebra : Type*} [Ring Algebra] [StarRing Algebra]
    (first second : Algebra)
    (first_isometry : star first * first = 1)
    (second_isometry : star second * second = 1)
    (partition : first * star first + second * star second = 1)
    (trace : Algebra →+ ℝ)
    (cyclic : ∀ left right, trace (left * right) = trace (right * left)) :
    trace 1 ≠ 1 := by
  intro normalized
  have relation := congrArg trace partition
  rw [map_add, cyclic first (star first), first_isometry,
    cyclic second (star second), second_isometry, normalized] at relation
  norm_num at relation

open InfoGeometry.Clifford

theorem equal_negative_coordinates_norm (scale : ℝ) :
    norm (⟨0, 0, scale, scale⟩ : SplitQuaternion) = -2 * scale ^ 2 := by
  dsimp [norm]
  ring

theorem equal_negative_coordinates_null_iff (scale : ℝ) :
    norm (⟨0, 0, scale, scale⟩ : SplitQuaternion) = 0 ↔ scale = 0 := by
  rw [equal_negative_coordinates_norm]
  constructor
  · intro equality
    have square_zero : scale ^ 2 = 0 := by linarith
    exact sq_eq_zero_iff.mp square_zero
  · rintro rfl
    norm_num

theorem opposite_signature_coordinates_null (scale : ℝ) :
    norm (⟨0, scale, scale, 0⟩ : SplitQuaternion) = 0 := by
  simp [norm]

theorem opposite_signature_coordinates_square_zero (scale : ℝ) :
    (⟨0, scale, scale, 0⟩ : SplitQuaternion) * ⟨0, scale, scale, 0⟩ = 0 := by
  change sqMul ⟨0, scale, scale, 0⟩ ⟨0, scale, scale, 0⟩ = sqZero
  ext <;> simp [sqMul, sqZero]

theorem centered_square_zero_iff (state : ℝ) :
    (state - 1 / 2) ^ 2 = 0 ↔ state = 1 / 2 := by
  rw [sq_eq_zero_iff, sub_eq_zero]

end InfoGeometry.Exceptional.CuntzArchimedeanColimit
