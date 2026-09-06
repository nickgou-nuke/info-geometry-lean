import Mathlib
import InfoGeometry.Topology.CuntzCantorSpectralTriple

open InfoGeometry.Topology

variable {Op : Type*} [Ring Op] [StarRing Op]

namespace InfoGeometry.Algebra

/-- The canonical endomorphism (zeta map) for the Kawamura CAR embedding.
    ζ(x) = s₁ x s₁* - s₂ x s₂*
-/
def kawamuraZeta (C : CuntzO2Carrier Op) (x : Op) : Op :=
  C.S_left * x * star C.S_left - C.S_right * x * star C.S_right

/-- The canonical endomorphism for O2.
    ρ(x) = s₁ x s₁* + s₂ x s₂*
-/
def kawamuraRho (C : CuntzO2Carrier Op) (x : Op) : Op :=
  C.S_left * x * star C.S_left + C.S_right * x * star C.S_right

@[simp]
theorem kawamuraZeta_star (C : CuntzO2Carrier Op) (x : Op) :
    star (kawamuraZeta C x) = kawamuraZeta C (star x) := by
  dsimp [kawamuraZeta]
  simp [mul_assoc]

theorem kawamuraZeta_mul_zeta (C : CuntzO2Carrier Op) (x y : Op) :
    kawamuraZeta C x * kawamuraZeta C y = kawamuraRho C (x * y) := by
  dsimp [kawamuraZeta, kawamuraRho]
  rw [mul_sub, sub_mul, sub_mul]
  have h1 : C.S_left * x * star C.S_left * (C.S_left * y * star C.S_left) = C.S_left * (x * y) * star C.S_left := by
    calc C.S_left * x * star C.S_left * (C.S_left * y * star C.S_left)
      _ = C.S_left * x * (star C.S_left * C.S_left) * y * star C.S_left := by simp [mul_assoc]
      _ = C.S_left * x * 1 * y * star C.S_left := by rw [C.left_isometry]
      _ = C.S_left * (x * y) * star C.S_left := by simp [mul_assoc]
  have h2 : C.S_right * x * star C.S_right * (C.S_right * y * star C.S_right) = C.S_right * (x * y) * star C.S_right := by
    calc C.S_right * x * star C.S_right * (C.S_right * y * star C.S_right)
      _ = C.S_right * x * (star C.S_right * C.S_right) * y * star C.S_right := by simp [mul_assoc]
      _ = C.S_right * x * 1 * y * star C.S_right := by rw [C.right_isometry]
      _ = C.S_right * (x * y) * star C.S_right := by simp [mul_assoc]
  have h3 : C.S_left * x * star C.S_left * (C.S_right * y * star C.S_right) = 0 := by
    calc C.S_left * x * star C.S_left * (C.S_right * y * star C.S_right)
      _ = C.S_left * x * (star C.S_left * C.S_right) * y * star C.S_right := by simp [mul_assoc]
      _ = C.S_left * x * 0 * y * star C.S_right := by rw [C.orthogonal_ranges.1]
      _ = 0 := by simp
  have h4 : C.S_right * x * star C.S_right * (C.S_left * y * star C.S_left) = 0 := by
    calc C.S_right * x * star C.S_right * (C.S_left * y * star C.S_left)
      _ = C.S_right * x * (star C.S_right * C.S_left) * y * star C.S_left := by simp [mul_assoc]
      _ = C.S_right * x * 0 * y * star C.S_left := by rw [C.orthogonal_ranges.2]
      _ = 0 := by simp
  rw [h1, h2, h3, h4]
  simp [sub_eq_add_neg]

theorem kawamuraRho_add (C : CuntzO2Carrier Op) (x y : Op) :
    kawamuraRho C (x + y) = kawamuraRho C x + kawamuraRho C y := by
  dsimp [kawamuraRho]
  simp [mul_add, add_mul]
  abel

theorem kawamuraRho_one (C : CuntzO2Carrier Op) :
    kawamuraRho C 1 = 1 := by
  dsimp [kawamuraRho]
  simp only [mul_one]
  exact C.range_sum

/-- The recursive fermion system (RFS) mapping ℕ to O₂ operators. -/
noncomputable def kawamuraCARSequence (C : CuntzO2Carrier Op) : ℕ → Op
| 0 => C.S_left * star C.S_right
| n + 1 => kawamuraZeta C (kawamuraCARSequence C n)

/-- Base case for the CAR anticommutation: a₁ a₁* + a₁* a₁ = 1 -/
theorem kawamuraCAR_base_anticomm (C : CuntzO2Carrier Op) :
    let a := kawamuraCARSequence C 0
    a * star a + star a * a = 1 := by
  intro a
  change (C.S_left * star C.S_right) * star (C.S_left * star C.S_right) +
         star (C.S_left * star C.S_right) * (C.S_left * star C.S_right) = 1
  simp only [star_mul, star_star]
  -- We have s₁ s₂* s₂ s₁* + s₂ s₁* s₁ s₂*
  have h1 : C.S_left * star C.S_right * (C.S_right * star C.S_left) = C.S_left * (star C.S_right * C.S_right) * star C.S_left := by
    simp [mul_assoc]
  have h2 : C.S_right * star C.S_left * (C.S_left * star C.S_right) = C.S_right * (star C.S_left * C.S_left) * star C.S_right := by
    simp [mul_assoc]
  rw [h1, h2]
  rw [C.right_isometry, C.left_isometry]
  simp only [mul_one]
  exact C.range_sum

/-- Base case for the CAR anticommutation: a₁ a₁ + a₁ a₁ = 0 -/
theorem kawamuraCAR_base_nilpotent (C : CuntzO2Carrier Op) :
    let a := kawamuraCARSequence C 0
    a * a + a * a = 0 := by
  intro a
  have h : a * a = 0 := by
    change (C.S_left * star C.S_right) * (C.S_left * star C.S_right) = 0
    have h1 : (C.S_left * star C.S_right) * (C.S_left * star C.S_right) = C.S_left * (star C.S_right * C.S_left) * star C.S_right := by
      simp [mul_assoc]
    rw [h1]
    have h2 : star C.S_right * C.S_left = 0 := C.orthogonal_ranges.2
    rw [h2]
    simp
  rw [h, add_zero]

theorem kawamuraRho_zero (C : CuntzO2Carrier Op) :
    kawamuraRho C 0 = 0 := by
  dsimp [kawamuraRho]
  simp

/-- Full induction for the CAR anticommutation: aₙ aₙ* + aₙ* aₙ = 1 -/
theorem kawamuraCAR_anticomm (C : CuntzO2Carrier Op) (n : ℕ) :
    let a := kawamuraCARSequence C n
    a * star a + star a * a = 1 := by
  induction' n with n ih
  · exact kawamuraCAR_base_anticomm C
  · change kawamuraZeta C (kawamuraCARSequence C n) * star (kawamuraZeta C (kawamuraCARSequence C n)) +
           star (kawamuraZeta C (kawamuraCARSequence C n)) * kawamuraZeta C (kawamuraCARSequence C n) = 1
    rw [kawamuraZeta_star]
    simp only [kawamuraZeta_mul_zeta]
    rw [← kawamuraRho_add]
    rw [ih]
    exact kawamuraRho_one C

/-- Full induction for the CAR anticommutation: aₙ aₙ + aₙ aₙ = 0 -/
theorem kawamuraCAR_nilpotent (C : CuntzO2Carrier Op) (n : ℕ) :
    let a := kawamuraCARSequence C n
    a * a + a * a = 0 := by
  induction' n with n ih
  · exact kawamuraCAR_base_nilpotent C
  · change kawamuraZeta C (kawamuraCARSequence C n) * kawamuraZeta C (kawamuraCARSequence C n) +
           kawamuraZeta C (kawamuraCARSequence C n) * kawamuraZeta C (kawamuraCARSequence C n) = 0
    simp only [kawamuraZeta_mul_zeta]
    rw [← kawamuraRho_add]
    rw [ih]
    exact kawamuraRho_zero C

end InfoGeometry.Algebra
