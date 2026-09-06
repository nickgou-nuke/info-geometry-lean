import Mathlib.Tactic
import InfoGeometry.Topology.CuntzCantorSpectralTriple
import InfoGeometry.Canonical.F4MixingTopologicalReadout

open InfoGeometry.Topology

variable {Op : Type*} [Ring Op] [StarRing Op]

namespace InfoGeometry.Algebra

/-- The canonical endomorphism (zeta map) for the Kawamura CAR embedding. -/
def kawamuraZeta (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) (x : Op) : Op :=
  CuntzO2Carrier.S_left C * x * star (CuntzO2Carrier.S_left C) - CuntzO2Carrier.S_right C * x * star (CuntzO2Carrier.S_right C)

/-- The canonical endomorphism for O₂. -/
def kawamuraRho (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) (x : Op) : Op :=
  CuntzO2Carrier.S_left C * x * star (CuntzO2Carrier.S_left C) + CuntzO2Carrier.S_right C * x * star (CuntzO2Carrier.S_right C)

@[simp] theorem kawamuraZeta_star (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) (x : Op) :
    star (kawamuraZeta C x) = kawamuraZeta C (star x) := by
  dsimp [kawamuraZeta]
  simp [mul_assoc]

theorem kawamuraZeta_mul_zeta (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) (x y : Op) :
    kawamuraZeta C x * kawamuraZeta C y = kawamuraRho C (x * y) := by
  dsimp [kawamuraZeta, kawamuraRho]
  rw [mul_sub, sub_mul, sub_mul]
  have h1 : CuntzO2Carrier.S_left C * x * star (CuntzO2Carrier.S_left C) * (CuntzO2Carrier.S_left C * y * star (CuntzO2Carrier.S_left C)) = CuntzO2Carrier.S_left C * (x * y) * star (CuntzO2Carrier.S_left C) := by
    calc
      CuntzO2Carrier.S_left C * x * star (CuntzO2Carrier.S_left C) * (CuntzO2Carrier.S_left C * y * star (CuntzO2Carrier.S_left C)) = CuntzO2Carrier.S_left C * x * (star (CuntzO2Carrier.S_left C) * CuntzO2Carrier.S_left C) * y * star (CuntzO2Carrier.S_left C) := by simp [mul_assoc]
      _ = CuntzO2Carrier.S_left C * x * 1 * y * star (CuntzO2Carrier.S_left C) := by rw [CuntzO2Carrier.left_isometry C]
      _ = CuntzO2Carrier.S_left C * (x * y) * star (CuntzO2Carrier.S_left C) := by simp [mul_assoc]
  have h2 : CuntzO2Carrier.S_right C * x * star (CuntzO2Carrier.S_right C) * (CuntzO2Carrier.S_right C * y * star (CuntzO2Carrier.S_right C)) = CuntzO2Carrier.S_right C * (x * y) * star (CuntzO2Carrier.S_right C) := by
    calc
      CuntzO2Carrier.S_right C * x * star (CuntzO2Carrier.S_right C) * (CuntzO2Carrier.S_right C * y * star (CuntzO2Carrier.S_right C)) = CuntzO2Carrier.S_right C * x * (star (CuntzO2Carrier.S_right C) * CuntzO2Carrier.S_right C) * y * star (CuntzO2Carrier.S_right C) := by simp [mul_assoc]
      _ = CuntzO2Carrier.S_right C * x * 1 * y * star (CuntzO2Carrier.S_right C) := by rw [CuntzO2Carrier.right_isometry C]
      _ = CuntzO2Carrier.S_right C * (x * y) * star (CuntzO2Carrier.S_right C) := by simp [mul_assoc]
  have h3 : CuntzO2Carrier.S_left C * x * star (CuntzO2Carrier.S_left C) * (CuntzO2Carrier.S_right C * y * star (CuntzO2Carrier.S_right C)) = 0 := by
    calc
      CuntzO2Carrier.S_left C * x * star (CuntzO2Carrier.S_left C) * (CuntzO2Carrier.S_right C * y * star (CuntzO2Carrier.S_right C)) = CuntzO2Carrier.S_left C * x * (star (CuntzO2Carrier.S_left C) * CuntzO2Carrier.S_right C) * y * star (CuntzO2Carrier.S_right C) := by simp [mul_assoc]
      _ = CuntzO2Carrier.S_left C * x * 0 * y * star (CuntzO2Carrier.S_right C) := by rw [(CuntzO2Carrier.orthogonal_ranges C).1]
      _ = 0 := by simp
  have h4 : CuntzO2Carrier.S_right C * x * star (CuntzO2Carrier.S_right C) * (CuntzO2Carrier.S_left C * y * star (CuntzO2Carrier.S_left C)) = 0 := by
    calc
      CuntzO2Carrier.S_right C * x * star (CuntzO2Carrier.S_right C) * (CuntzO2Carrier.S_left C * y * star (CuntzO2Carrier.S_left C)) = CuntzO2Carrier.S_right C * x * (star (CuntzO2Carrier.S_right C) * CuntzO2Carrier.S_left C) * y * star (CuntzO2Carrier.S_left C) := by simp [mul_assoc]
      _ = CuntzO2Carrier.S_right C * x * 0 * y * star (CuntzO2Carrier.S_left C) := by rw [(CuntzO2Carrier.orthogonal_ranges C).2]
      _ = 0 := by simp
  rw [h1, h2, h3, h4]
  simp [sub_eq_add_neg]

theorem kawamuraRho_add (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) (x y : Op) :
    kawamuraRho C (x + y) = kawamuraRho C x + kawamuraRho C y := by
  dsimp [kawamuraRho]
  simp [mul_add, add_mul]
  abel

theorem kawamuraRho_one (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    kawamuraRho C 1 = 1 := by
  dsimp [kawamuraRho]
  simp only [mul_one]
  exact CuntzO2Carrier.range_sum C

noncomputable def kawamuraCARSequence (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) : ℕ → Op
  | 0 => CuntzO2Carrier.S_left C * star (CuntzO2Carrier.S_right C)
  | n + 1 => kawamuraZeta C (kawamuraCARSequence C n)

theorem kawamuraCAR_base_anticomm (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    let a := kawamuraCARSequence C 0
    a * star a + star a * a = 1 := by
  intro a
  change (CuntzO2Carrier.S_left C * star (CuntzO2Carrier.S_right C)) * star (CuntzO2Carrier.S_left C * star (CuntzO2Carrier.S_right C)) +
         star (CuntzO2Carrier.S_left C * star (CuntzO2Carrier.S_right C)) * (CuntzO2Carrier.S_left C * star (CuntzO2Carrier.S_right C)) = 1
  simp only [star_mul, star_star]
  have h1 : CuntzO2Carrier.S_left C * star (CuntzO2Carrier.S_right C) * (CuntzO2Carrier.S_right C * star (CuntzO2Carrier.S_left C)) = CuntzO2Carrier.S_left C * (star (CuntzO2Carrier.S_right C) * CuntzO2Carrier.S_right C) * star (CuntzO2Carrier.S_left C) := by simp [mul_assoc]
  have h2 : CuntzO2Carrier.S_right C * star (CuntzO2Carrier.S_left C) * (CuntzO2Carrier.S_left C * star (CuntzO2Carrier.S_right C)) = CuntzO2Carrier.S_right C * (star (CuntzO2Carrier.S_left C) * CuntzO2Carrier.S_left C) * star (CuntzO2Carrier.S_right C) := by simp [mul_assoc]
  rw [h1, h2, CuntzO2Carrier.right_isometry C, CuntzO2Carrier.left_isometry C]
  simp only [mul_one]
  exact CuntzO2Carrier.range_sum C

theorem kawamuraCAR_base_nilpotent (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    let a := kawamuraCARSequence C 0
    a * a + a * a = 0 := by
  intro a
  have h : a * a = 0 := by
    change (CuntzO2Carrier.S_left C * star (CuntzO2Carrier.S_right C)) * (CuntzO2Carrier.S_left C * star (CuntzO2Carrier.S_right C)) = 0
    have h1 : (CuntzO2Carrier.S_left C * star (CuntzO2Carrier.S_right C)) * (CuntzO2Carrier.S_left C * star (CuntzO2Carrier.S_right C)) = CuntzO2Carrier.S_left C * (star (CuntzO2Carrier.S_right C) * CuntzO2Carrier.S_left C) * star (CuntzO2Carrier.S_right C) := by simp [mul_assoc]
    rw [h1, (CuntzO2Carrier.orthogonal_ranges C).2]
    simp
  rw [h, add_zero]

theorem kawamuraRho_zero (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    kawamuraRho C 0 = 0 := by
  dsimp [kawamuraRho]
  simp

theorem kawamuraCAR_anticomm (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) (n : ℕ) :
    let a := kawamuraCARSequence C n
    a * star a + star a * a = 1 := by
  induction' n with n ih
  · exact kawamuraCAR_base_anticomm C
  · change kawamuraZeta C (kawamuraCARSequence C n) * star (kawamuraZeta C (kawamuraCARSequence C n)) +
      star (kawamuraZeta C (kawamuraCARSequence C n)) * kawamuraZeta C (kawamuraCARSequence C n) = 1
    rw [kawamuraZeta_star]
    simp only [kawamuraZeta_mul_zeta]
    rw [← kawamuraRho_add, ih]
    exact kawamuraRho_one C

theorem kawamuraCAR_nilpotent (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) (n : ℕ) :
    let a := kawamuraCARSequence C n
    a * a + a * a = 0 := by
  induction' n with n ih
  · exact kawamuraCAR_base_nilpotent C
  · change kawamuraZeta C (kawamuraCARSequence C n) * kawamuraZeta C (kawamuraCARSequence C n) +
      kawamuraZeta C (kawamuraCARSequence C n) * kawamuraZeta C (kawamuraCARSequence C n) = 0
    simp only [kawamuraZeta_mul_zeta]
    rw [← kawamuraRho_add, ih]
    exact kawamuraRho_zero C

theorem kawamuraCAR_creation_self_anticomm (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) (n : ℕ) :
    let a := kawamuraCARSequence C n
    star a * star a + star a * star a = 0 := by
  intro a
  have h := kawamuraCAR_nilpotent C n
  change a * a + a * a = 0 at h
  have hstar := congrArg star h
  simp only [star_add, star_mul, star_zero] at hstar
  exact hstar

end InfoGeometry.Algebra
