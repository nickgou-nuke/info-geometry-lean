import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ZornSpinor

/-! Native non-unital non-associative ring laws for the canonical Zorn carrier. -/

noncomputable section

namespace InfoGeometry.Canonical

@[simp] lemma zorn_zero_a : (0 : ZornMatrix ℝ).a = 0 := rfl
@[simp] lemma zorn_zero_b : (0 : ZornMatrix ℝ).b = 0 := rfl
@[simp] lemma zorn_zero_x : (0 : ZornMatrix ℝ).x = 0 := rfl
@[simp] lemma zorn_zero_y : (0 : ZornMatrix ℝ).y = 0 := rfl

@[simp] lemma zorn_add_a (X Y : ZornMatrix ℝ) : (X + Y).a = X.a + Y.a := rfl
@[simp] lemma zorn_add_b (X Y : ZornMatrix ℝ) : (X + Y).b = X.b + Y.b := rfl
@[simp] lemma zorn_add_x (X Y : ZornMatrix ℝ) : (X + Y).x = X.x + Y.x := rfl
@[simp] lemma zorn_add_y (X Y : ZornMatrix ℝ) : (X + Y).y = X.y + Y.y := rfl

lemma zorn_dot_add_left (x y z : Fin 3 → ℝ) :
    ZornMatrix.dot (x + y) z = ZornMatrix.dot x z + ZornMatrix.dot y z := by
  simp [ZornMatrix.dot]
  ring

lemma zorn_dot_add_right (x y z : Fin 3 → ℝ) :
    ZornMatrix.dot x (y + z) = ZornMatrix.dot x y + ZornMatrix.dot x z := by
  simp [ZornMatrix.dot]
  ring

lemma zorn_cross_add_left (x y z : Fin 3 → ℝ) :
    ZornMatrix.cross (x + y) z = ZornMatrix.cross x z + ZornMatrix.cross y z := by
  funext i
  fin_cases i <;> simp [ZornMatrix.cross] <;> ring

lemma zorn_cross_add_right (x y z : Fin 3 → ℝ) :
    ZornMatrix.cross x (y + z) = ZornMatrix.cross x y + ZornMatrix.cross x z := by
  funext i
  fin_cases i <;> simp [ZornMatrix.cross] <;> ring

instance canonicalZornNonUnitalNonAssocRing :
    NonUnitalNonAssocRing (ZornMatrix ℝ) where
  zero_mul := by
    intro x
    cases x
    apply ZornMatrix.ext
    · simp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross]
    · simp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross]
    · funext i
      fin_cases i <;> simp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross]
    · funext i
      fin_cases i <;> simp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross]
  mul_zero := by
    intro x
    cases x
    apply ZornMatrix.ext
    · simp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross]
    · simp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross]
    · funext i
      fin_cases i <;> simp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross]
    · funext i
      fin_cases i <;> simp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross]
  left_distrib := by
    intro x y z
    cases x; cases y; cases z
    apply ZornMatrix.ext
    · simp [ZornMatrix.mul, zorn_dot_add_left, zorn_dot_add_right]
      ring
    · simp [ZornMatrix.mul, zorn_dot_add_left, zorn_dot_add_right]
      ring
    · funext i
      fin_cases i <;> simp [ZornMatrix.mul, zorn_cross_add_left, zorn_cross_add_right] <;> ring
    · funext i
      fin_cases i <;> simp [ZornMatrix.mul, zorn_cross_add_left, zorn_cross_add_right] <;> ring
  right_distrib := by
    intro x y z
    cases x; cases y; cases z
    apply ZornMatrix.ext
    · simp [ZornMatrix.mul, zorn_dot_add_left, zorn_dot_add_right]
      ring
    · simp [ZornMatrix.mul, zorn_dot_add_left, zorn_dot_add_right]
      ring
    · funext i
      fin_cases i <;> simp [ZornMatrix.mul, zorn_cross_add_left, zorn_cross_add_right] <;> ring
    · funext i
      fin_cases i <;> simp [ZornMatrix.mul, zorn_cross_add_left, zorn_cross_add_right] <;> ring

end InfoGeometry.Canonical
