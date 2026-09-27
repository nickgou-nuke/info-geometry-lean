import Mathlib.Tactic

namespace SupergradedCartanGrassmannian

variable {A : Type*} [Ring A]

def bracket (x y : A) : A := x * y - y * x

structure GradedMaurerCartanForm (A : Type*) where
  w_n2 : A
  w_n1 : A
  w_0  : A
  w_p1 : A
  w_p2 : A

def grade_zero_curvature (w : GradedMaurerCartanForm A) : A :=
  bracket w.w_n2 w.w_p2 + bracket w.w_n1 w.w_p1 + bracket w.w_0 w.w_0 + bracket w.w_p1 w.w_n1 + bracket w.w_p2 w.w_n2

lemma bracket_antisymm (x y : A) : bracket x y = - bracket y x := by
  dsimp [bracket]
  ring

theorem grade_zero_curvature_expansion (w : GradedMaurerCartanForm A) :
  grade_zero_curvature w = bracket w.w_0 w.w_0 + 2 • bracket w.w_n1 w.w_p1 + 2 • bracket w.w_n2 w.w_p2 := by
  dsimp [grade_zero_curvature, bracket]
  ring

end SupergradedCartanGrassmannian
