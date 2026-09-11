import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.HolyTrinity

/-- The Null Cone Confinement Constraint -/
def is_confined (det_Z : ℚ) : Prop := det_Z = 0
def is_bulk (det_Z : ℚ) : Prop := det_Z ≠ 0

/-- Isolated quarks live exclusively on the null cone -/
theorem quark_confinement (a b : ℚ) (x y : Fin 3 → ℚ) (hq : a = 0 ∧ b = 0 ∧ y = 0) :
  is_confined (a * b - ∑ i, x i * y i) := by
  rcases hq with ⟨ha, hb, hy⟩
  simp [ha, hb, hy, is_confined]

/-- D4 Triality permutes the 8_v, 8_s, 8_c representations -/
inductive D4Rep where
  | Vector
  | Semispinor
  | ConjSemispinor
  deriving DecidableEq, Repr

/-- The canonical generator of the Z/3Z subgroup of S3 triality -/
def triality_shift (rep : D4Rep) : D4Rep :=
  match rep with
  | .Vector => .Semispinor
  | .Semispinor => .ConjSemispinor
  | .ConjSemispinor => .Vector

/-- Triality shift is an automorphism of order 3 -/
theorem triality_order_three (rep : D4Rep) :
  triality_shift (triality_shift (triality_shift rep)) = rep := by
  cases rep <;> rfl

end InfoGeometry.HolyTrinity
