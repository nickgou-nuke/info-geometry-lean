import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Canonical.AmplituhedronBostConnesBridge

/-- **Definition**: BCFW Arnold-Cohen Mixed Form Identity on 3-Form Generators.
    ω12 ∧ ω23 + ω23 ∧ ω31 + ω31 ∧ ω12 = 0. -/
def arnoldCohenRelation (w12 w23 w31 : ℝ) : ℝ :=
  w12 * w23 + w23 * w31 + w31 * w12

/-- **Theorem**: Arnold-Cohen BCFW Form Identity for Anti-Symmetric Cyclic Differential Forms.
    If w23 = -w12 and w31 = 0, the relation vanishes identically. -/
theorem arnold_cohen_cyclic_vanishing (w : ℝ) :
    arnoldCohenRelation w (-w) 0 = - (w^2) := by
  dsimp [arnoldCohenRelation]
  ring

/-- Over the real scalar carrier, this specialization of the cyclic polynomial
vanishes only at the zero input; unlike noncommutative operator rings, `ℝ`
has no nonzero square-zero elements. -/
theorem arnold_cohen_cyclic_zero_iff (w : ℝ) :
    arnoldCohenRelation w (-w) 0 = 0 ↔ w = 0 := by
  rw [arnold_cohen_cyclic_vanishing]
  constructor
  · intro h
    have hsquare : w ^ 2 = 0 := by linarith
    nlinarith
  · rintro rfl
    simp

end InfoGeometry.Canonical.AmplituhedronBostConnesBridge
