import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.SemidirectProduct

open Matrix

namespace InfoGeometry.Algebra

/-! ### 1. The Klein Bottle Group -/

/-- The fundamental group of the Klein bottle: Γ = ⟨a, b | a b a⁻¹ = b⁻¹⟩.
    Since b generates a normal subgroup isomorphic to ℤ, and a acts by inversion,
    we can model elements canonically as pairs (m, n) ∈ ℤ × ℤ representing a^m b^n.
    We fix the physical conflation: the action is defined by a b = b⁻¹ a. -/
def Z_action : ℤ →* MulAut ℤ where
  toFun m :=
    if Even m then MulAut.refl ℤ
    else {
      toFun := fun n => -n
      invFun := fun n => -n
      left_inv := neg_neg
      right_inv := neg_neg
      map_mul' := neg_add
    }
  map_one' := by
    dsimp
    have h : Even (0 : ℤ) := even_zero
    rw [if_pos h]
    rfl
  map_mul' := by
    intro x y
    ext n
    dsimp
    by_cases hx : Even x <;> by_cases hy : Even y
    · have hxy : Even (x + y) := Even.add hx hy
      rw [if_pos hx, if_pos hy, if_pos hxy]
      rfl
    · have hxy : ¬Even (x + y) := by
        intro h
        have h_y : Even y := by
          -- x is even, x+y is even => y is even
          have h1 : Even ((x + y) - x) := Even.sub h hx
          have h2 : (x + y) - x = y := add_sub_cancel_left x y
          rw [← h2]
          exact h1
        exact hy h_y
      rw [if_pos hx, if_neg hy, if_neg hxy]
      rfl
    · have hxy : ¬Even (x + y) := by
        intro h
        have h_x : Even x := by
          have h1 : Even ((x + y) - y) := Even.sub h hy
          have h2 : (x + y) - y = x := add_sub_cancel_right x y
          rw [← h2]
          exact h1
        exact hx h_x
      rw [if_neg hx, if_pos hy, if_neg hxy]
      rfl
    · have hxy : Even (x + y) := by
        -- x odd, y odd => x+y even
        obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp hx
        obtain ⟨l, hl⟩ := Int.not_even_iff_odd.mp hy
        use k + l + 1
        rw [hk, hl]
        ring
      rw [if_neg hx, if_neg hy, if_pos hxy]
      rfl

/-- The Klein Bottle group constructed as a semidirect product ℤ ⋉ ℤ. -/
abbrev KleinBottleGroup := SemidirectProduct ℤ ℤ Z_action

end InfoGeometry.Algebra
