import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Group.TypeTags.Basic

open Matrix

namespace InfoGeometry.Algebra

/-! ### 1. The Klein Bottle Group -/

/-- The fundamental group of the Klein bottle: Γ = ⟨a, b | a b a⁻¹ = b⁻¹⟩.
    Since b generates a normal subgroup isomorphic to ℤ, and a acts by inversion,
    we can model elements canonically as pairs (m, n) ∈ ℤ × ℤ representing a^m b^n.
    We fix the physical conflation: the action is defined by a b = b⁻¹ a. -/
private def intNegAut : MulAut (Multiplicative ℤ) where
  toFun := fun n => n⁻¹
  invFun := fun n => n⁻¹
  left_inv := inv_inv
  right_inv := inv_inv
  map_mul' x y := by
    rw [mul_inv_rev, mul_comm]

/-- The action of the first integer factor on the second is inversion for odd powers. -/
def Z_action : Multiplicative ℤ →* MulAut (Multiplicative ℤ) where
  toFun m := if Even m.toAdd then 1 else intNegAut
  map_one' := by
    ext n
    simp
  map_mul' := by
    intro x y
    ext n
    simp only [toAdd_mul, MulAut.mul_apply, intNegAut]
    by_cases hx : Even x.toAdd <;> by_cases hy : Even y.toAdd
    · have hxy : Even (x.toAdd + y.toAdd) :=
        Int.even_add.mpr ⟨fun _ => hy, fun _ => hx⟩
      simp [hx, hy, hxy]
    · have hxy : ¬Even (x.toAdd + y.toAdd) := by
        intro h
        exact hy ((Int.even_add.mp h).mp hx)
      simp [hx, hy, hxy]
    · have hxy : ¬Even (x.toAdd + y.toAdd) := by
        intro h
        exact hx ((Int.even_add.mp h).mpr hy)
      simp [hx, hy, hxy]
    · have hxy : Even (x.toAdd + y.toAdd) :=
        Int.even_add.mpr ⟨fun h => (hx h).elim, fun h => (hy h).elim⟩
      simp [hx, hy, hxy]

/-- The Klein Bottle group constructed as a semidirect product ℤ ⋉ ℤ. -/
abbrev KleinBottleGroup :=
  SemidirectProduct (Multiplicative ℤ) (Multiplicative ℤ) Z_action

end InfoGeometry.Algebra
