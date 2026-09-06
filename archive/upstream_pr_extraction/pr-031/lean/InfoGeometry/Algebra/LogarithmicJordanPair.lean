import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Tactic.Module

/-!
# Finite logarithmic Jordan pairs

This file isolates the finite-dimensional algebraic certificate underlying a
rank-two logarithmic sector.  It makes no scaling-limit or LCFT claim.

For an endomorphism `H`, eigenvalue `E`, eigenvector `v`, and generalized
eigenvector `w`, the predicate `IsJordanPair H E v w` states

* `v ≠ 0`,
* `H v = E • v`,
* `H w = E • w + v`.

The theorems below prove that the shifted operator `H - E I` kills `v`, sends
`w` to `v`, is square-zero on `w`, and is nonzero on `w`.
-/

namespace InfoGeometry.Algebra.LogarithmicJordanPair

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The spectral shift `H - E I`. -/
def shifted (H : Module.End ℂ V) (E : ℂ) : Module.End ℂ V :=
  H - E • LinearMap.id

/--
An explicit rank-two Jordan pair for `H` at eigenvalue `E`.

This is a proposition on concrete vectors, not a proof-carrying wrapper.
-/
def IsJordanPair (H : Module.End ℂ V) (E : ℂ) (v w : V) : Prop :=
  v ≠ 0 ∧ H v = E • v ∧ H w = E • w + v

/-- An operator has a logarithmic Jordan cell when it admits a rank-two pair. -/
def HasLogarithmicJordanCell (H : Module.End ℂ V) : Prop :=
  ∃ E : ℂ, ∃ v w : V, IsJordanPair H E v w

@[simp]
theorem shifted_apply (H : Module.End ℂ V) (E : ℂ) (x : V) :
    shifted H E x = H x - E • x := by
  simp [shifted]

/-- The shifted operator kills the eigenvector of a Jordan pair. -/
theorem shifted_eigenvector_eq_zero
    {H : Module.End ℂ V} {E : ℂ} {v w : V}
    (h : IsJordanPair H E v w) :
    shifted H E v = 0 := by
  rw [shifted_apply, h.2.1]
  exact sub_self _

/-- The shifted operator maps the generalized vector to the eigenvector. -/
theorem shifted_generalized_eq_eigenvector
    {H : Module.End ℂ V} {E : ℂ} {v w : V}
    (h : IsJordanPair H E v w) :
    shifted H E w = v := by
  rw [shifted_apply, h.2.2]
  module

/-- The square of the shifted operator kills the generalized vector. -/
theorem shifted_sq_generalized_eq_zero
    {H : Module.End ℂ V} {E : ℂ} {v w : V}
    (h : IsJordanPair H E v w) :
    (shifted H E).comp (shifted H E) w = 0 := by
  rw [LinearMap.comp_apply, shifted_generalized_eq_eigenvector h,
    shifted_eigenvector_eq_zero h]

/-- The first shifted action on the generalized vector is nonzero. -/
theorem shifted_generalized_ne_zero
    {H : Module.End ℂ V} {E : ℂ} {v w : V}
    (h : IsJordanPair H E v w) :
    shifted H E w ≠ 0 := by
  rw [shifted_generalized_eq_eigenvector h]
  exact h.1

/--
A Jordan pair gives the exact rank-two minimal-polynomial behavior on its
generalized vector.
-/
theorem rank_two_shifted_nilpotence
    {H : Module.End ℂ V} {E : ℂ} {v w : V}
    (h : IsJordanPair H E v w) :
    (shifted H E).comp (shifted H E) w = 0 ∧ shifted H E w ≠ 0 :=
  ⟨shifted_sq_generalized_eq_zero h, shifted_generalized_ne_zero h⟩

/-- Any explicit Jordan pair produces a logarithmic-cell existence theorem. -/
theorem hasLogarithmicJordanCell_of_isJordanPair
    {H : Module.End ℂ V} {E : ℂ} {v w : V}
    (h : IsJordanPair H E v w) :
    HasLogarithmicJordanCell H :=
  ⟨E, v, w, h⟩

end InfoGeometry.Algebra.LogarithmicJordanPair
