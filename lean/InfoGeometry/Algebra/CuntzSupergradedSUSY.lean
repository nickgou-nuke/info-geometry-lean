import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import InfoGeometry.Topology.KANWallpaperIsomorphism

/-!
# Cuntz wallpaper supergraded SUSY shadow

This module records the finite supergraded-algebra shadow of the KAN-wallpaper
matrix bridge.

It does not prove physical supersymmetry, super-Poincare representation theory,
or a collider-scale SUSY model.  It proves the finite algebraic pattern:

* an odd generator `Q` is represented by the glide matrix `G`;
* an even generator `P_x` is represented by the translation matrix `T_x`;
* the self-anticommutator of `Q` is twice `P_x`;
* `Q` commutes with `P_x` in this finite projective matrix model.

#### BUCKET 1: CLOSED FINITE THEOREMS

`susy_anticommutator_generates_spacetime`,
`supercharge_commutes_with_momentum_matrix`, and
`supercharge_commutator_with_momentum_zero`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

None.

#### BUCKET 3: OPEN CLOSURE DEBT

The full Cuntz algebra representation, a Hilbert-space supercharge operator,
super-Poincare covariance, and physical supersymmetry remain outside this
finite matrix module.
-/

noncomputable section

namespace InfoGeometry.Algebra.SupergradedSUSY

open Matrix InfoGeometry.Topology.KANWallpaper

/-- The odd generator `Q`, represented by the non-symmorphic glide reflection. -/
def Q : ProjMatrix := G

/-- The even translation generator `P_x`, represented by the unit `x` translation. -/
def P_x : ProjMatrix := T_x

/-- Matrix anticommutator `{A,B} = AB + BA`. -/
def superAnticommutator (A B : ProjMatrix) : ProjMatrix :=
  A * B + B * A

/-- Matrix commutator `[A,B] = AB - BA`. -/
def commutator (A B : ProjMatrix) : ProjMatrix :=
  A * B - B * A

/--
Finite SUSY-shaped anticommutator relation.

The self-anticommutator of the odd glide generator is twice the even
translation generator.
-/
theorem susy_anticommutator_generates_spacetime :
    superAnticommutator Q Q = P_x + P_x := by
  unfold superAnticommutator Q P_x
  rw [glide_squared_is_translation]

/-- The odd glide generator commutes with the even translation matrix. -/
theorem supercharge_commutes_with_momentum_matrix :
    Q * P_x = P_x * Q := by
  unfold Q P_x
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [G, T_x, Matrix.mul_apply, Fin.sum_univ_three]
  norm_num

/-- The matrix commutator of `Q` with `P_x` is zero. -/
theorem supercharge_commutator_with_momentum_zero :
    commutator Q P_x = 0 := by
  unfold commutator
  rw [supercharge_commutes_with_momentum_matrix]
  simp

/--
Backwards-compatible theorem name for the finite commutation statement.
-/
theorem supercharge_commutes_with_momentum :
    Q * P_x - P_x * Q = 0 := by
  simpa [commutator] using supercharge_commutator_with_momentum_zero

end InfoGeometry.Algebra.SupergradedSUSY

end noncomputable section
