import Mathlib

/-!
# KAN wallpaper finite matrix bridge

This module records a finite projective-matrix bridge between the concrete
`pg` glide matrix and the nilpotent generator of the associated translation.

It does not prove a full KAN decomposition theorem, a black-hole event-horizon
theorem, or a physical crystallographic origin of gravity.  It proves the
finite matrix identities that the downstream algebra may use:

#### BUCKET 1: CLOSED FINITE THEOREMS

`glide_squared_is_translation` and `translation_is_nilpotent_horizon`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

None.

#### BUCKET 3: OPEN CLOSURE DEBT

The full Lie-theoretic KAN decomposition, quotient-space topology, and physical
holographic interpretation remain outside this finite module.
-/

noncomputable section
namespace InfoGeometry.Topology.KANWallpaper

open Matrix

/-- The 3x3 projective matrix representation over the reals. -/
abbrev ProjMatrix := Matrix (Fin 3) (Fin 3) ℝ

/--
The glide reflection operator `G` as a 3x3 projective matrix.

It combines the parity flip `y ↦ -y` with a half-translation `x ↦ x + 1/2`.
-/
def G : ProjMatrix :=
  ![![1,  0, 1/2],
    ![0, -1,  0],
    ![0,  0,  1]]

/-- The unit translation operator `T_x`, sending `x ↦ x + 1`. -/
def T_x : ProjMatrix :=
  ![![1, 0, 1],
    ![0, 1, 0],
    ![0, 0, 1]]

/--
The square of the glide reflection is the unit `x` translation.

This is a finite projective-matrix identity.
-/
theorem glide_squared_is_translation : G * G = T_x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [G, T_x, Matrix.mul_apply, Fin.sum_univ_three]
  norm_num

/-- The nilpotent generator of the translation in this finite model, `n = T_x - I`. -/
def n : ProjMatrix := T_x - 1

/--
The translation generator is strictly square-zero.

This is the finite nilpotent `N`-factor shadow used by downstream bridges.
-/
theorem translation_is_nilpotent_horizon : n * n = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [n, T_x, Matrix.mul_apply, Fin.sum_univ_three]

end InfoGeometry.Topology.KANWallpaper

end noncomputable section
