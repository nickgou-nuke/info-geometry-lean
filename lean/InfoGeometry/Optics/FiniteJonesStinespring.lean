/-
InfoGeometry/Optics/FiniteJonesStinespring.lean

Finite-dimensional Stinespring audit for lossy Jones channels.

This file proves the finite optical conservation identity:

  R† R + V† V = 1
      =>
  1 - R† R = V† V.

The theorem is constructive and contains no physical property socket.
Physical interpretations such as "metal lattice", "heat", or "commutant" are
added in later calibration layers.
-/

import Mathlib.Tactic
import InfoGeometry.Optics.FiniteJonesModel

noncomputable section

namespace InfoGeometry.Optics.FiniteJonesStinespring

open FiniteJonesModel

/-! ## 1. Optical defect and gain -/

/-- Visible optical defect: `1 - R†R`. -/
def opticalDefect
    {Op : Type*} [Ring Op] [StarRing Op]
    (R : Op) : Op :=
  1 - star R * R

/-- Visible intensity: `R†R`. -/
def visibleIntensity
    {Op : Type*} [Ring Op] [StarRing Op]
    (R : Op) : Op :=
  star R * R

/-- Hidden/environment gain: `V†V`. -/
def hiddenGain
    {Op : Type*} [Ring Op] [StarRing Op]
    (V : Op) : Op :=
  star V * V

/-- Hidden environment gain: `V†V`. -/
def environmentGain
    {Op : Type*} [Ring Op] [StarRing Op]
    (V : Op) : Op :=
  hiddenGain V

/-! ## 2. Stinespring isometry pair -/

/--
Finite Stinespring isometry pair.

`R` is the visible optical channel.
`V` is the hidden/environment channel.

The only property is the constructive conservation law
`R†R + V†V = 1`.
-/
abbrev StinespringIsometry
    (Op : Type*) [Ring Op] [StarRing Op] :=
  {p : Op × Op //
    star p.1 * p.1 + star p.2 * p.2 = 1}

namespace StinespringIsometry

variable {Op : Type*} [Ring Op] [StarRing Op]
variable (S : StinespringIsometry Op)

abbrev R : Op := S.1.1

abbrev V : Op := S.1.2

abbrev isometry_eq_one : star S.R * S.R + star S.V * S.V = 1 := S.2

/--
The visible optical defect is exactly hidden gain.
-/
theorem defect_eq_hiddenGain :
    opticalDefect S.R = hiddenGain S.V := by
  dsimp [opticalDefect, hiddenGain]
  calc
    1 - star S.R * S.R
        = (star S.R * S.R + star S.V * S.V) - star S.R * S.R := by
            rw [S.isometry_eq_one]
    _ = star S.V * S.V := by
            abel

/--
Visible optical defect equals hidden environment gain.
-/
theorem defect_eq_environment_gain :
    opticalDefect S.R = environmentGain S.V := by
  dsimp [environmentGain]
  exact S.defect_eq_hiddenGain

/--
If hidden coupling is zero, visible defect is zero.
-/
theorem defect_eq_zero_of_hidden_zero
    (hV : S.V = 0) :
    opticalDefect S.R = 0 := by
  rw [S.defect_eq_hiddenGain]
  dsimp [hiddenGain]
  rw [hV]
  simp

/--
If hidden gain is zero, visible defect is zero.
-/
theorem defect_eq_zero_of_hiddenGain_zero
    (hV : hiddenGain S.V = 0) :
    opticalDefect S.R = 0 := by
  rw [S.defect_eq_hiddenGain]
  exact hV

/--
Visible intensity plus hidden environment gain is ideal.
-/
theorem visibleIntensity_add_environmentGain :
    visibleIntensity S.R + environmentGain S.V = 1 := by
  dsimp [visibleIntensity, environmentGain, hiddenGain]
  exact S.isometry_eq_one

end StinespringIsometry

/-! ## 3. Diagonal lossy mirror -/

/-- Diagonal visible Jones channel: `diag(r_s, r_p)`. -/
def diagonalVisibleChannel
    (rs rp : ℂ) : JonesMat :=
  diagJones rs rp

/-- Diagonal environment leak: `diag(v_s, v_p)`. -/
def diagonalEnvironmentChannel
    (vs vp : ℂ) : JonesMat :=
  diagJones vs vp

/--
For diagonal channels, the isometry law reduces to two scalar equations.
-/
theorem diagonal_left_column_isometry
    (rs rp vs vp : ℂ)
    (hs : star rs * rs + star vs * vs = 1)
    (hp : star rp * rp + star vp * vp = 1) :
    star (diagonalVisibleChannel rs rp) * diagonalVisibleChannel rs rp +
      star (diagonalEnvironmentChannel vs vp) * diagonalEnvironmentChannel vs vp
      =
    1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [diagonalVisibleChannel, diagonalEnvironmentChannel, diagJones,
      Matrix.mul_apply] using hs
  · simp [diagonalVisibleChannel, diagonalEnvironmentChannel, diagJones,
      Matrix.mul_apply]
  · simp [diagonalVisibleChannel, diagonalEnvironmentChannel, diagJones,
      Matrix.mul_apply]
  · simpa [diagonalVisibleChannel, diagonalEnvironmentChannel, diagJones,
      Matrix.mul_apply] using hp

/--
Diagonal lossy mirror as a finite Stinespring pair.
-/
def diagonalStinespringIsometry
    (rs rp vs vp : ℂ)
    (hs : star rs * rs + star vs * vs = 1)
    (hp : star rp * rp + star vp * vp = 1) :
    StinespringIsometry JonesMat :=
  ⟨⟨diagonalVisibleChannel rs rp, diagonalEnvironmentChannel vs vp⟩,
    diagonal_left_column_isometry rs rp vs vp hs hp⟩

/--
For a diagonal lossy mirror, visible defect equals hidden gain.
-/
theorem diagonal_defect_eq_environment_gain
    (rs rp vs vp : ℂ)
    (hs : star rs * rs + star vs * vs = 1)
    (hp : star rp * rp + star vp * vp = 1) :
    opticalDefect (diagonalVisibleChannel rs rp) =
      environmentGain (diagonalEnvironmentChannel vs vp) :=
  (diagonalStinespringIsometry rs rp vs vp hs hp).defect_eq_environment_gain

/-! ## 4. Jones specialization -/

/-- Finite Jones Stinespring isometry. -/
abbrev JonesStinespringIsometry :=
  StinespringIsometry JonesMat

end InfoGeometry.Optics.FiniteJonesStinespring
