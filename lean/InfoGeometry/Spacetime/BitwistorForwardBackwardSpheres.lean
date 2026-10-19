/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Section 114: Polarization of a Scalar Quadratic Form

This module defines a three-coordinate record and the scalar quadratic form
`q(t, v) = t² - (x² + y² + z²)`. It proves its polarization identity and the
resulting identities for sums of two inputs when each input has `q = 0`.
No bispinor matrix, Riemann sphere, spinor representation, or physical mass/energy
object is constructed; those interpretations remain outside this theorem surface.
-/

namespace InfoGeometry.Spacetime.Bitwistor

variable {R : Type*} [CommRing R]

/-! ### 1. 3D Spatial Carrier and Relativistic Dot Product -/

@[ext]
structure Space3D (R : Type*) where
  x : R
  y : R
  z : R
  deriving DecidableEq, Repr, Inhabited

namespace Space3D

variable {R : Type*} [CommRing R]

def zeroSpace3D : Space3D R := ⟨0, 0, 0⟩

def sampleSpace3DInt : Space3D ℤ := ⟨3, 4, 12⟩

theorem sampleSpace3DInt_ne_zero :
    sampleSpace3DInt ≠ zeroSpace3D := by
  decide

def dot (u v : Space3D R) : R :=
  u.x * v.x + u.y * v.y + u.z * v.z

def sq (u : Space3D R) : R :=
  dot u u

end Space3D

/-! ### 2. Scalar Quadratic Form and Its Null Predicate -/

/-- Scalar quadratic form `t² - (x² + y² + z²)` on the coordinate record. -/
def minkowskiQuadraticCoord (t : R) (v : Space3D R) : R :=
  t^2 - Space3D.sq v

/-- Predicate that the defined scalar quadratic form vanishes. -/
def isNullQuadraticCoord (t : R) (v : Space3D R) : Prop :=
  minkowskiQuadraticCoord t v = 0

/-! ### 3. Coordinatewise Sums -/

/-- Sum of two scalar time coordinates. -/
def sumTimeCoord (t_fwd t_bwd : R) : R :=
  t_fwd + t_bwd

/-- Coordinatewise sum of two three-coordinate records. -/
def sumSpaceCoord (v_fwd v_bwd : Space3D R) : Space3D R :=
  ⟨v_fwd.x + v_bwd.x, v_fwd.y + v_bwd.y, v_fwd.z + v_bwd.z⟩

/-! ### 4. Polarization and Null-Pair Identities -/

/-- Polarization identity for the scalar quadratic form under coordinatewise addition. -/
theorem quadratic_sum_polarization (t_fwd t_bwd : R) (v_fwd v_bwd : Space3D R) :
    minkowskiQuadraticCoord (sumTimeCoord t_fwd t_bwd) (sumSpaceCoord v_fwd v_bwd) =
      minkowskiQuadraticCoord t_fwd v_fwd + minkowskiQuadraticCoord t_bwd v_bwd +
      2 * (t_fwd * t_bwd - Space3D.dot v_fwd v_bwd) := by
  dsimp [minkowskiQuadraticCoord, sumTimeCoord, sumSpaceCoord, Space3D.sq, Space3D.dot]
  ring

/-- If both inputs satisfy the scalar null predicate, the quadratic form of their
coordinatewise sum is the displayed cross term. -/
theorem null_pair_cross_term_identity
    (t_fwd t_bwd : R) (v_fwd v_bwd : Space3D R)
    (h_fwd_null : isNullQuadraticCoord t_fwd v_fwd)
    (h_bwd_null : isNullQuadraticCoord t_bwd v_bwd) :
    minkowskiQuadraticCoord (sumTimeCoord t_fwd t_bwd) (sumSpaceCoord v_fwd v_bwd) =
    2 * (t_fwd * t_bwd - Space3D.dot v_fwd v_bwd) := by
  dsimp [isNullQuadraticCoord] at h_fwd_null h_bwd_null
  rw [quadratic_sum_polarization, h_fwd_null, h_bwd_null]
  ring

/-- For equal scalar time coordinates and opposite spatial coordinates, the sum's
quadratic value is `4 * E²`, assuming the original pair has zero quadratic value. -/
theorem opposite_spatial_sum_quadratic
    (E : R) (v : Space3D R) (h_null : isNullQuadraticCoord E v) :
    minkowskiQuadraticCoord (sumTimeCoord E E) (sumSpaceCoord v ⟨-v.x, -v.y, -v.z⟩) = 4 * E^2 := by
  have h_bwd_null : isNullQuadraticCoord E ⟨-v.x, -v.y, -v.z⟩ := by
    dsimp [isNullQuadraticCoord, minkowskiQuadraticCoord, Space3D.sq, Space3D.dot] at h_null ⊢
    linear_combination h_null
  rw [null_pair_cross_term_identity E E v ⟨-v.x, -v.y, -v.z⟩ h_null h_bwd_null]
  dsimp [isNullQuadraticCoord, minkowskiQuadraticCoord, Space3D.sq, Space3D.dot] at h_null ⊢
  linear_combination -2 * h_null

end InfoGeometry.Spacetime.Bitwistor
