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
# Section 114: Bitwistors, Forward/Backward Riemann Spheres, and the Genesis of Rest Mass
Target: `InfoGeometry/Spacetime/BitwistorForwardBackwardSpheres.lean`

Formalizes:
1. Two null Riemann spheres: Forward (`(t_fwd, v_fwd)`) and Backward (`(t_bwd, v_bwd)`).
2. Their individual masslessness: `bispinorDet t_fwd v_fwd = 0` and `bispinorDet t_bwd v_bwd = 0`.
3. The bitwistor as the superposition of the two spheres: `X_mass = X_fwd + X_bwd`.
4. Mass genesis theorem (`bitwistor_mass_genesis`):
   `bispinorDet (t_fwd + t_bwd) (v_fwd + v_bwd) = 2 * (t_fwd * t_bwd - v_fwd · v_bwd)`.
   Rest mass squared arises strictly from the relativistic cross inner product of the two null cones.
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

/-! ### 2. Van der Waerden Bispinor Determinant and Null Cone Condition -/

/-- Relativistic Minkowski interval (bispinor determinant): `det X = t² - r²`. -/
def bispinorDet (t : R) (v : Space3D R) : R :=
  t^2 - Space3D.sq v

/--
Light-ray predicate (Riemann sphere `CP¹`):
The bispinor determinant vanishes (`bispinorDet t v = 0`, massless field).
-/
def isLightRay (t : R) (v : Space3D R) : Prop :=
  bispinorDet t v = 0

/-! ### 3. Bitwistor Superposition (Forward + Backward Spheres) -/

/-- Time component of the bitwistor (sum of forward and backward energies). -/
def bitwistorTime (t_fwd t_bwd : R) : R :=
  t_fwd + t_bwd

/-- Spatial momentum component of the bitwistor (sum of forward and backward 3-momenta). -/
def bitwistorSpace (v_fwd v_bwd : Space3D R) : Space3D R :=
  ⟨v_fwd.x + v_bwd.x, v_fwd.y + v_bwd.y, v_fwd.z + v_bwd.z⟩

/-! ### 4. Main Theorem: Genesis of Rest Mass from Two Null Spheres -/

/--
General polarization identity for the bitwistor determinant prior to imposing nullity:
`det(X_fwd + X_bwd) = det(X_fwd) + det(X_bwd) + 2 (t_fwd t_bwd - v_fwd · v_bwd)`.
-/
theorem bitwistor_det_polarization (t_fwd t_bwd : R) (v_fwd v_bwd : Space3D R) :
    bispinorDet (bitwistorTime t_fwd t_bwd) (bitwistorSpace v_fwd v_bwd) =
      bispinorDet t_fwd v_fwd + bispinorDet t_bwd v_bwd +
      2 * (t_fwd * t_bwd - Space3D.dot v_fwd v_bwd) := by
  dsimp [bispinorDet, bitwistorTime, bitwistorSpace, Space3D.sq, Space3D.dot]
  ring

/--
Bitwistor mass genesis theorem (Section 114):
When a forward null ray (`bispinorDet t_fwd v_fwd = 0`) and a backward null ray
(`bispinorDet t_bwd v_bwd = 0`) are superposed, the invariant rest mass squared of the
composite bitwistor is generated strictly by their relativistic cross inner product:
`m² = det(X_fwd + X_bwd) = 2 * (t_fwd * t_bwd - v_fwd · v_bwd)`.
-/
theorem bitwistor_mass_genesis
    (t_fwd t_bwd : R) (v_fwd v_bwd : Space3D R)
    (h_fwd_null : isLightRay t_fwd v_fwd)
    (h_bwd_null : isLightRay t_bwd v_bwd) :
    bispinorDet (bitwistorTime t_fwd t_bwd) (bitwistorSpace v_fwd v_bwd) =
    2 * (t_fwd * t_bwd - Space3D.dot v_fwd v_bwd) := by
  dsimp [isLightRay] at h_fwd_null h_bwd_null
  rw [bitwistor_det_polarization, h_fwd_null, h_bwd_null]
  ring

/--
Head-on counter-propagating null spheres (`v_bwd = -v_fwd`, `t_bwd = t_fwd = E`)
generate a rest-frame massive particle with `v_tot = 0` and rest mass squared `m² = 4 E²`.
-/
theorem counter_propagating_null_spheres_rest_mass
    (E : R) (v : Space3D R) (h_null : isLightRay E v) :
    bispinorDet (bitwistorTime E E) (bitwistorSpace v ⟨-v.x, -v.y, -v.z⟩) = 4 * E^2 := by
  have h_bwd_null : isLightRay E ⟨-v.x, -v.y, -v.z⟩ := by
    dsimp [isLightRay, bispinorDet, Space3D.sq, Space3D.dot] at h_null ⊢
    linear_combination h_null
  rw [bitwistor_mass_genesis E E v ⟨-v.x, -v.y, -v.z⟩ h_null h_bwd_null]
  dsimp [isLightRay, bispinorDet, Space3D.sq, Space3D.dot] at h_null ⊢
  linear_combination -2 * h_null

/-! ### 5. Master Synthesis of Section 114 -/

theorem bitwistor_mass_genesis_master_synthesis :
    (∀ (t_fwd t_bwd : R) (v_fwd v_bwd : Space3D R),
      isLightRay t_fwd v_fwd → isLightRay t_bwd v_bwd →
      bispinorDet (bitwistorTime t_fwd t_bwd) (bitwistorSpace v_fwd v_bwd) =
        2 * (t_fwd * t_bwd - Space3D.dot v_fwd v_bwd)) ∧
    (∀ (E : R) (v : Space3D R),
      isLightRay E v →
      bispinorDet (bitwistorTime E E) (bitwistorSpace v ⟨-v.x, -v.y, -v.z⟩) = 4 * E^2) :=
  ⟨bitwistor_mass_genesis, counter_propagating_null_spheres_rest_mass⟩

end InfoGeometry.Spacetime.Bitwistor
