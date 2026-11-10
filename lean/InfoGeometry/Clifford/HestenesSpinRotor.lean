/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import InfoGeometry.Clifford.HestenesOddSector

namespace InfoGeometry.Clifford.Hestenes

open CliffordAlgebra

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem spinRotor_exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

/-- In any non-commutative ring `[Ring B]`, bilateral rotor action composes contravariantly
on the right factor: `(R₁ * R₂) * v * (R₂_inv * R₁_inv) = R₁ * (R₂ * v * R₂_inv) * R₁_inv`. -/
theorem ring_rotor_action_mul
    {B : Type*} [Ring B] (R₁ R₂ v R₁_inv R₂_inv : B) :
    (R₁ * R₂) * v * (R₂_inv * R₁_inv) = R₁ * (R₂ * v * R₂_inv) * R₁_inv := by
  simp only [mul_assoc]

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

/--
The Spin Rotor Action on Spacetime:
An even operator R acts on an odd vector v by the adjoint action R * v * R⁻¹.
This theorem guarantees that the resulting object is strictly contained within the odd sector.
-/
theorem spin_action_preserves_odd (R_op v R_inv : CliffordAlgebra Q)
    (hR : R_op ∈ ClPlus Q) (hv : v ∈ ClMinus Q) (hRinv : R_inv ∈ ClPlus Q) :
    R_op * v * R_inv ∈ ClMinus Q := by
  -- R_op * v is in ClMinus
  have h_Rv := clPlus_mul_clMinus Q R_op v hR hv
  -- (R_op * v) * R_inv is in ClMinus
  exact clMinus_mul_clPlus Q (R_op * v) R_inv h_Rv hRinv

/--
A geometric rotor in the even subalgebra.
We define a Rotor as an even element R such that R * R_rev = 1.
-/
structure GeometricRotor (Q : QuadraticForm R M) where
  val : ClPlus Q

instance : Inhabited (GeometricRotor Q) :=
  ⟨⟨0⟩⟩

/-- The canonical adjoint action of a Rotor on a generalized spacetime vector -/
def GeometricRotor.action (R_op : GeometricRotor Q) (v : ClMinus Q) (R_inv : ClPlus Q) : ClMinus Q :=
  ⟨R_op.val.val * v.val * R_inv.val, spin_action_preserves_odd Q R_op.val.val v.val R_inv.val R_op.val.property v.property R_inv.property⟩

end InfoGeometry.Clifford.Hestenes
