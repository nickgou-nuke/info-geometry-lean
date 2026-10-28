/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.MatrixOperatorIdentities
import InfoGeometry.Canonical.FiniteFrameMaurerCartanPolarSplit
import Mathlib.Algebra.Lie.Cochain
import Mathlib.Algebra.Ring.Action.ConjAct

/-!
# Inner Maurer--Cartan cochains on the full matrix algebra

The native conjugation algebra equivalence defines a complex-linear
one-cochain. Its flatness uses the full Chevalley--Eilenberg differential,
including the bracket of the two directions. No commutation hypothesis on
the directions or faithful adjoint representation is imposed.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.MatrixMaurerCartan

open Matrix
open InfoGeometry.Canonical.FiniteFrameMaurerCartanPolarSplit

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℂ

/-- The left logarithmic inner-derivative cochain, using native conjugation. -/
def maurerCartan (G : Matˣ) : Mat →ₗ[ℂ] Mat :=
  (MulSemiringAction.toAlgEquiv ℂ Mat (ConjAct.toConjAct G⁻¹)).toLinearMap -
    LinearMap.id

/-- The cochain is the displacement of a matrix under inverse conjugation. -/
theorem maurerCartan_apply_conj (G : Matˣ) (H : Mat) :
    maurerCartan G H = (↑(G⁻¹) : Mat) * H * (G : Mat) - H := by
  rfl

/-- The conjugation displacement is the left logarithmic inner derivative. -/
theorem maurerCartan_apply (G : Matˣ) (H : Mat) :
    maurerCartan G H = (↑(G⁻¹) : Mat) * ⁅H, (G : Mat)⁆ := by
  rw [maurerCartan_apply_conj]
  simp only [Ring.lie_def, mul_sub, ← mul_assoc, Units.inv_mul, one_mul]

/-- Adding the cochain recovers the native conjugation algebra equivalence. -/
theorem add_maurerCartan_apply (G : Matˣ) (H : Mat) :
    H + maurerCartan G H =
      MulSemiringAction.toAlgEquiv ℂ Mat (ConjAct.toConjAct G⁻¹) H := by
  change H + (_ - H) = _
  abel

/-- This cochain specializes the existing finite-frame logarithmic derivative. -/
theorem maurerCartan_eq_leftMaurerCartan (G : Matˣ) (H : Mat) :
    maurerCartan G H = leftMaurerCartan G ⁅H, (G : Mat)⁆ :=
  maurerCartan_apply G H

/-- Multiplication by the frame reconstructs its inner derivative. -/
theorem mul_maurerCartan (G : Matˣ) (H : Mat) :
    (G : Mat) * maurerCartan G H = ⁅H, (G : Mat)⁆ := by
  rw [maurerCartan_apply, ← mul_assoc, Units.mul_inv, one_mul]

/-- Associative differentiation of a native matrix unit inverse. -/
theorem lie_units_inv (G : Matˣ) (H : Mat) :
    ⁅H, (↑(G⁻¹) : Mat)⁆ =
      -((↑(G⁻¹) : Mat) * ⁅H, (G : Mat)⁆ * (↑(G⁻¹) : Mat)) := by
  have hsum : ⁅H, (G : Mat)⁆ * (↑(G⁻¹) : Mat) +
      (G : Mat) * ⁅H, (↑(G⁻¹) : Mat)⁆ = 0 := by
    rw [← MatrixOperatorIdentities.lie_mul, Units.mul_inv]
    simp only [Ring.lie_def, mul_one, one_mul, sub_self]
  have hscaled := congrArg (fun X : Mat => (↑(G⁻¹) : Mat) * X) hsum
  simp only [mul_add, ← mul_assoc, Units.inv_mul, one_mul, mul_zero] at hscaled
  exact eq_neg_of_add_eq_zero_right hscaled

/-- The identity frame has zero logarithmic displacement. -/
@[simp] theorem maurerCartan_one : maurerCartan (1 : Matˣ) = 0 := by
  ext H
  simp [maurerCartan_apply_conj]

/-- The kernel of the cochain is precisely the centralizer of its frame. -/
theorem maurerCartan_apply_eq_zero_iff (G : Matˣ) (H : Mat) :
    maurerCartan G H = 0 ↔ Commute (G : Mat) H := by
  rw [maurerCartan_apply_conj, sub_eq_zero]
  exact Units.commute_iff_inv_mul_cancel.symm

/-- Product frames obey the noncommutative left logarithmic cocycle law. -/
theorem maurerCartan_mul (G K : Matˣ) (H : Mat) :
    maurerCartan (G * K) H =
      (↑(K⁻¹) : Mat) * maurerCartan G H * (K : Mat) + maurerCartan K H := by
  have hproduct : ⁅H, ((G * K : Matˣ) : Mat)⁆ =
      productTangent G K ⁅H, (G : Mat)⁆ ⁅H, (K : Mat)⁆ :=
    MatrixOperatorIdentities.lie_mul H (G : Mat) (K : Mat)
  rw [maurerCartan_eq_leftMaurerCartan, hproduct, leftMaurerCartan_mul,
    ← maurerCartan_eq_leftMaurerCartan G H,
    ← maurerCartan_eq_leftMaurerCartan K H]

/-- Inverting the frame negates and conjugates its logarithmic cochain. -/
theorem maurerCartan_inv (G : Matˣ) (H : Mat) :
    maurerCartan G⁻¹ H =
      -((G : Mat) * maurerCartan G H * (↑(G⁻¹) : Mat)) := by
  rw [maurerCartan_apply, inv_inv, lie_units_inv, maurerCartan_apply]
  simp only [mul_neg, mul_assoc]

/-- An inner logarithmic displacement has zero cyclic matrix trace. -/
theorem trace_maurerCartan_zero (G : Matˣ) (H : Mat) :
    trace (maurerCartan G H) = 0 := by
  rw [maurerCartan_apply_conj, trace_sub, trace_mul_cycle]
  simp

/-- Adding the cochain transports the entire noncommutative Lie bracket. -/
theorem maurerCartan_bracket_transport (G : Matˣ) (A B : Mat) :
    ⁅A + maurerCartan G A, B + maurerCartan G B⁆ =
      ⁅A, B⁆ + maurerCartan G ⁅A, B⁆ := by
  rw [add_maurerCartan_apply, add_maurerCartan_apply, add_maurerCartan_apply]
  simp only [Ring.lie_def, map_sub, map_mul]

/-- Full Maurer--Cartan flatness, including the bracket of the directions. -/
theorem maurerCartan_equation (G : Matˣ) (A B : Mat) :
    ⁅A, maurerCartan G B⁆ - ⁅B, maurerCartan G A⁆ -
        maurerCartan G ⁅A, B⁆ + ⁅maurerCartan G A, maurerCartan G B⁆ = 0 := by
  calc
    _ = ⁅A + maurerCartan G A, B + maurerCartan G B⁆ -
        (⁅A, B⁆ + maurerCartan G ⁅A, B⁆) := by
      simp only [Ring.lie_def]
      noncomm_ring
    _ = 0 := by rw [maurerCartan_bracket_transport, sub_self]

/-- Mathlib's native Chevalley--Eilenberg differential equals minus the wedge
commutator, evaluated on arbitrary matrix directions. -/
theorem maurerCartan_differential (G : Matˣ) (A B : Mat) :
    LieModule.Cohomology.d₁₂ ℂ Mat Mat (maurerCartan G) A B =
      -⁅maurerCartan G A, maurerCartan G B⁆ := by
  rw [LieModule.Cohomology.d₁₂_apply_apply]
  exact eq_neg_of_add_eq_zero_left (maurerCartan_equation G A B)

/-- The curl of reconstructed inner derivatives is the derivative along the
direction bracket; it need not vanish when the directions do not commute. -/
theorem reconstructed_curl (G : Matˣ) (A B : Mat) :
    ⁅A, (G : Mat) * maurerCartan G B⁆ -
        ⁅B, (G : Mat) * maurerCartan G A⁆ = ⁅⁅A, B⁆, (G : Mat)⁆ := by
  rw [mul_maurerCartan, mul_maurerCartan]
  exact lie_lie.symm

end InfoGeometry.OperatorAlgebra.MatrixMaurerCartan
