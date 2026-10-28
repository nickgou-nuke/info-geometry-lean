/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.MatrixMaurerCartan
import InfoGeometry.OperatorAlgebra.IndividuatedCayley
import InfoGeometry.OperatorAlgebra.PeirceChiralGeometry
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Cayley geometry on the full complex matrix algebra

The expression uses Mathlib's matrix inverse. All rational identities carry
the native invertibility condition on the denominator. Skew-adjoint matrices
are proved to satisfy this condition, and their Cayley images are unitary.
The commutator formula keeps the resolvents on both sides of the bracket.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.MatrixCayleyGeometry

open Matrix
open scoped ComplexOrder

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Cayley expression; the geometric domain is `IsUnit (1 + X)`. -/
def cayley (X : Matrix n n ℂ) : Matrix n n ℂ := (1 - X) * (1 + X)⁻¹

theorem cayley_eq_invOf (X : Matrix n n ℂ) [Invertible (1 + X)] :
    cayley X = (1 - X) * ⅟(1 + X) := by
  rw [Matrix.invOf_eq_nonsing_inv]
  rfl

/-- Commutation of the two polynomials is derived, not imposed on inputs. -/
theorem commute_one_sub_one_add (X : Matrix n n ℂ) : Commute (1 - X) (1 + X) := by
  change (1 - X) * (1 + X) = (1 + X) * (1 - X)
  noncomm_ring

theorem commute_cayley (X : Matrix n n ℂ) [Invertible (1 + X)] :
    Commute X (cayley X) := by
  rw [cayley_eq_invOf]
  have hAdd : Commute X (1 + X) := by
    change X * (1 + X) = (1 + X) * X
    noncomm_ring
  have hSub : Commute X (1 - X) := by
    change X * (1 - X) = (1 - X) * X
    noncomm_ring
  exact hSub.mul_right hAdd.invOf_right

theorem one_add_cayley (X : Matrix n n ℂ) [Invertible (1 + X)] :
    1 + cayley X = (2 : ℂ) • ⅟(1 + X) := by
  rw [cayley_eq_invOf]
  calc
    _ = (1 + X) * ⅟(1 + X) + (1 - X) * ⅟(1 + X) := by
      rw [mul_invOf_self]
    _ = _ := by simp only [two_smul]; noncomm_ring

theorem one_sub_cayley (X : Matrix n n ℂ) [Invertible (1 + X)] :
    1 - cayley X = (2 : ℂ) • (X * ⅟(1 + X)) := by
  rw [cayley_eq_invOf]
  calc
    _ = (1 + X) * ⅟(1 + X) - (1 - X) * ⅟(1 + X) := by
      rw [mul_invOf_self]
    _ = _ := by simp only [two_smul]; noncomm_ring

theorem cayley_eq_two_smul_inv_sub_one (X : Matrix n n ℂ)
    [Invertible (1 + X)] : cayley X = (2 : ℂ) • ⅟(1 + X) - 1 := by
  have h := one_add_cayley X
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_comm] using h

@[simp] theorem cayley_zero : cayley (0 : Matrix n n ℂ) = 1 := by
  simp [cayley]

/-- Negation gives the inverse exactly when both denominators are units. -/
theorem cayley_mul_cayley_neg (X : Matrix n n ℂ)
    [Invertible (1 + X)] [Invertible (1 - X)] : cayley X * cayley (-X) = 1 := by
  have hneg : cayley (-X) = (1 + X) * ⅟(1 - X) := by
    simp only [cayley, sub_neg_eq_add, ← sub_eq_add_neg,
      ← Matrix.invOf_eq_nonsing_inv]
  rw [cayley_eq_invOf, hneg]
  calc
    _ = (1 - X) * (⅟(1 + X) * (1 + X)) * ⅟(1 - X) := by
      simp only [mul_assoc]
    _ = 1 := by rw [invOf_mul_self, mul_one, mul_invOf_self]

theorem cayley_neg_mul_cayley (X : Matrix n n ℂ)
    [Invertible (1 + X)] [Invertible (1 - X)] : cayley (-X) * cayley X = 1 := by
  have hneg : cayley (-X) = (1 + X) * ⅟(1 - X) := by
    simp only [cayley, sub_neg_eq_add, ← sub_eq_add_neg,
      ← Matrix.invOf_eq_nonsing_inv]
  rw [cayley_eq_invOf, hneg]
  calc
    _ = (1 + X) * (⅟(1 - X) * (1 - X)) * ⅟(1 + X) := by
      simp only [mul_assoc]
    _ = 1 := by rw [invOf_mul_self, mul_one, mul_invOf_self]

/-- Inversion of an invertible input negates its Cayley coordinate. -/
theorem cayley_units_inv (G : (Matrix n n ℂ)ˣ)
    [Invertible (1 + (G : Matrix n n ℂ))] :
    cayley (↑(G⁻¹) : Matrix n n ℂ) = -cayley (G : Matrix n n ℂ) := by
  have hb : IsUnit (1 + (↑(G⁻¹) : Matrix n n ℂ)) := by
    have he : 1 + (↑(G⁻¹) : Matrix n n ℂ) =
        (↑(G⁻¹) : Matrix n n ℂ) * (1 + (G : Matrix n n ℂ)) := by
      simp only [mul_add, mul_one, Units.inv_mul, add_comm]
    rw [he]
    exact (G⁻¹).isUnit.mul (isUnit_of_invertible _)
  letI := hb.invertible
  have hfactor : (1 + (↑(G⁻¹) : Matrix n n ℂ)) * (G : Matrix n n ℂ) =
      1 + (G : Matrix n n ℂ) := by
    simp only [add_mul, one_mul, Units.inv_mul, add_comm]
  have hi : ⅟(1 + (↑(G⁻¹) : Matrix n n ℂ)) =
      (G : Matrix n n ℂ) * ⅟(1 + (G : Matrix n n ℂ)) :=
    invOf_eq_right_inv (by rw [← mul_assoc, hfactor, mul_invOf_self])
  rw [cayley_eq_invOf, cayley_eq_invOf, hi]
  calc
    _ = ((1 - (↑(G⁻¹) : Matrix n n ℂ)) * (G : Matrix n n ℂ)) *
        ⅟(1 + (G : Matrix n n ℂ)) := by simp only [mul_assoc]
    _ = ((G : Matrix n n ℂ) - 1) * ⅟(1 + (G : Matrix n n ℂ)) := by
      rw [sub_mul, one_mul, Units.inv_mul]
    _ = _ := by noncomm_ring

/-- The two-point resolvent identity retains the order of noncommuting inputs. -/
theorem cayley_sub_cayley (X Y : Matrix n n ℂ)
    [Invertible (1 + X)] [Invertible (1 + Y)] :
    cayley X - cayley Y =
      -(2 : ℂ) • (⅟(1 + X) * (X - Y) * ⅟(1 + Y)) := by
  have hres : ⅟(1 + X) - ⅟(1 + Y) =
      -(⅟(1 + X) * (X - Y) * ⅟(1 + Y)) := by
    calc
      _ = ⅟(1 + X) * ((1 + Y) - (1 + X)) * ⅟(1 + Y) := by
        simp only [mul_sub, sub_mul, mul_assoc, mul_invOf_self, mul_one]
        rw [← mul_assoc, invOf_mul_self, one_mul]
      _ = _ := by noncomm_ring
  rw [cayley_eq_two_smul_inv_sub_one, cayley_eq_two_smul_inv_sub_one]
  calc
    _ = (2 : ℂ) • (⅟(1 + X) - ⅟(1 + Y)) := by
      simp only [two_smul]
      abel
    _ = _ := by rw [hres, smul_neg, neg_smul]

/-- Inverse differentiation supplies the exact two-sided resolvent formula. -/
theorem lie_cayley (H X : Matrix n n ℂ) [Invertible (1 + X)] :
    ⁅H, cayley X⁆ = -(2 : ℂ) • (⅟(1 + X) * ⁅H, X⁆ * ⅟(1 + X)) := by
  have hi := MatrixMaurerCartan.lie_units_inv (unitOfInvertible (1 + X)) H
  change ⁅H, ⅟(1 + X)⁆ = -(⅟(1 + X) * ⁅H, 1 + X⁆ * ⅟(1 + X)) at hi
  have hbr : ⁅H, 1 + X⁆ = ⁅H, X⁆ := by
    simp only [Ring.lie_def]
    noncomm_ring
  rw [hbr] at hi
  rw [cayley_eq_two_smul_inv_sub_one]
  calc
    _ = (2 : ℂ) • ⁅H, ⅟(1 + X)⁆ := by
      simp only [Ring.lie_def, two_smul]
      noncomm_ring
    _ = _ := by rw [hi, smul_neg, neg_smul]

/-- The Cayley chart preserves the entire centralizer, not only X itself. -/
theorem commute_cayley_iff (H X : Matrix n n ℂ) [Invertible (1 + X)] :
    Commute H (cayley X) ↔ Commute H X := by
  change H * cayley X = cayley X * H ↔ H * X = X * H
  rw [← sub_eq_zero, ← sub_eq_zero]
  change ⁅H, cayley X⁆ = 0 ↔ ⁅H, X⁆ = 0
  rw [lie_cayley, smul_eq_zero]
  simp only [neg_ne_zero, OfNat.ofNat_ne_zero, false_or]
  constructor
  · intro h
    have h' := congrArg (fun Y => (1 + X) * Y * (1 + X)) h
    simpa only [mul_assoc, invOf_mul_self, mul_one, mul_zero, zero_mul,
      mul_invOf_self, one_mul] using h'
  · intro h
    rw [h, mul_zero, zero_mul]

/-- A skew-adjoint matrix has both Cayley denominators invertible. -/
theorem isUnit_one_sub_and_one_add_of_skew {X : Matrix n n ℂ}
    (hX : star X = -X) : IsUnit (1 - X) ∧ IsUnit (1 + X) := by
  have hg : (1 + star X * X).PosDef :=
    Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self X)
  have he : (1 - X) * (1 + X) = 1 + star X * X := by
    rw [hX]
    noncomm_ring
  apply (commute_one_sub_one_add X).isUnit_mul_iff.mp
  rw [he]
  exact hg.isUnit

/-- The existing general starred-ring Cayley theorem yields native unitary membership. -/
theorem cayley_mem_unitary_of_skew {X : Matrix n n ℂ} (hX : star X = -X) :
    cayley X ∈ unitary (Matrix n n ℂ) := by
  letI := (isUnit_one_sub_and_one_add_of_skew hX).2.invertible
  let R : IndividuatedCayley.VerifiedUnitaryResolvent (Matrix n n ℂ) X 1 :=
    { denomInv := ⅟(1 + X)
      denom_right := mul_invOf_self _
      denom_left := invOf_mul_self _
      D_phase_linear := by simp [IndividuatedCayley.PhaseLinear]
      D_selfAdjoint := star_one _
      K_skewAdjoint := hX }
  rw [cayley_eq_invOf, Unitary.mem_iff]
  exact R.boundedCayley_is_unitary

/-- Square-zero operators have a polynomial Cayley expression. -/
theorem cayley_of_square_zero {N : Matrix n n ℂ} (hN : N * N = 0) :
    cayley N = 1 - (2 : ℂ) • N := by
  letI : Invertible (1 + N) :=
    { invOf := 1 - N
      invOf_mul_self := by noncomm_ring [hN]
      mul_invOf_self := by noncomm_ring [hN] }
  rw [cayley_eq_invOf]
  change (1 - N) * (1 - N) = 1 - (2 : ℂ) • N
  simp only [two_smul]
  noncomm_ring [hN]

/-- The directed Peirce corner supplies a genuine link from nilpotency to Cayley algebra. -/
theorem cayley_component10 {p : Matrix n n ℂ} (hp : IsIdempotentElem p)
    (A : Matrix n n ℂ) :
    cayley (InfoGeometry.Core.PeirceDecomposition.component10 p A) =
      1 - (2 : ℂ) • InfoGeometry.Core.PeirceDecomposition.component10 p A :=
  cayley_of_square_zero (InfoGeometry.Core.IdempotentCartan.corners_square_zero hp.eq A).1

/-- The finite admissible chart excludes the value minus identity. -/
theorem cayley_ne_neg_one [Nonempty n] (X : Matrix n n ℂ) [Invertible (1 + X)] :
    cayley X ≠ -1 := by
  intro h
  have hi := one_add_cayley X
  rw [h, add_neg_cancel] at hi
  have hz : ⅟(1 + X) = 0 := by
    have hs := (smul_eq_zero.mp hi.symm)
    exact hs.resolve_left (by norm_num)
  have hc := invOf_mul_self (1 + X)
  rw [hz, zero_mul] at hc
  exact zero_ne_one hc

end InfoGeometry.OperatorAlgebra.MatrixCayleyGeometry
