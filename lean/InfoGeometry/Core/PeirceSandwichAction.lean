/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.SquareZeroSandwich
import InfoGeometry.Core.PeirceRotor

/-! # Peirce geometry and normalized sandwich actions

Opposing corners supply square-zero inputs. Reflexivity is an additional
hypothesis only in the normalized section. The supported operators remain
in the full matrix algebra; no diagonal or scalar carrier replaces them.
-/
namespace InfoGeometry.Core.PeirceSandwichAction

open Matrix InfoGeometry.Core.SquareZeroSandwich
open InfoGeometry.Core.PeirceDecomposition InfoGeometry.Core.DualSeedPeirce
open InfoGeometry.Core.PeirceRotor InfoGeometry.Core.DiracSuperalgebra
open InfoGeometry.Singular.MoorePenrose

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- Opposing Peirce corners give the corrected sum action without reflexivity. -/
theorem dissipator_opposing_corners {P : Matrix n n R} (hp : P * P = P)
    (A B : Matrix n n R) :
    symmDissipator (component10 P A) (component01 P B)
      (component10 P A + component01 P B) =
      -((2 : R) • ((component10 P A * component01 P B +
        component01 P B * component10 P A) * (component10 P A + component01 P B))) := by
  exact dissipator_add
    (peirce10_mul_peirce10_eq_zero P hp (component10_mem P A) (component10_mem P A))
    (peirce01_mul_peirce01_eq_zero P hp (component01_mem P B) (component01_mem P B))

variable {X Y : Matrix n n R}

/-- Reflexivity normalizes multiplication of the sum by the support. -/
theorem support_mul_add (h : IsDualSeedPair X Y) :
    (X * Y + Y * X) * (X + Y) = X + Y := by
  change (polePlus X Y + poleMinus X Y) * (X + Y) = X + Y
  simp only [add_mul, mul_add, h.pd, h.pb, h.qd, h.qb, add_zero, zero_add]

theorem support_mul_sub (h : IsDualSeedPair X Y) :
    (X * Y + Y * X) * (X - Y) = X - Y := by
  change (polePlus X Y + poleMinus X Y) * (X - Y) = X - Y
  simp only [add_mul, mul_sub, h.pd, h.pb, h.qd, h.qb, sub_zero, zero_sub]
  abel

theorem support_mul_commutator (h : IsDualSeedPair X Y) :
    (X * Y + Y * X) * (X * Y - Y * X) = X * Y - Y * X := by
  change (polePlus X Y + poleMinus X Y) *
    (polePlus X Y - poleMinus X Y) = polePlus X Y - poleMinus X Y
  simp only [add_mul, mul_sub, h.pp, h.pq, h.qp, h.qq, sub_zero, zero_sub]
  abel

/-- The sum has coefficient -2, rather than the claimed zero action. -/
theorem dissipator_add_of_reflexive (h : IsDualSeedPair X Y) :
    symmDissipator X Y (X + Y) = -((2 : R) • (X + Y)) := by
  rw [dissipator_add h.d_sq h.b_sq, support_mul_add h]

/-- The difference also has coefficient -2, rather than the claimed -4. -/
theorem dissipator_sub_of_reflexive (h : IsDualSeedPair X Y) :
    symmDissipator X Y (X - Y) = -((2 : R) • (X - Y)) := by
  rw [dissipator_sub h.d_sq h.b_sq, support_mul_sub h]

theorem dissipator_commutator_of_reflexive (h : IsDualSeedPair X Y) :
    symmDissipator X Y (X * Y - Y * X) = -((4 : R) • (X * Y - Y * X)) := by
  rw [dissipator_commutator h.d_sq h.b_sq, support_mul_commutator h]

/-- The symmetric sandwich exchanges the two support coefficients. -/
theorem sandwich_peirceBlock (h : IsDualSeedPair X Y) (a b c d : R) :
    symmSandwich X Y (peirceBlock X Y a b c d) =
      d • polePlus X Y + a • poleMinus X Y := by
  have hxy : X * Y = polePlus X Y := rfl
  have hyx : Y * X = poleMinus X Y := rfl
  simp only [symmSandwich_apply, peirceBlock, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, h.pp, h.pq, h.qp, h.qq, h.pd, h.pb,
    h.dp, h.dq, h.qd, h.qb, h.bp, h.bq, h.d_sq, h.b_sq, hxy, hyx,
    smul_zero, add_zero, zero_add]
  module

/-- Exact action on every existing supported Peirce block. -/
theorem dissipator_peirceBlock (h : IsDualSeedPair X Y) (a b c d : R) :
    symmDissipator X Y (peirceBlock X Y a b c d) =
      peirceBlock X Y (2 * (d - a)) (-2 * b) (-2 * c) (2 * (a - d)) := by
  rw [symmDissipator_apply, sandwich_peirceBlock h]
  change (2 : R) • (d • polePlus X Y + a • poleMinus X Y) -
    ((polePlus X Y + poleMinus X Y) * peirceBlock X Y a b c d +
      peirceBlock X Y a b c d * (polePlus X Y + poleMinus X Y)) = _
  simp only [peirceBlock, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    h.pp, h.pq, h.qp, h.qq, h.pd, h.pb, h.dp, h.dq, h.qd, h.qb, h.bp, h.bq,
    smul_zero, add_zero, zero_add]
  module

/-- The represented block family is invariant under the actual linear map. -/
theorem dissipator_mem_block_range (h : IsDualSeedPair X Y)
    {Z : Matrix n n R} (hz : ∃ a b c d : R, Z = peirceBlock X Y a b c d) :
    ∃ a b c d : R, symmDissipator X Y Z = peirceBlock X Y a b c d := by
  obtain ⟨a, b, c, d, rfl⟩ := hz
  exact ⟨2 * (d - a), -2 * b, -2 * c, 2 * (a - d), dissipator_peirceBlock h a b c d⟩

/-- Iterated action on the sum, without assuming convergence or a semigroup. -/
theorem dissipator_iterate_add (h : IsDualSeedPair X Y) (k : ℕ) :
    (symmDissipator X Y)^[k] (X + Y) = (-2 : R) ^ k • (X + Y) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_smul, dissipator_add_of_reflexive h]
    simp only [smul_neg, smul_smul, pow_succ, mul_neg, neg_smul]

/-- A nonzero real reflexive seed pair refutes the proposed stationary sum. -/
theorem real_dissipator_add_ne_zero {X Y : Matrix n n ℝ}
    (h : IsDualSeedPair X Y) (hx : X ≠ 0) :
    symmDissipator X Y (X + Y) ≠ 0 := by
  rw [dissipator_add_of_reflexive h, neg_ne_zero]
  apply smul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
  intro hz
  exact hx ((h.velocity_eq_zero_iff).mp hz).1

end InfoGeometry.Core.PeirceSandwichAction
