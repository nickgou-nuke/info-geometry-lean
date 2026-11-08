/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceCoupledCorners
import InfoGeometry.OperatorAlgebra.SquareZeroModeActions

/-!
# Fourteen Peirce identities, with their actual hypotheses

Uses the existing Peirce corners, reflection, and native inner derivations.
The last identity is additive cancellation, not a projection theorem. The
first thirteen are associative-ring identities; no centrality, diagonalization,
star, invertibility, or spectral assumption is imposed.
-/

namespace InfoGeometry.WheelerEpilogue

attribute [local instance 100] LieRing.ofAssociativeRing

open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.Core.PeirceGrading
open InfoGeometry.Core.PeirceCoupledCorners
open InfoGeometry.OperatorAlgebra.PeirceSuperoperators
open InfoGeometry.OperatorAlgebra.SquareZeroModeActions

variable {B : Type*} [Ring B]

/-- Adjacent copies of an idempotent in a right-associated product. -/
theorem idempotent_mul_assoc {p : B} (hp : p * p = p) (x : B) :
    p * (p * x) = p * x := by
  rw [← mul_assoc, hp]

/-- A right annihilator removes the two mixed terms, without commuting inputs. -/
theorem double_lie_of_right_annihilator {a z : B} (h : z * a = 0) :
    ⁅a, ⁅a, z⁆⁆ = a * a * z := by
  change a * (a * z - z * a) - (a * z - z * a) * a = a * a * z
  rw [h, sub_zero, mul_assoc a z a, h, mul_zero, sub_zero, mul_assoc]

/-- This identity holds for arbitrary native endomorphisms, independently of
any idempotent or square-zero input. It asserts no idempotence of the summands. -/
theorem signed_endomorphism_partition {R V : Type*} [Ring R]
    [AddCommGroup V] [Module R V] (f g h : Module.End R V) :
    ((8 : ℤ) • (1 : Module.End R V) + (f + g + h)) +
      (f - g - h) + (g - f - h) + (h - f - g) =
        (8 : ℤ) • (1 : Module.End R V) := by
  abel

/-- The fourteen supplied equations on the existing owner carriers.
The factors 4 are repeated addition, not scalar replacements for the weight.
This theorem is a regression/assembly of owner results, not fourteen new
independent discoveries or a completeness theorem for a tactic. -/
theorem fourteen_laws {p : B} (hp : p * p = p) (a c X : B) :
    let u := component10 p a
    let v := component01 p c
    let e := u + v
    let j := u - v
    let m := u * v + v * u
    let s := ⁅u, v⁆
    let f := -((LieAlgebra.ad ℤ B e) ^ 2)
    let g := (LieAlgebra.ad ℤ B j) ^ 2
    let h := -((LieAlgebra.ad ℤ B s) ^ 2)
    u * u = 0 ∧
    v * v = 0 ∧
    e * e = m ∧
    j * j = -m ∧
    e * e + j * j = 0 ∧
    e * j + j * e = 0 ∧
    j * e = s ∧
    s = reflection p * m ∧
    f e = 0 ∧
    f m = 0 ∧
    f j = -(4 • (m * j)) ∧
    f s = -(4 • (m * s)) ∧
    u * v * u = m * u ∧
    ((8 : ℤ) • X + (f X + g X + h X)) +
      (f X - g X - h X) + (g X - f X - h X) +
      (h X - f X - g X) = (8 : ℤ) • X := by
  dsimp only
  have hu : component10 p a * component10 p a = 0 :=
    peirce10_mul_peirce10_eq_zero p hp (component10_mem p a) (component10_mem p a)
  have hv : component01 p c * component01 p c = 0 :=
    peirce01_mul_peirce01_eq_zero p hp (component01_mem p c) (component01_mem p c)
  refine ⟨hu, hv, square_zero_pair_sum_sq hu hv,
    square_zero_pair_sub_sq hu hv, ?_, ?_, square_zero_pair_sub_mul_sum hu hv,
    ?_, neg_ad_sum_sq_sum (R := ℤ) _ _, neg_ad_sum_sq_weight (R := ℤ) hu hv,
    neg_ad_sum_sq_difference (R := ℤ) hu hv,
    neg_ad_sum_sq_bracket (R := ℤ) hu hv, ?_, ?_⟩
  · rw [square_zero_pair_sum_sq hu hv, square_zero_pair_sub_sq hu hv, add_neg_cancel]
  · rw [square_zero_pair_sum_mul_sub hu hv, square_zero_pair_sub_mul_sum hu hv,
      neg_add_cancel]
  · exact (reflection_mul_jordan hp (component10_mem p a) (component01_mem p c)).symm
  · symm
    rw [add_mul, mul_assoc (component01 p c), hu, mul_zero, add_zero]
  · abel

end InfoGeometry.WheelerEpilogue
