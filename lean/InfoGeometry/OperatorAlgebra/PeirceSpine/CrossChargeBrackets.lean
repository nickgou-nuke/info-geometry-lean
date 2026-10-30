/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.CornerChargeSectors
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge

/-!
# Cross-charge brackets in the full endomorphism ring

Corrected A54: the extremal bracket uses crossed Q supports:
Q₊ X Q₋ - Q₋ X Q₊. It is not the difference of same-support sandwiches.
-/
namespace InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.LieJordan
variable {B : Type*} [Ring B]

theorem lie_sandwich_comm (U W : B) :
    comm (lieOp ℤ U) (sandwichOp ℤ W W) =
      crossTransport ℤ (comm U W) W := by
  ext X
  simp only [comm, LinearMap.sub_apply, Module.End.mul_apply,
    lieOp_apply, sandwichOp_apply, crossTransport_apply]
  noncomm_ring

variable (P A C : B)

theorem plus_lie_minus_sandwich_comm :
    comm (lieOp ℤ (conePlus P A)) (sandwichOp ℤ (coneMinus P C) (coneMinus P C)) =
      crossTransport ℤ (genSig P A C) (coneMinus P C) :=
  lie_sandwich_comm (conePlus P A) (coneMinus P C)

theorem minus_lie_plus_sandwich_comm :
    comm (lieOp ℤ (coneMinus P C)) (sandwichOp ℤ (conePlus P A) (conePlus P A)) =
      -crossTransport ℤ (genSig P A C) (conePlus P A) := by
  rw [lie_sandwich_comm]
  ext X
  simp only [LinearMap.neg_apply, crossTransport_apply, genSig, comm]
  noncomm_ring

/-- Ordered composition reverses the order of the right multiplication factors. -/
theorem extreme_sandwich_comm :
    comm (sandwichOp ℤ (conePlus P A) (conePlus P A))
      (sandwichOp ℤ (coneMinus P C) (coneMinus P C)) =
      sandwichOp ℤ (qgtPlus P A C) (qgtMinus P A C) -
      sandwichOp ℤ (qgtMinus P A C) (qgtPlus P A C) := by
  ext X
  simp only [comm, LinearMap.sub_apply, Module.End.mul_apply, sandwichOp_apply,
    qgtPlus, qgtMinus, mul_assoc]

/-- Exact error of replacing crossed supports by same-support sandwiches. -/
theorem extreme_same_support_residual :
    comm (sandwichOp ℤ (conePlus P A) (conePlus P A))
      (sandwichOp ℤ (coneMinus P C) (coneMinus P C)) -
      (sandwichOp ℤ (qgtPlus P A C) (qgtPlus P A C) -
        sandwichOp ℤ (qgtMinus P A C) (qgtMinus P A C)) =
      -sandwichOp ℤ (genV P A C) (genSig P A C) := by
  rw [extreme_sandwich_comm]
  ext X
  simp only [LinearMap.sub_apply, LinearMap.neg_apply, sandwichOp_apply,
    qgtPlus, qgtMinus, genV, genSig, comm, anticomm]
  noncomm_ring

variable {P} (hP : P * P = P)
include hP

theorem plus_minus_two_bracket_mem :
    comm (lieOp ℤ (conePlus P A)) (sandwichOp ℤ (coneMinus P C) (coneMinus P C)) ∈
      chargeSector P (-1) := by
  have h := comm_mem_chargeSector (m := 1) (n := -2)
    (plus_lie_mem_sector hP A) (minus_sandwich_mem_sector hP C)
  simpa only [Int.reduceAdd] using h

theorem minus_plus_two_bracket_mem :
    comm (lieOp ℤ (coneMinus P C)) (sandwichOp ℤ (conePlus P A) (conePlus P A)) ∈
      chargeSector P 1 := by
  have h := comm_mem_chargeSector (m := -1) (n := 2)
    (minus_lie_mem_sector hP C) (plus_sandwich_mem_sector hP A)
  simpa only [Int.reduceAdd] using h

theorem extreme_bracket_mem :
    comm (sandwichOp ℤ (conePlus P A) (conePlus P A))
      (sandwichOp ℤ (coneMinus P C) (coneMinus P C)) ∈ chargeSector P 0 := by
  have h := comm_mem_chargeSector (m := 2) (n := -2)
    (plus_sandwich_mem_sector hP A) (minus_sandwich_mem_sector hP C)
  simpa only [Int.reduceAdd] using h

end InfoGeometry.OperatorAlgebra.PeirceSpine
