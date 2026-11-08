/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.AlbertCayleyDickson
import Mathlib.Tactic

namespace InfoGeometry.NCG.PeirceGradingOperator

variable {A : Type*} [Ring A]

open InfoGeometry.Canonical.AlbertCayleyDickson
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix

def P_plus : OpZornMatrix A := ⟨1, 0, 0, 0⟩
def P_minus : OpZornMatrix A := ⟨0, 0, 0, 1⟩
def eta_grading : OpZornMatrix A := ⟨1, 0, 0, -1⟩

/-- Peirce corner axioms: P₊, P₋ are orthogonal idempotents summing to 1. -/
theorem peirce_corner_axioms :
    (P_plus * P_plus : OpZornMatrix A) = P_plus ∧
    (P_minus * P_minus : OpZornMatrix A) = P_minus ∧
    (P_plus * P_minus : OpZornMatrix A) = 0 ∧
    (P_minus * P_plus : OpZornMatrix A) = 0 ∧
    P_plus + P_minus = (1 : OpZornMatrix A) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext <;>
      simp [P_plus, P_minus, instMulOpZornMatrix, instAddOpZornMatrix,
        OpVec3.dot, OpVec3.skewCross, OpVec3.leftScale, OpVec3.rightScale])

/-- The Peirce grading element is an involution: η² = 1. -/
theorem eta_square_one :
    (eta_grading * eta_grading : OpZornMatrix A) = (1 : OpZornMatrix A) := by
  ext <;>
    simp [eta_grading, instMulOpZornMatrix, OpVec3.dot,
      OpVec3.skewCross, OpVec3.leftScale, OpVec3.rightScale]

/-- Corner grading: η * P₊ = P₊, η * P₋ = -P₋, P₊ * η = P₊, P₋ * η = -P₋. -/
theorem eta_corner_grading :
    (eta_grading * P_plus : OpZornMatrix A) = P_plus ∧
    (eta_grading * P_minus : OpZornMatrix A) = -P_minus ∧
    (P_plus * eta_grading : OpZornMatrix A) = P_plus ∧
    (P_minus * eta_grading : OpZornMatrix A) = -P_minus := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (ext <;>
      simp [eta_grading, P_plus, P_minus, instMulOpZornMatrix,
        instNegOpZornMatrix, OpVec3.dot, OpVec3.skewCross,
        OpVec3.leftScale, OpVec3.rightScale])

end InfoGeometry.NCG.PeirceGradingOperator
