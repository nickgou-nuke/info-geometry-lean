/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace DetectorGeometry.InformationCarnotCycle

section CarnotEfficiency

def efficiency (K ε : ℝ) : ℝ := 1 - K * ε

noncomputable def criticalEfficiency (K : ℝ) : ℝ := 1 / K

theorem efficiency_at_zero (K : ℝ) : efficiency K 0 = 1 := by
  simp [efficiency]

theorem efficiency_at_critical (K : ℝ) (hK : K ≠ 0) :
    efficiency K (criticalEfficiency K) = 0 := by
  simp only [efficiency, criticalEfficiency]
  field_simp [hK]
  ring

end CarnotEfficiency

section Summit

noncomputable def balancePoint (K : ℝ) : ℝ := 1 / (2 * K)

def informationPower (N₀ K ε : ℝ) : ℝ := N₀ * ε * efficiency K ε

theorem efficiency_at_balance (K : ℝ) (hK : K ≠ 0) :
    efficiency K (balancePoint K) = 1 / 2 := by
  simp only [efficiency, balancePoint]
  field_simp [hK]
  ring

theorem power_at_balance (N₀ K : ℝ) (hK : K ≠ 0) :
    informationPower N₀ K (balancePoint K) = N₀ / (4 * K) := by
  simp only [informationPower, efficiency, balancePoint]
  field_simp [hK]
  ring

end Summit

section Capacity

noncomputable def informationPrimitive (K ε : ℝ) : ℝ :=
  ε ^ 2 / 2 - K * ε ^ 3 / 3

noncomputable def cycleCapacity (K : ℝ) : ℝ := 1 / (6 * K ^ 2)

theorem cycle_capacity_evaluation (K : ℝ) (hK : K ≠ 0) :
    informationPrimitive K (criticalEfficiency K) - informationPrimitive K 0 =
      cycleCapacity K := by
  simp only [informationPrimitive, criticalEfficiency, cycleCapacity]
  field_simp [hK]
  ring

end Capacity

section Equipartition

def coincidencePower (N₀ K ε : ℝ) : ℝ := N₀ * K * ε ^ 2

theorem summit_equipartition (N₀ K : ℝ) (hK : K ≠ 0) :
    informationPower N₀ K (balancePoint K) =
        coincidencePower N₀ K (balancePoint K) ∧
    informationPower N₀ K (balancePoint K) = N₀ / (4 * K) := by
  constructor
  · simp only [informationPower, coincidencePower, efficiency, balancePoint]
    field_simp [hK]
    ring
  · exact power_at_balance N₀ K hK

theorem endpoint_power_at_critical (N₀ K : ℝ) (hK : K ≠ 0) :
    informationPower N₀ K (criticalEfficiency K) = 0 := by
  simp only [informationPower]
  rw [efficiency_at_critical K hK]
  simp

end Equipartition

section CausalPoset

inductive Archetype
  | carnotEfficiency
  | maximumPowerSummit
  | enclosedCapacity
  | equipartition
  | cycleClosure
  deriving DecidableEq, Repr

def rank : Archetype → Nat
  | .carnotEfficiency => 156
  | .maximumPowerSummit => 157
  | .enclosedCapacity => 158
  | .equipartition => 159
  | .cycleClosure => 160

def causallyPrecedes (a b : Archetype) : Prop := rank a ≤ rank b

theorem causal_refl (a : Archetype) : causallyPrecedes a a := le_rfl

theorem causal_trans {a b c : Archetype} :
    causallyPrecedes a b → causallyPrecedes b c → causallyPrecedes a c := by
  exact Nat.le_trans

theorem causal_antisymm {a b : Archetype} :
    causallyPrecedes a b → causallyPrecedes b a → a = b := by
  intro hab hba
  cases a <;> cases b <;> simp [causallyPrecedes, rank] at hab hba ⊢

theorem canonical_chain :
    causallyPrecedes .carnotEfficiency .maximumPowerSummit ∧
    causallyPrecedes .maximumPowerSummit .enclosedCapacity ∧
    causallyPrecedes .enclosedCapacity .equipartition ∧
    causallyPrecedes .equipartition .cycleClosure := by
  norm_num [causallyPrecedes, rank]

end CausalPoset

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- Non-commutative operator realization mapping each `InformationCarnotCycle.Archetype`
node to its canonical Peirce operator in `[Ring B]`. -/
def informationCarnotOperator (P A C : B) : Archetype → B
  | .carnotEfficiency => 1 - P
  | .maximumPowerSummit => P * (1 - P)
  | .enclosedCapacity => genV P A C
  | .equipartition => genPhi P A C * genPhi P A C + genJ P A C * genJ P A C
  | .cycleClosure => InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C)

/-- **Theorem (Non-Commutative Operator Carnot Cycle Closure over `[Ring B]`)**:
For any idempotent `P * P = P` in a non-commutative ring `[Ring B]`, the complementary
efficiency projector `1 - P` is idempotent, `P (1 - P) = 0`, the equipartition sum
`Φ² + J² = 0` balances, and the cycle commutator closes as `[Φ, J] = 2 Σ`. -/
theorem informationCarnot_operator_identities {P : B} (hP : P * P = P) (A C : B) :
    informationCarnotOperator P A C .carnotEfficiency *
      informationCarnotOperator P A C .carnotEfficiency =
      informationCarnotOperator P A C .carnotEfficiency ∧
    informationCarnotOperator P A C .maximumPowerSummit = 0 ∧
    genPhi P A C * genPhi P A C =
      informationCarnotOperator P A C .enclosedCapacity ∧
    informationCarnotOperator P A C .equipartition = 0 ∧
    informationCarnotOperator P A C .cycleClosure = -((2 : ℤ) • genSig P A C) := by
  dsimp only [informationCarnotOperator]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

end NonCommutativeOperatorRealization

end DetectorGeometry.InformationCarnotCycle
