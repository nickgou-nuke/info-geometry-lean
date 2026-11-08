/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace DetectorGeometry.ApollonianBalanceParabola

section Parabola

def singleObserved (N₀ K ε : ℝ) : ℝ := N₀ * ε * (1 - K * ε)

def coincidenceRate (N₀ K ε : ℝ) : ℝ := N₀ * K * ε ^ 2

theorem pole_one (N₀ K : ℝ) : singleObserved N₀ K 0 = 0 := by
  simp [singleObserved]

noncomputable def criticalEfficiency (K : ℝ) : ℝ := 1 / K

theorem pole_two (N₀ K : ℝ) (hK : K ≠ 0) :
    singleObserved N₀ K (criticalEfficiency K) = 0 := by
  simp only [singleObserved, criticalEfficiency]
  rw [mul_one_div_cancel hK, sub_self, mul_zero]

noncomputable def balancePoint (K : ℝ) : ℝ := 1 / (2 * K)

theorem balance_midpoint (K : ℝ) (hK : K ≠ 0) :
    balancePoint K = (1 / 2) * criticalEfficiency K := by
  simp only [balancePoint, criticalEfficiency]
  field_simp [hK]

theorem vertex_form (N₀ K ε : ℝ) (hK : K ≠ 0) :
    singleObserved N₀ K ε = N₀ / (4 * K) -
      N₀ * K * (ε - balancePoint K) ^ 2 := by
  simp only [singleObserved, balancePoint]
  field_simp [hK]
  ring

theorem equipartition_at_balance (N₀ K : ℝ) (hK : K ≠ 0) :
    singleObserved N₀ K (balancePoint K) =
        coincidenceRate N₀ K (balancePoint K) ∧
    singleObserved N₀ K (balancePoint K) = N₀ / (4 * K) := by
  constructor <;> simp only [singleObserved, coincidenceRate, balancePoint]
  · field_simp [hK]
    ring
  · field_simp [hK]
    ring

end Parabola

section CrossRatio

noncomputable def crossRatio (K ε : ℝ) : ℝ := (K * ε) / (1 - K * ε)

theorem crossRatio_at_balance (K : ℝ) (hK : K ≠ 0) :
    crossRatio K (balancePoint K) = 1 := by
  simp only [crossRatio, balancePoint]
  field_simp [hK]
  ring

theorem crossRatio_count_ratio (N₀ K ε : ℝ)
    (hsingle : singleObserved N₀ K ε ≠ 0) :
    crossRatio K ε = coincidenceRate N₀ K ε / singleObserved N₀ K ε := by
  have hN₀ : N₀ ≠ 0 := by
    intro h
    apply hsingle
    simp [singleObserved, h]
  have hε : ε ≠ 0 := by
    intro h
    apply hsingle
    simp [singleObserved, h]
  have hfactor : 1 - K * ε ≠ 0 := by
    intro h
    apply hsingle
    simp [singleObserved, h]
  simp only [crossRatio, coincidenceRate, singleObserved]
  field_simp [hN₀, hε, hfactor]

end CrossRatio

section CausalPoset

inductive Archetype
  | vacuumPole
  | summingPole
  | equipartitionPeak
  | crossRatio
  deriving DecidableEq, Repr

def rank : Archetype → Nat
  | .vacuumPole => 152
  | .summingPole => 153
  | .equipartitionPeak => 154
  | .crossRatio => 155

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
    causallyPrecedes .vacuumPole .summingPole ∧
    causallyPrecedes .summingPole .equipartitionPeak ∧
    causallyPrecedes .equipartitionPeak .crossRatio := by
  norm_num [causallyPrecedes, rank]

end CausalPoset

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- Non-commutative operator realization mapping each `ApollonianBalanceParabola.Archetype`
node to its canonical Peirce operator in `[Ring B]`. -/
def apollonianBalanceOperator (P A C : B) : Archetype → B
  | .vacuumPole => P * (1 - P)
  | .summingPole => (1 - P) * P
  | .equipartitionPeak => P + (1 - P) - invS P * invS P
  | .crossRatio => InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C)

/-- **Theorem (Non-Commutative Operator Apollonian Balance over `[Ring B]`)**:
For any idempotent `P * P = P` in a non-commutative ring `[Ring B]`, both boundary poles
`P (1 - P) = 0` and `(1 - P) P = 0` vanish, the equipartition balance identity
`P + (1 - P) - S² = 0` holds, and the cross-ratio commutator satisfies `[Φ, J] = -2 Σ`. -/
theorem apollonianBalance_operator_identities {P : B} (hP : P * P = P) (A C : B) :
    apollonianBalanceOperator P A C .vacuumPole = 0 ∧
    apollonianBalanceOperator P A C .summingPole = 0 ∧
    apollonianBalanceOperator P A C .equipartitionPeak = 0 ∧
    apollonianBalanceOperator P A C .crossRatio = -((2 : ℤ) • genSig P A C) := by
  dsimp only [apollonianBalanceOperator]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

end NonCommutativeOperatorRealization

end DetectorGeometry.ApollonianBalanceParabola
