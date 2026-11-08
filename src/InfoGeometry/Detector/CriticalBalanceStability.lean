/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace DetectorGeometry.CriticalBalanceStability

section Stability

def singlesRate (k ε : ℝ) : ℝ := ε * (1 - k * ε)

noncomputable def balancePoint (k : ℝ) : ℝ := 1 / (2 * k)

noncomputable def maxCapacity (k : ℝ) : ℝ := 1 / (4 * k)

def scalingBeta (k ε : ℝ) : ℝ := 1 - 2 * k * ε

theorem beta_vanishes_at_balance (k : ℝ) (hk : k ≠ 0) :
    scalingBeta k (balancePoint k) = 0 := by
  simp only [scalingBeta, balancePoint]
  rw [mul_one_div_cancel (mul_ne_zero two_ne_zero hk)]
  ring

theorem quadratic_damping (k δ : ℝ) (hk : k ≠ 0) :
    singlesRate k (balancePoint k + δ) = maxCapacity k - k * δ ^ 2 := by
  simp only [singlesRate, balancePoint, maxCapacity]
  field_simp [hk]
  ring

theorem strict_damping (k δ : ℝ) (hk : 0 < k) (hδ : δ ≠ 0) :
    singlesRate k (balancePoint k + δ) < maxCapacity k := by
  rw [quadratic_damping k δ (ne_of_gt hk)]
  have hδsq : 0 < δ ^ 2 := sq_pos_of_ne_zero hδ
  nlinarith [mul_pos hk hδsq]

end Stability

section PairFraction

def coincidenceRate (k ε : ℝ) : ℝ := k * ε ^ 2

def totalPhotons (k ε : ℝ) : ℝ := singlesRate k ε + 2 * coincidenceRate k ε

noncomputable def pairFraction (k ε : ℝ) : ℝ :=
  (2 * coincidenceRate k ε) / totalPhotons k ε

theorem totalPhotons_formula (k ε : ℝ) :
    totalPhotons k ε = ε * (1 + k * ε) := by
  simp [totalPhotons, singlesRate, coincidenceRate]
  ring

theorem pairFraction_formula (k ε : ℝ) (hε : ε ≠ 0)
    (hden : 1 + k * ε ≠ 0) :
    pairFraction k ε = (2 * k * ε) / (1 + k * ε) := by
  simp only [pairFraction, coincidenceRate]
  rw [totalPhotons_formula]
  have h := hε
  field_simp [h, hden]

theorem pairFraction_at_zero (k : ℝ) : pairFraction k 0 = 0 := by
  simp [pairFraction, coincidenceRate, totalPhotons, singlesRate]

theorem pairFraction_at_contact (k : ℝ) (hk : k ≠ 0) :
    pairFraction k (1 / k) = 1 := by
  have hden : 1 + k * (1 / k) ≠ 0 := by
    rw [mul_one_div_cancel hk]
    norm_num
  rw [pairFraction_formula k (1 / k) (one_div_ne_zero hk) hden]
  field_simp [hk]
  ring

theorem pairFraction_at_balance (k : ℝ) (hk : k ≠ 0) :
    pairFraction k (balancePoint k) = 2 / 3 := by
  have hden : 1 + k * balancePoint k ≠ 0 := by
    simp only [balancePoint]
    rw [show k * (1 / (2 * k)) = 1 / 2 by
      field_simp [hk]]
    norm_num
  rw [pairFraction_formula k (balancePoint k)
    (one_div_ne_zero (mul_ne_zero two_ne_zero hk)) hden]
  simp only [balancePoint]
  field_simp [hk]
  ring

end PairFraction

section SouriauVector

structure ThermalVector where
  beta0 : ℝ
  beta1 : ℝ
  beta2 : ℝ

def minkowskiNormSq (v : ThermalVector) : ℝ :=
  v.beta0 ^ 2 - v.beta1 ^ 2 - v.beta2 ^ 2

def criticalThermalVector (β : ℝ) : ThermalVector :=
  ⟨β, 0, β⟩

theorem criticalThermalVector_lightlike (β : ℝ) :
    minkowskiNormSq (criticalThermalVector β) = 0 := by
  simp [minkowskiNormSq, criticalThermalVector]

theorem scaling_beta_unique_zero (k ε : ℝ) (hk : k ≠ 0) :
    scalingBeta k ε = 0 ↔ ε = balancePoint k := by
  simp only [scalingBeta, balancePoint]
  constructor
  · intro h
    have htwo : 2 * k ≠ 0 := mul_ne_zero two_ne_zero hk
    field_simp [htwo] at h ⊢
    linarith
  · intro h
    rw [h]
    rw [mul_one_div_cancel (mul_ne_zero two_ne_zero hk)]
    ring

end SouriauVector

section CausalPoset

inductive Archetype
  | stability
  | pairingCondensate
  | souriauLightCone
  | rgFixedPoint
  deriving DecidableEq, Repr

def rank : Archetype → Nat
  | .stability => 161
  | .pairingCondensate => 162
  | .souriauLightCone => 163
  | .rgFixedPoint => 164

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
    causallyPrecedes .stability .pairingCondensate ∧
    causallyPrecedes .pairingCondensate .souriauLightCone ∧
    causallyPrecedes .souriauLightCone .rgFixedPoint := by
  norm_num [causallyPrecedes, rank]

end CausalPoset

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- Non-commutative operator realization mapping each `CriticalBalanceStability.Archetype`
node to its canonical Peirce operator in `[Ring B]`. -/
def criticalBalanceOperator (P A C X : B) : Archetype → B
  | .stability => derivSqPhi P A C (genJ P A C)
  | .pairingCondensate => genV P A C
  | .souriauLightCone => conePlus P A * conePlus P A
  | .rgFixedPoint => invS P * evenGrade P X * invS P

/-- **Theorem (Non-Commutative Operator Critical Balance & Stability over `[Ring B]`)**:
For any idempotent `P * P = P` in a non-commutative ring `[Ring B]`, the double-commutator
stability operator satisfies `ad_Φ²(J) = -4 V J`, the Souriau light-cone ray `a₊` is
square-zero (`a₊² = 0`), the pairing condensate satisfies `Φ² = V`, and the RG fixed-point
even projection is invariant under reflection conjugation. -/
theorem criticalBalance_operator_identities {P : B} (hP : P * P = P) (A C X : B) :
    criticalBalanceOperator P A C X .stability =
      -((4 : ℤ) • (genV P A C * genJ P A C)) ∧
    genPhi P A C * genPhi P A C =
      criticalBalanceOperator P A C X .pairingCondensate ∧
    criticalBalanceOperator P A C X .souriauLightCone = 0 ∧
    criticalBalanceOperator P A C X .rgFixedPoint = evenGrade P X := by
  dsimp only [criticalBalanceOperator]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (InfoGeometry.OperatorAlgebra.PeirceSpine.archetype_A5_klein_hadamard_spectra_and_partition
      (P := P) hP A C X).2.2.2.1
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP

end NonCommutativeOperatorRealization

end DetectorGeometry.CriticalBalanceStability
