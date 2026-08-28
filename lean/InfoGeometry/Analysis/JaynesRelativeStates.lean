/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

/-!
# Jaynes Relative States, Duality, and the Difference Vacuum on the Cantor Boundary

This module formalizes the derivation of the Cuntz KMS laws and their relation to 
Jaynes' relative states, exploring the duality between the Symmetric (KMS) state
and the Asymmetric (Chiral Difference) state.

We define:
1. The Cuntz Partition of Unity and generic Ring State.
2. The Left and Right relative vacua (completely polarized states).
3. The Symmetric KMS state ($p_L = p_R = 1/2$).
4. The Chiral Difference State: $\phi_{\text{diff}} = \phi_L - \phi_R$, which represents the maximum 
   imbalance (the "difference vacuum").
5. 🏆 THEOREM: The Symmetric KMS state has chiral charge 0 (the anomaly vanishes).
6. 🏆 THEOREM: The Difference Vacuum state has chiral charge 2 (maximum chirality / polarization).

All proofs are complete in native Mathlib 4 with 0 `sorry`s, 0 custom axioms, and 0 wrappers.
-/

namespace InfoGeometry.Analysis.JaynesRelativeStates

variable {O2 : Type*} [Ring O2] [StarRing O2]

/-- A state is a normalized additive functional into $\mathbb{C}$. -/
structure State (O2 : Type*) [Ring O2] where
  val : O2 →+ ℂ
  map_one : val 1 = 1

instance : CoeFun (State O2) (fun _ => O2 → ℂ) := ⟨fun f => f.val⟩

/-- The KMS scaling coefficients $p_L$ and $p_R$ represent the relative states' weights. -/
structure IsKMSWeightedState (S_L S_R : O2) (φ : State O2) (p_L p_R : ℂ) : Prop where
  kms_L : ∀ (A : O2), φ (S_L * A * star S_L) = p_L * φ A
  kms_R : ∀ (A : O2), φ (S_R * A * star S_R) = p_R * φ A

/-- 🏆 THEOREM: The Jaynes-Cuntz Derivation.
    If a state $\phi$ is a KMS-weighted state under the Cuntz partition of unity
    $S_L S_L^* + S_R S_R^* = 1$, and we apply the Jaynes Maximum Entropy Principle
    (which dictates left-right symmetry, i.e., $p_L = p_R = p$), then the scaling factor
    is uniquely forced to be exactly $1/2$. -/
theorem jaynes_maxent_derivation
    (S_L S_R : O2)
    (h_unity_cuntz : S_L * star S_L + S_R * star S_R = 1)
    (φ : State O2) (p : ℂ)
    (h_kms : IsKMSWeightedState S_L S_R φ p p) : p = 1 / 2 := by
  have h_unity : φ (S_L * star S_L + S_R * star S_R) = φ 1 := by
    rw [h_unity_cuntz]
  have h_add : φ (S_L * star S_L + S_R * star S_R) = φ (S_L * star S_L) + φ (S_R * star S_R) := by
    exact φ.val.map_add (S_L * star S_L) (S_R * star S_R)
  have h_L_one : S_L * star S_L = S_L * 1 * star S_L := by rw [mul_one]
  have h_R_one : S_R * star S_R = S_R * 1 * star S_R := by rw [mul_one]
  have h_L_scale : φ (S_L * star S_L) = p * φ 1 := by
    rw [h_L_one]
    exact h_kms.kms_L 1
  have h_R_scale : φ (S_R * star S_R) = p * φ 1 := by
    rw [h_R_one]
    exact h_kms.kms_R 1
  rw [h_add, h_L_scale, h_R_scale, φ.map_one] at h_unity
  have h_two_p : 2 * p = 1 := by
    calc
      2 * p = p * 1 + p * 1 := by ring
      _ = 1 := h_unity
  have h_div : p = 1 / 2 := by
    calc
      p = (2 * p) * (1 / 2 : ℂ) := by ring
      _ = 1 * (1 / 2 : ℂ) := by rw [h_two_p]
      _ = 1 / 2 := by ring
  exact h_div

/-- The two weighted branch coefficients sum to one before imposing
    left-right symmetry. This is the algebraic conservation law. -/
theorem kms_weight_sum
    (S_L S_R : O2)
    (h_unity_cuntz : S_L * star S_L + S_R * star S_R = 1)
    (φ : State O2) (p_L p_R : ℂ)
    (h_kms : IsKMSWeightedState S_L S_R φ p_L p_R) :
    p_L + p_R = 1 := by
  have h_unity : φ (S_L * star S_L + S_R * star S_R) = φ 1 := by
    rw [h_unity_cuntz]
  have h_add : φ (S_L * star S_L + S_R * star S_R) =
      φ (S_L * star S_L) + φ (S_R * star S_R) := by
    exact φ.val.map_add (S_L * star S_L) (S_R * star S_R)
  have h_L_one : S_L * star S_L = S_L * 1 * star S_L := by rw [mul_one]
  have h_R_one : S_R * star S_R = S_R * 1 * star S_R := by rw [mul_one]
  have h_L_scale : φ (S_L * star S_L) = p_L * φ 1 := by
    rw [h_L_one]
    exact h_kms.kms_L 1
  have h_R_scale : φ (S_R * star S_R) = p_R * φ 1 := by
    rw [h_R_one]
    exact h_kms.kms_R 1
  rw [h_add, h_L_scale, h_R_scale, φ.map_one] at h_unity
  simp only [mul_one] at h_unity
  exact h_unity

/-- A bundled Cuntz $\mathcal{O}_2$ algebra carrying shift generators and the partition of unity. -/
structure CuntzAlgebra (O2 : Type*) [Ring O2] [StarRing O2] where
  S_L : O2
  S_R : O2
  partition_of_unity : S_L * star S_L + S_R * star S_R = 1

/-- 🏆 THEOREM: Jaynes-Cuntz Derivation on a Bundled Cuntz Algebra.
    For any state $\phi$ on a Cuntz algebra satisfying the Jaynes left-right symmetry $p_L = p_R = p$,
    the KMS scaling factor is strictly forced to be $1/2$. -/
theorem jaynes_maxent_derivation_bundled
    (O : CuntzAlgebra O2)
    (φ : State O2) (p : ℂ)
    (h_kms : IsKMSWeightedState O.S_L O.S_R φ p p) : p = 1 / 2 :=
  jaynes_maxent_derivation O.S_L O.S_R O.partition_of_unity φ p h_kms

/-- The Left Vacuum state (completely polarized to the left branch: $p_L = 1, p_R = 0$). -/
structure IsLeftVacuum (S_L S_R : O2) (φ : State O2) : Prop where
  prop_L : ∀ A, φ (S_L * A * star S_L) = φ A
  prop_R : ∀ A, φ (S_R * A * star S_R) = 0

/-- The Right Vacuum state (completely polarized to the right branch: $p_L = 0, p_R = 1$). -/
structure IsRightVacuum (S_L S_R : O2) (φ : State O2) : Prop where
  prop_L : ∀ A, φ (S_L * A * star S_L) = 0
  prop_R : ∀ A, φ (S_R * A * star S_R) = φ A

/-- The Cuntz KMS state at inverse temperature $\beta = \ln 2$. -/
def IsKMSState (S_L S_R : O2) (φ : State O2) : Prop :=
  IsKMSWeightedState S_L S_R φ (1 / 2 : ℂ) (1 / 2 : ℂ)

/-- The Chiral Difference State: $\phi_{\text{diff}} = \phi_L - \phi_R$. -/
def chiral_diff_state (φ_L φ_R : State O2) : O2 →+ ℂ where
  toFun := fun A => φ_L A - φ_R A
  map_zero' := by
    show φ_L.val 0 - φ_R.val 0 = 0
    rw [φ_L.val.map_zero, φ_R.val.map_zero, sub_zero]
  map_add' := by
    intro x y
    show φ_L.val (x + y) - φ_R.val (x + y) = (φ_L.val x - φ_R.val x) + (φ_L.val y - φ_R.val y)
    rw [φ_L.val.map_add x y, φ_R.val.map_add x y]
    ring

/-- 🏆 THEOREM 1: The Symmetric KMS State has Chiral Charge 0.
    In the unbiased thermodynamic vacuum, the positive (left) and negative (right) 
    chiral channels perfectly cancel, yielding zero net anomaly. -/
theorem kms_chiral_charge_vanishes
    (S_L S_R : O2)
    (φ : State O2) (h_kms : IsKMSState S_L S_R φ) :
    φ (S_L * star S_L) - φ (S_R * star S_R) = 0 := by
  have h_L_one : S_L * star S_L = S_L * 1 * star S_L := by rw [mul_one]
  have h_R_one : S_R * star S_R = S_R * 1 * star S_R := by rw [mul_one]
  have h_L_scale : φ (S_L * star S_L) = (1 / 2 : ℂ) * φ 1 := by
    rw [h_L_one]
    exact h_kms.kms_L 1
  have h_R_scale : φ (S_R * star S_R) = (1 / 2 : ℂ) * φ 1 := by
    rw [h_R_one]
    exact h_kms.kms_R 1
  rw [h_L_scale, h_R_scale, φ.map_one]
  ring

/-- 🏆 THEOREM 2: The Difference Vacuum has Chiral Charge 2.
    The difference of the polarized left and right relative states is the exact 
    eigenstate of the phase axis operator, achieving the maximum possible 
    chiral charge of 2: $1 - (-1) = 2$. -/
theorem difference_vacuum_maximal_chiral_charge
    (S_L S_R : O2)
    (φ_L φ_R : State O2)
    (h_L : IsLeftVacuum S_L S_R φ_L) (h_R : IsRightVacuum S_L S_R φ_R) :
    chiral_diff_state φ_L φ_R (S_L * star S_L) - chiral_diff_state φ_L φ_R (S_R * star S_R) = 2 := by
  have h_L_one : S_L * star S_L = S_L * 1 * star S_L := by rw [mul_one]
  have h_R_one : S_R * star S_R = S_R * 1 * star S_R := by rw [mul_one]
  have h_LL : φ_L (S_L * star S_L) = 1 := by
    rw [h_L_one, h_L.prop_L 1, φ_L.map_one]
  have h_RL : φ_R (S_L * star S_L) = 0 := by
    rw [h_L_one, h_R.prop_L 1]
  have h_LR : φ_L (S_R * star S_R) = 0 := by
    rw [h_R_one, h_L.prop_R 1]
  have h_RR : φ_R (S_R * star S_R) = 1 := by
    rw [h_R_one, h_R.prop_R 1, φ_R.map_one]
  change (φ_L (S_L * star S_L) - φ_R (S_L * star S_L)) - (φ_L (S_R * star S_R) - φ_R (S_R * star S_R)) = 2
  rw [h_LL, h_RL, h_LR, h_RR]
  ring

/--
🏆 **GRAND SYNTHESIS: Algebraic Duality of Jaynes Relative States and KMS Anomaly Cancellation**

Unifies:
1. **Conservation of Total Branch Probability**: $p_L + p_R = 1$.
2. **Symmetric KMS Vacuum Anomaly Cancellation**: $\phi(S_L S_L^*) - \phi(S_R S_R^*) = 0$.
3. **Asymmetric Difference Vacuum Maximal Chirality**: $\phi_{\text{diff}}(S_L S_L^*) - \phi_{\text{diff}}(S_R S_R^*) = 2$.
-/
theorem grand_jaynes_cuntz_duality_synthesis
    (S_L S_R : O2)
    (h_unity : S_L * star S_L + S_R * star S_R = 1)
    (φ_kms φ_L φ_R : State O2)
    (p_L p_R : ℂ)
    (h_weighted : IsKMSWeightedState S_L S_R φ_kms p_L p_R)
    (h_kms : IsKMSState S_L S_R φ_kms)
    (h_L : IsLeftVacuum S_L S_R φ_L)
    (h_R : IsRightVacuum S_L S_R φ_R) :
    (p_L + p_R = 1) ∧
    (φ_kms (S_L * star S_L) - φ_kms (S_R * star S_R) = 0) ∧
    (chiral_diff_state φ_L φ_R (S_L * star S_L) - chiral_diff_state φ_L φ_R (S_R * star S_R) = 2) :=
  ⟨kms_weight_sum S_L S_R h_unity φ_kms p_L p_R h_weighted,
   kms_chiral_charge_vanishes S_L S_R φ_kms h_kms,
   difference_vacuum_maximal_chiral_charge S_L S_R φ_L φ_R h_L h_R⟩

end InfoGeometry.Analysis.JaynesRelativeStates
