/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

/-!
# Jaynes Relative States and the Derivation of Cuntz KMS Laws

This module formalizes the derivation of the KMS state properties for the Cuntz algebra
$\mathcal{O}_2$ from the perspective of Jaynes' Principle of Maximum Entropy (MaxEnt).

The derivation is driven by two physical constraints:
1. The Cuntz Partition of Unity: $S_L S_L^* + S_R S_R^* = 1$.
2. Jaynes' Principle of Insufficient Reason (unbiased left-right exchange symmetry: $p_L = p_R = p$).

We prove that these two constraints mathematically force the KMS scaling factors to be
exactly $1/2$, without any arbitrary assumption or custom axioms.
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

/- The two weighted branch coefficients sum to one before imposing
    left-right symmetry.  This is the algebraic conservation law underlying
    the symmetric value proved below. -/
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

end InfoGeometry.Analysis.JaynesRelativeStates
