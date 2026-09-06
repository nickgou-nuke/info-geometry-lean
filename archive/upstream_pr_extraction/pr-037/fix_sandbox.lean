import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot
import Mathlib.RingTheory.Adjoin.Basic

import InfoGeometry.Projective.QuantumGrassmannian

noncomputable section

namespace InfoGeometry.Projective.QuantumGrassmannian

universe u
variable {R : Type u} [Field R] (q : R)

local notation "a0" => entry R q 0 0
local notation "a1" => entry R q 0 1
local notation "a2" => entry R q 0 2
local notation "a3" => entry R q 0 3
local notation "b0" => entry R q 1 0
local notation "b1" => entry R q 1 1
local notation "b2" => entry R q 1 2
local notation "b3" => entry R q 1 3

local notation "p01" => quantumMinor R q ⟨(0, 1), by decide⟩
local notation "p23" => quantumMinor R q ⟨(2, 3), by decide⟩
local notation "p02" => quantumMinor R q ⟨(0, 2), by decide⟩
local notation "p13" => quantumMinor R q ⟨(1, 3), by decide⟩
local notation "p03" => quantumMinor R q ⟨(0, 3), by decide⟩
local notation "p12" => quantumMinor R q ⟨(1, 2), by decide⟩

lemma minor_01 : p01 = a0 * b1 - q • (a1 * b0) := rfl
lemma minor_23 : p23 = a2 * b3 - q • (a3 * b2) := rfl
lemma minor_02 : p02 = a0 * b2 - q • (a2 * b0) := rfl
lemma minor_13 : p13 = a1 * b3 - q • (a3 * b1) := rfl
lemma minor_03 : p03 = a0 * b3 - q • (a3 * b0) := rfl
lemma minor_12 : p12 = a1 * b2 - q • (a2 * b1) := rfl

lemma expand_binomial {A : Type u} [Ring A] [Algebra R A] (X Y Z W : A) (q : R) :
  (X - q • Y) * (Z - q • W) = X * Z - q • (X * W) - q • (Y * Z) + q^2 • (Y * W) := by
  simp only [sub_mul, mul_sub, mul_smul_comm, smul_mul_assoc, sq, smul_smul]
  abel

-- sameRow for a
lemma a0_a1 : a0 * a1 = q • (a1 * a0) := entry_sameRow R q 0 0 1 (by decide)
lemma a0_a2 : a0 * a2 = q • (a2 * a0) := entry_sameRow R q 0 0 2 (by decide)
lemma a0_a3 : a0 * a3 = q • (a3 * a0) := entry_sameRow R q 0 0 3 (by decide)
lemma a1_a2 : a1 * a2 = q • (a2 * a1) := entry_sameRow R q 0 1 2 (by decide)
lemma a1_a3 : a1 * a3 = q • (a3 * a1) := entry_sameRow R q 0 1 3 (by decide)
lemma a2_a3 : a2 * a3 = q • (a3 * a2) := entry_sameRow R q 0 2 3 (by decide)

-- sameRow for b
lemma b0_b1 : b0 * b1 = q • (b1 * b0) := entry_sameRow R q 1 0 1 (by decide)
lemma b0_b2 : b0 * b2 = q • (b2 * b0) := entry_sameRow R q 1 0 2 (by decide)
lemma b0_b3 : b0 * b3 = q • (b3 * b0) := entry_sameRow R q 1 0 3 (by decide)
lemma b1_b2 : b1 * b2 = q • (b2 * b1) := entry_sameRow R q 1 1 2 (by decide)
lemma b1_b3 : b1 * b3 = q • (b3 * b1) := entry_sameRow R q 1 1 3 (by decide)
lemma b2_b3 : b2 * b3 = q • (b3 * b2) := entry_sameRow R q 1 2 3 (by decide)

-- separated
lemma b0_a1 : b0 * a1 = a1 * b0 := entry_separated R q 0 1 1 0 (by decide) (by decide)
lemma b0_a2 : b0 * a2 = a2 * b0 := entry_separated R q 0 1 2 0 (by decide) (by decide)
lemma b0_a3 : b0 * a3 = a3 * b0 := entry_separated R q 0 1 3 0 (by decide) (by decide)
lemma b1_a2 : b1 * a2 = a2 * b1 := entry_separated R q 0 1 2 1 (by decide) (by decide)
lemma b1_a3 : b1 * a3 = a3 * b1 := entry_separated R q 0 1 3 1 (by decide) (by decide)
lemma b2_a3 : b2 * a3 = a3 * b2 := entry_separated R q 0 1 3 2 (by decide) (by decide)

-- crossing
lemma b1_a0 : b1 * a0 = a0 * b1 - (q - q⁻¹) • (a1 * b0) := by
  have := entry_crossing R q 0 1 0 1 (by decide) (by decide)
  calc b1 * a0 = a0 * b1 - (a0 * b1 - b1 * a0) := by abel
       _       = a0 * b1 - (q - q⁻¹) • (a1 * b0) := by rw [this]

lemma b2_a0 : b2 * a0 = a0 * b2 - (q - q⁻¹) • (a2 * b0) := by
  have := entry_crossing R q 0 1 0 2 (by decide) (by decide)
  calc b2 * a0 = a0 * b2 - (a0 * b2 - b2 * a0) := by abel
       _       = a0 * b2 - (q - q⁻¹) • (a2 * b0) := by rw [this]

lemma b3_a0 : b3 * a0 = a0 * b3 - (q - q⁻¹) • (a3 * b0) := by
  have := entry_crossing R q 0 1 0 3 (by decide) (by decide)
  calc b3 * a0 = a0 * b3 - (a0 * b3 - b3 * a0) := by abel
       _       = a0 * b3 - (q - q⁻¹) • (a3 * b0) := by rw [this]

lemma b2_a1 : b2 * a1 = a1 * b2 - (q - q⁻¹) • (a2 * b1) := by
  have := entry_crossing R q 0 1 1 2 (by decide) (by decide)
  calc b2 * a1 = a1 * b2 - (a1 * b2 - b2 * a1) := by abel
       _       = a1 * b2 - (q - q⁻¹) • (a2 * b1) := by rw [this]

lemma b3_a1 : b3 * a1 = a1 * b3 - (q - q⁻¹) • (a3 * b1) := by
  have := entry_crossing R q 0 1 1 3 (by decide) (by decide)
  calc b3 * a1 = a1 * b3 - (a1 * b3 - b3 * a1) := by abel
       _       = a1 * b3 - (q - q⁻¹) • (a3 * b1) := by rw [this]

lemma b3_a2 : b3 * a2 = a2 * b3 - (q - q⁻¹) • (a3 * b2) := by
  have := entry_crossing R q 0 1 2 3 (by decide) (by decide)
  calc b3 * a2 = a2 * b3 - (a2 * b3 - b3 * a2) := by abel
       _       = a2 * b3 - (q - q⁻¹) • (a3 * b2) := by rw [this]

-- p01 * p23 expansions
lemma term1_01_23 : a0 * b1 * (a2 * b3) = a0 * a2 * b1 * b3 := by
  calc a0 * b1 * (a2 * b3) = a0 * (b1 * a2) * b3 := by simp only [mul_assoc]
       _                   = a0 * (a2 * b1) * b3 := by rw [b1_a2 q]
       _                   = a0 * a2 * b1 * b3   := by simp only [mul_assoc]

lemma term2_01_23 : a0 * b1 * (a3 * b2) = a0 * a3 * b1 * b2 := by
  calc a0 * b1 * (a3 * b2) = a0 * (b1 * a3) * b2 := by simp only [mul_assoc]
       _                   = a0 * (a3 * b1) * b2 := by rw [b1_a3 q]
       _                   = a0 * a3 * b1 * b2   := by simp only [mul_assoc]

lemma term3_01_23 : a1 * b0 * (a2 * b3) = a1 * a2 * b0 * b3 := by
  calc a1 * b0 * (a2 * b3) = a1 * (b0 * a2) * b3 := by simp only [mul_assoc]
       _                   = a1 * (a2 * b0) * b3 := by rw [b0_a2 q]
       _                   = a1 * a2 * b0 * b3   := by simp only [mul_assoc]

lemma term4_01_23 : a1 * b0 * (a3 * b2) = a1 * a3 * b0 * b2 := by
  calc a1 * b0 * (a3 * b2) = a1 * (b0 * a3) * b2 := by simp only [mul_assoc]
       _                   = a1 * (a3 * b0) * b2 := by rw [b0_a3 q]
       _                   = a1 * a3 * b0 * b2   := by simp only [mul_assoc]

lemma p01_p23_expand : p01 * p23 =
    a0 * a2 * b1 * b3 -
    q • (a0 * a3 * b1 * b2) -
    q • (a1 * a2 * b0 * b3) +
    q^2 • (a1 * a3 * b0 * b2) := by
  calc p01 * p23
    _ = (a0 * b1 - q • (a1 * b0)) * (a2 * b3 - q • (a3 * b2)) := rfl
    _ = a0 * b1 * (a2 * b3) - q • (a0 * b1 * (a3 * b2)) -
        q • (a1 * b0 * (a2 * b3)) + q^2 • (a1 * b0 * (a3 * b2)) := by rw [expand_binomial]
    _ = a0 * a2 * b1 * b3 - q • (a0 * a3 * b1 * b2) -
        q • (a1 * a2 * b0 * b3) + q^2 • (a1 * a3 * b0 * b2) := by
        rw [term1_01_23 q, term2_01_23 q, term3_01_23 q, term4_01_23 q]

-- p02 * p13 expansions
lemma term1_02_13 : a0 * b2 * (a1 * b3) = a0 * a1 * b2 * b3 - (q - q⁻¹) • (a0 * a2 * b1 * b3) := by
  calc a0 * b2 * (a1 * b3)
    _ = a0 * (b2 * a1) * b3 := by simp only [mul_assoc]
    _ = a0 * (a1 * b2 - (q - q⁻¹) • (a2 * b1)) * b3 := by rw [b2_a1 q]
    _ = a0 * a1 * b2 * b3 - (q - q⁻¹) • (a0 * a2 * b1 * b3) := by
        simp only [mul_sub, sub_mul, mul_assoc, mul_smul_comm, smul_mul_assoc]

lemma term2_02_13 : q • (a0 * b2 * (a3 * b1)) = a0 * a3 * b1 * b2 := by
  calc q • (a0 * b2 * (a3 * b1))
    _ = q • (a0 * (b2 * a3) * b1) := by simp only [mul_assoc]
    _ = q • (a0 * (a3 * b2) * b1) := by rw [b2_a3 q]
    _ = a0 * a3 * (q • (b2 * b1)) := by simp only [mul_assoc, smul_mul_assoc, mul_smul_comm]
    _ = a0 * a3 * (b1 * b2) := by rw [← b2_b1 q]
    _ = a0 * a3 * b1 * b2 := by simp only [mul_assoc]

lemma term3_02_13 : q • (a2 * b0 * (a1 * b3)) = a1 * a2 * b0 * b3 := by
  calc q • (a2 * b0 * (a1 * b3))
    _ = q • (a2 * (b0 * a1) * b3) := by simp only [mul_assoc]
    _ = q • (a2 * (a1 * b0) * b3) := by rw [b0_a1 q]
    _ = (q • (a2 * a1)) * b0 * b3 := by simp only [mul_assoc, smul_mul_assoc, mul_smul_comm]
    _ = (a1 * a2) * b0 * b3 := by rw [← a2_a1 q]
    _ = a1 * a2 * b0 * b3 := by simp only [mul_assoc]

lemma term4_02_13 : q^2 • (a2 * b0 * (a3 * b1)) = q^2 • (a2 * a3 * b0 * b1) := by
  calc q^2 • (a2 * b0 * (a3 * b1))
    _ = q^2 • (a2 * (b0 * a3) * b1) := by simp only [mul_assoc]
    _ = q^2 • (a2 * (a3 * b0) * b1) := by rw [b0_a3 q]
    _ = q^2 • (a2 * a3 * b0 * b1) := by simp only [mul_assoc]

lemma q_p02_p13_expand : q • (p02 * p13) =
    q • (a0 * a1 * b2 * b3) - (q * (q - q⁻¹)) • (a0 * a2 * b1 * b3) -
    q • (a0 * a3 * b1 * b2) - q • (a1 * a2 * b0 * b3) + q^3 • (a2 * a3 * b0 * b1) := by
  calc q • (p02 * p13)
    _ = q • ((a0 * b2 - q • (a2 * b0)) * (a1 * b3 - q • (a3 * b1))) := rfl
    _ = q • (a0 * b2 * (a1 * b3) - q • (a0 * b2 * (a3 * b1)) -
             q • (a2 * b0 * (a1 * b3)) + q^2 • (a2 * b0 * (a3 * b1))) := by rw [expand_binomial]
    _ = q • (a0 * b2 * (a1 * b3)) - q • (q • (a0 * b2 * (a3 * b1))) -
        q • (q • (a2 * b0 * (a1 * b3))) + q • (q^2 • (a2 * b0 * (a3 * b1))) := by
        simp only [smul_sub, smul_add]
    _ = q • (a0 * a1 * b2 * b3 - (q - q⁻¹) • (a0 * a2 * b1 * b3)) -
        q • (a0 * a3 * b1 * b2) - q • (a1 * a2 * b0 * b3) +
        q^3 • (a2 * a3 * b0 * b1) := by
        rw [term1_02_13 q, term2_02_13 q, term3_02_13 q, term4_02_13 q]
        have hq3 : q * q^2 = q^3 := by ring
        rw [smul_smul, hq3]
    _ = q • (a0 * a1 * b2 * b3) - (q * (q - q⁻¹)) • (a0 * a2 * b1 * b3) -
        q • (a0 * a3 * b1 * b2) - q • (a1 * a2 * b0 * b3) +
        q^3 • (a2 * a3 * b0 * b1) := by
        simp only [smul_sub, smul_smul]

-- p03 * p12 expansions
lemma term1_03_12 : q^2 • (a0 * b3 * (a1 * b2)) =
    q • (a0 * a1 * b2 * b3) - (q^2 * (q - q⁻¹)) • (a0 * a3 * b1 * b2) := by
  calc q^2 • (a0 * b3 * (a1 * b2))
    _ = q^2 • (a0 * (b3 * a1) * b2) := by simp only [mul_assoc]
    _ = q^2 • (a0 * (a1 * b3 - (q - q⁻¹) • (a3 * b1)) * b2) := by rw [b3_a1 q]
    _ = q^2 • (a0 * a1 * b3 * b2 - (q - q⁻¹) • (a0 * a3 * b1 * b2)) := by
        simp only [mul_sub, sub_mul, mul_assoc, smul_mul_assoc, mul_smul_comm]
    _ = q^2 • (a0 * a1 * b3 * b2) - q^2 • ((q - q⁻¹) • (a0 * a3 * b1 * b2)) := by rw [smul_sub]
    _ = q • (q • (a0 * a1 * b3 * b2)) - (q^2 * (q - q⁻¹)) • (a0 * a3 * b1 * b2) := by
        have hsq : q^2 = q * q := by ring
        nth_rewrite 1 [hsq]
        rw [smul_smul, smul_smul]
    _ = q • (a0 * a1 * (q • (b3 * b2))) - (q^2 * (q - q⁻¹)) • (a0 * a3 * b1 * b2) := by
        simp only [smul_mul_assoc, mul_smul_comm]
    _ = q • (a0 * a1 * (b2 * b3)) - (q^2 * (q - q⁻¹)) • (a0 * a3 * b1 * b2) := by
        rw [← b3_b2 q]
    _ = q • (a0 * a1 * b2 * b3) - (q^2 * (q - q⁻¹)) • (a0 * a3 * b1 * b2) := by simp only [mul_assoc]

lemma term2_03_12 : q^3 • (a0 * b3 * (a2 * b1)) =
    q^2 • (a0 * a2 * b1 * b3) - (q^2 * (q - q⁻¹)) • (a0 * a3 * b1 * b2) := by
  calc q^3 • (a0 * b3 * (a2 * b1))
    _ = q^3 • (a0 * (b3 * a2) * b1) := by simp only [mul_assoc]
    _ = q^3 • (a0 * (a2 * b3 - (q - q⁻¹) • (a3 * b2)) * b1) := by rw [b3_a2 q]
    _ = q^3 • (a0 * a2 * b3 * b1 - (q - q⁻¹) • (a0 * a3 * b2 * b1)) := by
        simp only [mul_sub, sub_mul, mul_assoc, smul_mul_assoc, mul_smul_comm]
    _ = q^3 • (a0 * a2 * b3 * b1) - q^3 • ((q - q⁻¹) • (a0 * a3 * b2 * b1)) := by rw [smul_sub]
    _ = (q^2 * q) • (a0 * a2 * b3 * b1) - (q^2 * (q - q⁻¹) * q) • (a0 * a3 * b2 * b1) := by
        have eq1 : q^3 = q^2 * q := by ring
        have eq2 : q^3 * (q - q⁻¹) = q^2 * (q - q⁻¹) * q := by ring
        nth_rewrite 1 [eq1]
        rw [smul_smul, eq2, smul_smul]
    _ = q^2 • (a0 * a2 * (q • (b3 * b1))) - (q^2 * (q - q⁻¹)) • (a0 * a3 * (q • (b2 * b1))) := by
        simp only [smul_mul_assoc, mul_smul_comm]
    _ = q^2 • (a0 * a2 * (b1 * b3)) - (q^2 * (q - q⁻¹)) • (a0 * a3 * (b1 * b2)) := by
        rw [← b3_b1 q, ← b2_b1 q]
    _ = q^2 • (a0 * a2 * b1 * b3) - (q^2 * (q - q⁻¹)) • (a0 * a3 * b1 * b2) := by simp only [mul_assoc]

lemma term3_03_12 : q^3 • (a3 * b0 * (a1 * b2)) = q^2 • (a1 * a3 * b0 * b2) := by
  calc q^3 • (a3 * b0 * (a1 * b2))
    _ = q^3 • (a3 * (b0 * a1) * b2) := by simp only [mul_assoc]
    _ = q^3 • (a3 * (a1 * b0) * b2) := by rw [b0_a1 q]
    _ = (q^2 * q) • (a3 * a1 * b0 * b2) := by
        have eq1 : q^3 = q^2 * q := by ring
        rw [eq1, mul_assoc, mul_assoc]
    _ = q^2 • (q • (a3 * a1 * b0 * b2)) := by rw [smul_smul]
    _ = q^2 • ((q • (a3 * a1)) * b0 * b2) := by simp only [smul_mul_assoc, mul_smul_comm]
    _ = q^2 • ((a1 * a3) * b0 * b2) := by rw [← a3_a1 q]
    _ = q^2 • (a1 * a3 * b0 * b2) := by simp only [mul_assoc]

lemma term4_03_12 : q^4 • (a3 * b0 * (a2 * b1)) = q^3 • (a2 * a3 * b0 * b1) := by
  calc q^4 • (a3 * b0 * (a2 * b1))
    _ = q^4 • (a3 * (b0 * a2) * b1) := by simp only [mul_assoc]
    _ = q^4 • (a3 * (a2 * b0) * b1) := by rw [b0_a2 q]
    _ = (q^3 * q) • (a3 * a2 * b0 * b1) := by
        have eq1 : q^4 = q^3 * q := by ring
        rw [eq1, mul_assoc, mul_assoc]
    _ = q^3 • (q • (a3 * a2 * b0 * b1)) := by rw [smul_smul]
    _ = q^3 • ((q • (a3 * a2)) * b0 * b1) := by simp only [smul_mul_assoc, mul_smul_comm]
    _ = q^3 • ((a2 * a3) * b0 * b1) := by rw [← a3_a2 q]
    _ = q^3 • (a2 * a3 * b0 * b1) := by simp only [mul_assoc]

lemma q2_p03_p12_expand : q^2 • (p03 * p12) =
    q • (a0 * a1 * b2 * b3) - (q^2 * (q - q⁻¹)) • (a0 * a3 * b1 * b2) -
    q^2 • (a0 * a2 * b1 * b3) + (q^2 * (q - q⁻¹)) • (a0 * a3 * b1 * b2) -
    q^2 • (a1 * a3 * b0 * b2) + q^3 • (a2 * a3 * b0 * b1) := by
  calc q^2 • (p03 * p12)
    _ = q^2 • ((a0 * b3 - q • (a3 * b0)) * (a1 * b2 - q • (a2 * b1))) := rfl
    _ = q^2 • (a0 * b3 * (a1 * b2) - q • (a0 * b3 * (a2 * b1)) -
             q • (a3 * b0 * (a1 * b2)) + q^2 • (a3 * b0 * (a2 * b1))) := by rw [expand_binomial]
    _ = q^2 • (a0 * b3 * (a1 * b2)) - q^2 • (q • (a0 * b3 * (a2 * b1))) -
        q^2 • (q • (a3 * b0 * (a1 * b2))) + q^2 • (q^2 • (a3 * b0 * (a2 * b1))) := by
        simp only [smul_sub, smul_add]
    _ = q^2 • (a0 * b3 * (a1 * b2)) - q^3 • (a0 * b3 * (a2 * b1)) -
        q^3 • (a3 * b0 * (a1 * b2)) + q^4 • (a3 * b0 * (a2 * b1)) := by
        have h3 : q^2 * q = q^3 := by ring
        have h4 : q^2 * q^2 = q^4 := by ring
        rw [← smul_smul, h3, ← smul_smul, h3, ← smul_smul, h4]
    _ = q • (a0 * a1 * b2 * b3) - (q^2 * (q - q⁻¹)) • (a0 * a3 * b1 * b2) -
        (q^2 • (a0 * a2 * b1 * b3) - (q^2 * (q - q⁻¹)) • (a0 * a3 * b1 * b2)) -
        q^2 • (a1 * a3 * b0 * b2) + q^3 • (a2 * a3 * b0 * b1) := by
        rw [term1_03_12 q, term2_03_12 q, term3_03_12 q, term4_03_12 q]
    _ = q • (a0 * a1 * b2 * b3) - (q^2 * (q - q⁻¹)) • (a0 * a3 * b1 * b2) -
        q^2 • (a0 * a2 * b1 * b3) + (q^2 * (q - q⁻¹)) • (a0 * a3 * b1 * b2) -
        q^2 • (a1 * a3 * b0 * b2) + q^3 • (a2 * a3 * b0 * b1) := by
        abel

lemma quantumPlucker_of_q_zero (hq : q = 0) :
    p01 * p23 - q • (p02 * p13) + q^2 • (p03 * p12) = 0 := by
  rw [hq]
  simp only [zero_smul, sub_zero, add_zero, zero_pow (by decide)]
  rw [p01_p23_expand q, hq]
  simp only [zero_smul, sub_zero, add_zero, zero_pow (by decide)]
  have a0_a2_eq : a0 * a2 = q • (a2 * a0) := entry_sameRow R q 0 0 2 (by decide)
  rw [a0_a2_eq, hq]
  simp only [zero_smul, zero_mul]

lemma quantumPlucker_of_q_ne_zero (hq : q ≠ 0) :
    p01 * p23 - q • (p02 * p13) + q^2 • (p03 * p12) = 0 := by
  rw [p01_p23_expand q, q_p02_p13_expand q, q2_p03_p12_expand q]
  generalize hM1 : a0 * a2 * b1 * b3 = M1
  generalize hM2 : a0 * a3 * b1 * b2 = M2
  generalize hM3 : a1 * a2 * b0 * b3 = M3
  generalize hM4 : a1 * a3 * b0 * b2 = M4
  generalize hM5 : a0 * a1 * b2 * b3 = M5
  generalize hM6 : a2 * a3 * b0 * b1 = M6
  
  have h1 : M1 = 1 • M1 := by simp
  nth_rewrite 1 [h1]
  
  have h_grouped : (1 • M1 - q • M2 - q • M3 + q^2 • M4)
      - (q • M5 - (q * (q - q⁻¹)) • M1 - q • M2 - q • M3 + q^3 • M6)
      + (q • M5 - (q^2 * (q - q⁻¹)) • M2 - q^2 • M1 + (q^2 * (q - q⁻¹)) • M2 - q^2 • M4 + q^3 • M6)
    = (1 + q * (q - q⁻¹) - q^2) • M1
      + (-q + q - q^2 * (q - q⁻¹) + q^2 * (q - q⁻¹)) • M2
      + (-q + q) • M3
      + (q^2 - q^2) • M4
      + (-q + q) • M5
      + (-q^3 + q^3) • M6 := by
    simp only [add_smul, sub_smul, neg_smul]
    abel

  rw [h_grouped]

  have coeff_M1 : 1 + q * (q - q⁻¹) - q^2 = 0 := by
    calc 1 + q * (q - q⁻¹) - q^2
      _ = 1 + q^2 - q * q⁻¹ - q^2 := by ring
      _ = 1 + q^2 - 1 - q^2 := by rw [mul_inv_cancel₀ hq]
      _ = 0 := by ring

  have coeff_M2 : -q + q - q^2 * (q - q⁻¹) + q^2 * (q - q⁻¹) = 0 := by ring
  have coeff_M3 : -q + q = 0 := by ring
  have coeff_M4 : q^2 - q^2 = 0 := by ring
  have coeff_M5 : -q + q = 0 := by ring
  have coeff_M6 : -q^3 + q^3 = 0 := by ring

  rw [coeff_M1, coeff_M2, coeff_M3, coeff_M4, coeff_M5, coeff_M6]
  simp only [zero_smul, add_zero]

/--
The q-Plücker exchange relation among the six ordered quantum minors 
of the 2x4 quantum matrix algebra.
-/
theorem quantum_plucker_exchange :
    (quantumMinor R q ⟨(0, 1), by decide⟩) * (quantumMinor R q ⟨(2, 3), by decide⟩)
    - q • ((quantumMinor R q ⟨(0, 2), by decide⟩) * (quantumMinor R q ⟨(1, 3), by decide⟩))
    + q^2 • ((quantumMinor R q ⟨(0, 3), by decide⟩) * (quantumMinor R q ⟨(1, 2), by decide⟩)) = 0 := by
  by_cases hq : q = 0
  · exact quantumPlucker_of_q_zero q hq
  · exact quantumPlucker_of_q_ne_zero q hq

end InfoGeometry.Projective.QuantumGrassmannian
