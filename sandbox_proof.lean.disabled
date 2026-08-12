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

lemma smul_pull_left {A : Type u} [Ring A] [Algebra R A] (c : R) (x y : A) :
  (c • x) * y = c • (x * y) := Algebra.smul_mul_assoc c x y

lemma smul_pull_right {A : Type u} [Ring A] [Algebra R A] (c : R) (x y : A) :
  x * (c • y) = c • (x * y) := Algebra.mul_smul_comm c x y

lemma smul_pull_both {A : Type u} [Ring A] [Algebra R A] (c d : R) (x y : A) :
  (c • x) * (d • y) = (c * d) • (x * y) := by
  rw [smul_pull_left, smul_pull_right, smul_smul]

variable (hq : q ≠ 0)

lemma b1_a2 : b1 * a2 = a2 * b1 := (entry_separated R q 0 1 2 1 (by decide) (by decide)).symm
lemma b1_a3 : b1 * a3 = a3 * b1 := (entry_separated R q 0 1 3 1 (by decide) (by decide)).symm
lemma b0_a2 : b0 * a2 = a2 * b0 := (entry_separated R q 0 1 2 0 (by decide) (by decide)).symm
lemma b0_a3 : b0 * a3 = a3 * b0 := (entry_separated R q 0 1 3 0 (by decide) (by decide)).symm
lemma b2_a3 : b2 * a3 = a3 * b2 := (entry_separated R q 0 1 3 2 (by decide) (by decide)).symm
lemma b0_a1 : b0 * a1 = a1 * b0 := (entry_separated R q 0 1 1 0 (by decide) (by decide)).symm

lemma b2_a1 : b2 * a1 = a1 * b2 - (q - q⁻¹) • (a2 * b1) := by
  have h := entry_crossing R q 0 1 1 2 (by decide) (by decide)
  calc b2 * a1 = a1 * b2 - (a1 * b2 - b2 * a1) := by abel
       _       = a1 * b2 - (q - q⁻¹) • (a2 * b1) := by rw [h]

lemma b3_a1 : b3 * a1 = a1 * b3 - (q - q⁻¹) • (a3 * b1) := by
  have h := entry_crossing R q 0 1 1 3 (by decide) (by decide)
  calc b3 * a1 = a1 * b3 - (a1 * b3 - b3 * a1) := by abel
       _       = a1 * b3 - (q - q⁻¹) • (a3 * b1) := by rw [h]

lemma b3_a2 : b3 * a2 = a2 * b3 - (q - q⁻¹) • (a3 * b2) := by
  have h := entry_crossing R q 0 1 2 3 (by decide) (by decide)
  calc b3 * a2 = a2 * b3 - (a2 * b3 - b3 * a2) := by abel
       _       = a2 * b3 - (q - q⁻¹) • (a3 * b2) := by rw [h]

lemma a2_a1 (hq : q ≠ 0) : a2 * a1 = q⁻¹ • (a1 * a2) := by
  have h := entry_sameRow R q 0 1 2 (by decide)
  calc a2 * a1 = (q⁻¹ * q) • (a2 * a1) := by rw [inv_mul_cancel₀ hq, one_smul]
       _ = q⁻¹ • (q • (a2 * a1)) := by rw [mul_smul]
       _ = q⁻¹ • (a1 * a2) := by rw [← h]

lemma a3_a1 (hq : q ≠ 0) : a3 * a1 = q⁻¹ • (a1 * a3) := by
  have h := entry_sameRow R q 0 1 3 (by decide)
  calc a3 * a1 = (q⁻¹ * q) • (a3 * a1) := by rw [inv_mul_cancel₀ hq, one_smul]
       _ = q⁻¹ • (q • (a3 * a1)) := by rw [mul_smul]
       _ = q⁻¹ • (a1 * a3) := by rw [← h]

lemma a3_a2 (hq : q ≠ 0) : a3 * a2 = q⁻¹ • (a2 * a3) := by
  have h := entry_sameRow R q 0 2 3 (by decide)
  calc a3 * a2 = (q⁻¹ * q) • (a3 * a2) := by rw [inv_mul_cancel₀ hq, one_smul]
       _ = q⁻¹ • (q • (a3 * a2)) := by rw [mul_smul]
       _ = q⁻¹ • (a2 * a3) := by rw [← h]

lemma b2_b1 (hq : q ≠ 0) : b2 * b1 = q⁻¹ • (b1 * b2) := by
  have h := entry_sameRow R q 1 1 2 (by decide)
  calc b2 * b1 = (q⁻¹ * q) • (b2 * b1) := by rw [inv_mul_cancel₀ hq, one_smul]
       _ = q⁻¹ • (q • (b2 * b1)) := by rw [mul_smul]
       _ = q⁻¹ • (b1 * b2) := by rw [← h]

lemma b3_b1 (hq : q ≠ 0) : b3 * b1 = q⁻¹ • (b1 * b3) := by
  have h := entry_sameRow R q 1 1 3 (by decide)
  calc b3 * b1 = (q⁻¹ * q) • (b3 * b1) := by rw [inv_mul_cancel₀ hq, one_smul]
       _ = q⁻¹ • (q • (b3 * b1)) := by rw [mul_smul]
       _ = q⁻¹ • (b1 * b3) := by rw [← h]

lemma b3_b2 (hq : q ≠ 0) : b3 * b2 = q⁻¹ • (b2 * b3) := by
  have h := entry_sameRow R q 1 2 3 (by decide)
  calc b3 * b2 = (q⁻¹ * q) • (b3 * b2) := by rw [inv_mul_cancel₀ hq, one_smul]
       _ = q⁻¹ • (q • (b3 * b2)) := by rw [mul_smul]
       _ = q⁻¹ • (b2 * b3) := by rw [← h]

@[simp] lemma expand_binomial {A : Type u} [Ring A] [Algebra R A] (X Y Z W : A) (q : R) :
  (X - q • Y) * (Z - q • W) = X * Z - q • (X * W) - q • (Y * Z) + q^2 • (Y * W) := by
  calc (X - q • Y) * (Z - q • W)
    _ = X * Z - (X * (q • W)) - ((q • Y) * Z) + ((q • Y) * (q • W)) := by
      rw [sub_mul, mul_sub, mul_sub]
      abel
    _ = X * Z - q • (X * W) - q • (Y * Z) + q^2 • (Y * W) := by
      rw [smul_pull_left, smul_pull_right, smul_pull_both]
      have h : q * q = q^2 := by ring
      rw [h]

lemma quantumPlucker_of_q_ne_zero (hq : q ≠ 0) :
    p01 * p23 - q • (p02 * p13) + q^2 • (p03 * p12) = 0 := by
  sorry

end InfoGeometry.Projective.QuantumGrassmannian
