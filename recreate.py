code = """import Mathlib.Algebra.FreeAlgebra
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

lemma smul_smul_fwd {A : Type u} [Ring A] [Algebra R A] (c d : R) (x : A) :
  c • d • x = (c * d) • x := smul_smul c d x

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
      rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]
      have h : q * q = q^2 := by ring
      rw [h]

lemma p01_p23_expand : p01 * p23 =
    a0 * a2 * b1 * b3 - q • (a0 * a3 * b1 * b2) -
    q • (a1 * a2 * b0 * b3) + q^2 • (a1 * a3 * b0 * b2) := by
  calc p01 * p23
    _ = (a0 * b1 - q • (a1 * b0)) * (a2 * b3 - q • (a3 * b2)) := rfl
    _ = a0 * b1 * (a2 * b3) - q • (a0 * b1 * (a3 * b2)) -
        q • (a1 * b0 * (a2 * b3)) + q^2 • (a1 * b0 * (a3 * b2)) := by
        have h_exp := expand_binomial (a0 * b1) (a1 * b0) (a2 * b3) (a3 * b2) q
        rw [h_exp]
    _ = a0 * (b1 * a2) * b3 - q • (a0 * (b1 * a3) * b2) -
        q • (a1 * (b0 * a2) * b3) + q^2 • (a1 * (b0 * a3) * b2) := by 
        simp only [mul_assoc]
    _ = a0 * (a2 * b1) * b3 - q • (a0 * (a3 * b1) * b2) -
        q • (a1 * (a2 * b0) * b3) + q^2 • (a1 * (a3 * b0) * b2) := by
        rw [b1_a2 q, b1_a3 q, b0_a2 q, b0_a3 q]
    _ = a0 * a2 * b1 * b3 - q • (a0 * a3 * b1 * b2) -
        q • (a1 * a2 * b0 * b3) + q^2 • (a1 * a3 * b0 * b2) := by
        simp only [mul_assoc]

lemma q_p02_p13_expand (hq : q ≠ 0) : q • (p02 * p13) =
    q • (a0 * a1 * b2 * b3) - (q^2 - 1) • (a0 * a2 * b1 * b3) - q • (a0 * a3 * b1 * b2) -
    q • (a1 * a2 * b0 * b3) + q^3 • (a2 * a3 * b0 * b1) := by
  calc q • (p02 * p13)
    _ = q • ((a0 * b2 - q • (a2 * b0)) * (a1 * b3 - q • (a3 * b1))) := rfl
    _ = q • (a0 * b2 * (a1 * b3) - q • (a0 * b2 * (a3 * b1)) -
             q • (a2 * b0 * (a1 * b3)) + q^2 • (a2 * b0 * (a3 * b1))) := by 
        have h_exp := expand_binomial (a0 * b2) (a2 * b0) (a1 * b3) (a3 * b1) q
        rw [h_exp]
    _ = q • (a0 * b2 * (a1 * b3)) - q • q • (a0 * b2 * (a3 * b1)) -
        q • q • (a2 * b0 * (a1 * b3)) + q • q^2 • (a2 * b0 * (a3 * b1)) := by
        simp only [smul_sub, smul_add]
    _ = q • (a0 * (b2 * a1) * b3) - q^2 • (a0 * (b2 * a3) * b1) -
        q^2 • (a2 * (b0 * a1) * b3) + q^3 • (a2 * (b0 * a3) * b1) := by
        have h2 : q * q = q^2 := by ring
        have h3 : q * q^2 = q^3 := by ring
        rw [smul_smul_fwd, h2, smul_smul_fwd, h2, smul_smul_fwd, h3]
        simp only [mul_assoc]
    _ = q • (a0 * (a1 * b2 - (q - q⁻¹) • (a2 * b1)) * b3) - q^2 • (a0 * (a3 * b2) * b1) -
        q^2 • (a2 * (a1 * b0) * b3) + q^3 • (a2 * (a3 * b0) * b1) := by
        rw [b2_a1 q, b2_a3 q, b0_a1 q, b0_a3 q]
    _ = q • (a0 * a1 * b2 * b3 - a0 * ((q - q⁻¹) • (a2 * b1)) * b3) - q^2 • (a0 * a3 * b2 * b1) -
        q^2 • (a2 * a1 * b0 * b3) + q^3 • (a2 * a3 * b0 * b1) := by
        simp only [mul_assoc, mul_sub, sub_mul]
    _ = q • (a0 * a1 * b2 * b3 - (q - q⁻¹) • (a0 * a2 * b1 * b3)) - q^2 • (a0 * a3 * b2 * b1) -
        q^2 • (a2 * a1 * b0 * b3) + q^3 • (a2 * a3 * b0 * b1) := by
        rw [smul_pull_right (q - q⁻¹) a0 (a2 * b1), smul_pull_left (q - q⁻¹) (a0 * (a2 * b1)) b3]
        simp only [mul_assoc]
    _ = q • (a0 * a1 * b2 * b3) - (q * (q - q⁻¹)) • (a0 * a2 * b1 * b3) - q^2 • (a0 * a3 * b2 * b1) -
        q^2 • (a2 * a1 * b0 * b3) + q^3 • (a2 * a3 * b0 * b1) := by
        simp only [smul_sub]
        rw [smul_smul_fwd q (q - q⁻¹) (a0 * a2 * b1 * b3)]
    _ = q • (a0 * a1 * b2 * b3) - (q * (q - q⁻¹)) • (a0 * a2 * b1 * b3) - q^2 • (a0 * a3 * (q⁻¹ • (b1 * b2))) -
        q^2 • ((q⁻¹ • (a1 * a2)) * b0 * b3) + q^3 • (a2 * a3 * b0 * b1) := by
        have hb2b1 : b2 * b1 = q⁻¹ • (b1 * b2) := b2_b1 q hq
        have ha2a1 : a2 * a1 = q⁻¹ • (a1 * a2) := a2_a1 q hq
        rw [hb2b1, ha2a1]
    _ = q • (a0 * a1 * b2 * b3) - (q * (q - q⁻¹)) • (a0 * a2 * b1 * b3) - q^2 • (q⁻¹ • (a0 * a3 * b1 * b2)) -
        q^2 • (q⁻¹ • (a1 * a2 * b0 * b3)) + q^3 • (a2 * a3 * b0 * b1) := by
        rw [smul_pull_right q⁻¹ (a0 * a3) (b1 * b2), smul_pull_left q⁻¹ (a1 * a2) (b0 * b3)]
        simp only [mul_assoc]
    _ = q • (a0 * a1 * b2 * b3) - (q^2 - 1) • (a0 * a2 * b1 * b3) - q • (a0 * a3 * b1 * b2) -
        q • (a1 * a2 * b0 * b3) + q^3 • (a2 * a3 * b0 * b1) := by
        have hh1 : q * (q - q⁻¹) = q^2 - 1 := by
          calc q * (q - q⁻¹) = q^2 - q * q⁻¹ := by ring
               _ = q^2 - 1 := by rw [mul_inv_cancel₀ hq]
        have hh2 : q^2 * q⁻¹ = q := by
          calc q^2 * q⁻¹ = q * (q * q⁻¹) := by ring
               _ = q * 1 := by rw [mul_inv_cancel₀ hq]
               _ = q := by ring
        rw [hh1, smul_smul_fwd, hh2, smul_smul_fwd, hh2]

lemma q2_p03_p12_expand (hq : q ≠ 0) : q^2 • (p03 * p12) =
    q^2 • (a0 * a1 * b3 * b2) - (q^3 - q) • (a0 * a3 * b1 * b2) -
    q^3 • (a0 * a2 * b3 * b1) + (q^4 - q^2) • (a0 * a3 * b2 * b1) -
    q^3 • (a3 * a1 * b0 * b2) + q^4 • (a3 * a2 * b0 * b1) := by
  calc q^2 • (p03 * p12)
    _ = q^2 • ((a0 * b3 - q • (a3 * b0)) * (a1 * b2 - q • (a2 * b1))) := rfl
    _ = q^2 • (a0 * b3 * (a1 * b2) - q • (a0 * b3 * (a2 * b1)) -
               q • (a3 * b0 * (a1 * b2)) + q^2 • (a3 * b0 * (a2 * b1))) := by 
        have h_exp := expand_binomial (a0 * b3) (a3 * b0) (a1 * b2) (a2 * b1) q
        rw [h_exp]
    _ = q^2 • (a0 * b3 * (a1 * b2)) - q^2 • q • (a0 * b3 * (a2 * b1)) -
        q^2 • q • (a3 * b0 * (a1 * b2)) + q^2 • q^2 • (a3 * b0 * (a2 * b1)) := by
        simp only [smul_sub, smul_add]
    _ = q^2 • (a0 * (b3 * a1) * b2) - q^3 • (a0 * (b3 * a2) * b1) -
        q^3 • (a3 * (b0 * a1) * b2) + q^4 • (a3 * (b0 * a2) * b1) := by
        have h3 : q^2 * q = q^3 := by ring
        have h4 : q^2 * q^2 = q^4 := by ring
        rw [smul_smul_fwd, h3, smul_smul_fwd, h3, smul_smul_fwd, h4]
        simp only [mul_assoc]
    _ = q^2 • (a0 * (a1 * b3 - (q - q⁻¹) • (a3 * b1)) * b2) - q^3 • (a0 * (a2 * b3 - (q - q⁻¹) • (a3 * b2)) * b1) -
        q^3 • (a3 * (a1 * b0) * b2) + q^4 • (a3 * (a2 * b0) * b1) := by
        rw [b3_a1 q, b3_a2 q, b0_a1 q, b0_a2 q]
    _ = q^2 • (a0 * a1 * b3 * b2 - a0 * ((q - q⁻¹) • (a3 * b1)) * b2) - q^3 • (a0 * a2 * b3 * b1 - a0 * ((q - q⁻¹) • (a3 * b2)) * b1) -
        q^3 • (a3 * a1 * b0 * b2) + q^4 • (a3 * a2 * b0 * b1) := by
        simp only [mul_assoc, mul_sub, sub_mul]
    _ = q^2 • (a0 * a1 * b3 * b2 - (q - q⁻¹) • (a0 * a3 * b1 * b2)) - q^3 • (a0 * a2 * b3 * b1 - (q - q⁻¹) • (a0 * a3 * b2 * b1)) -
        q^3 • (a3 * a1 * b0 * b2) + q^4 • (a3 * a2 * b0 * b1) := by
        rw [smul_pull_right (q - q⁻¹) a0 (a3 * b1), smul_pull_left (q - q⁻¹) (a0 * (a3 * b1)) b2]
        rw [smul_pull_right (q - q⁻¹) a0 (a3 * b2), smul_pull_left (q - q⁻¹) (a0 * (a3 * b2)) b1]
        simp only [mul_assoc]
    _ = q^2 • (a0 * a1 * b3 * b2) - (q^2 * (q - q⁻¹)) • (a0 * a3 * b1 * b2) -
        q^3 • (a0 * a2 * b3 * b1) + (q^3 * (q - q⁻¹)) • (a0 * a3 * b2 * b1) -
        q^3 • (a3 * a1 * b0 * b2) + q^4 • (a3 * a2 * b0 * b1) := by
        simp only [smul_sub]
        rw [smul_smul_fwd q^2 (q - q⁻¹) (a0 * a3 * b1 * b2), smul_smul_fwd q^3 (q - q⁻¹) (a0 * a3 * b2 * b1)]
    _ = q^2 • (a0 * a1 * b3 * b2) - (q^3 - q) • (a0 * a3 * b1 * b2) -
        q^3 • (a0 * a2 * b3 * b1) + (q^4 - q^2) • (a0 * a3 * b2 * b1) -
        q^3 • (a3 * a1 * b0 * b2) + q^4 • (a3 * a2 * b0 * b1) := by
        have h5 : q^2 * (q - q⁻¹) = q^3 - q := by
          calc q^2 * (q - q⁻¹) = q^3 - q^2 * q⁻¹ := by ring
               _ = q^3 - q * (q * q⁻¹) := by ring
               _ = q^3 - q * 1 := by rw [mul_inv_cancel₀ hq]
               _ = q^3 - q := by ring
        have h6 : q^3 * (q - q⁻¹) = q^4 - q^2 := by
          calc q^3 * (q - q⁻¹) = q^4 - q^3 * q⁻¹ := by ring
               _ = q^4 - q^2 * (q * q⁻¹) := by ring
               _ = q^4 - q^2 * 1 := by rw [mul_inv_cancel₀ hq]
               _ = q^4 - q^2 := by ring
        rw [h5, h6]

lemma q2_p03_p12_expand_rewritten (hq : q ≠ 0) : q^2 • (p03 * p12) =
    q • (a0 * a1 * b2 * b3) - (q^3 - q) • (a0 * a3 * b1 * b2) -
    q^2 • (a0 * a2 * b1 * b3) + (q^3 - q) • (a0 * a3 * b1 * b2) -
    q^2 • (a1 * a3 * b0 * b2) + q^3 • (a2 * a3 * b0 * b1) := by
  have h_exp := q2_p03_p12_expand q hq
  calc q^2 • (p03 * p12)
    _ = q^2 • (a0 * a1 * b3 * b2) - (q^3 - q) • (a0 * a3 * b1 * b2) -
        q^3 • (a0 * a2 * b3 * b1) + (q^4 - q^2) • (a0 * a3 * b2 * b1) -
        q^3 • (a3 * a1 * b0 * b2) + q^4 • (a3 * a2 * b0 * b1) := by rw [h_exp]
    _ = q^2 • (a0 * a1 * (q⁻¹ • (b2 * b3))) - (q^3 - q) • (a0 * a3 * b1 * b2) -
        q^3 • (a0 * a2 * (q⁻¹ • (b1 * b3))) + (q^4 - q^2) • (a0 * a3 * (q⁻¹ • (b1 * b2))) -
        q^3 • (q⁻¹ • (a1 * a3) * b0 * b2) + q^4 • (q⁻¹ • (a2 * a3) * b0 * b1) := by
        simp only [mul_assoc]
        have hb3b2 : b3 * b2 = q⁻¹ • (b2 * b3) := b3_b2 q hq
        have hb3b1 : b3 * b1 = q⁻¹ • (b1 * b3) := b3_b1 q hq
        have hb2b1 : b2 * b1 = q⁻¹ • (b1 * b2) := b2_b1 q hq
        have ha3a1 : a3 * a1 = q⁻¹ • (a1 * a3) := a3_a1 q hq
        have ha3a2 : a3 * a2 = q⁻¹ • (a2 * a3) := a3_a2 q hq
        rw [hb3b2, hb3b1, hb2b1, ha3a1, ha3a2]
    _ = q^2 • (q⁻¹ • (a0 * a1 * b2 * b3)) - (q^3 - q) • (a0 * a3 * b1 * b2) -
        q^3 • (q⁻¹ • (a0 * a2 * b1 * b3)) + (q^4 - q^2) • (q⁻¹ • (a0 * a3 * b1 * b2)) -
        q^3 • (q⁻¹ • (a1 * a3 * b0 * b2)) + q^4 • (q⁻¹ • (a2 * a3 * b0 * b1)) := by
        rw [smul_pull_right q⁻¹ a1 (b2 * b3), smul_pull_right q⁻¹ a0 (a1 * (b2 * b3))]
        rw [smul_pull_right q⁻¹ a2 (b1 * b3), smul_pull_right q⁻¹ a0 (a2 * (b1 * b3))]
        rw [smul_pull_right q⁻¹ a3 (b1 * b2), smul_pull_right q⁻¹ a0 (a3 * (b1 * b2))]
        rw [smul_pull_left q⁻¹ (a1 * a3) (b0 * b2), smul_pull_left q⁻¹ (a2 * a3) (b0 * b1)]
        simp only [mul_assoc]
    _ = q • (a0 * a1 * b2 * b3) - (q^3 - q) • (a0 * a3 * b1 * b2) -
        q^2 • (a0 * a2 * b1 * b3) + (q^3 - q) • (a0 * a3 * b1 * b2) -
        q^2 • (a1 * a3 * b0 * b2) + q^3 • (a2 * a3 * b0 * b1) := by
        have hh1 : q^2 * q⁻¹ = q := by
          calc q^2 * q⁻¹ = q * (q * q⁻¹) := by ring
               _ = q * 1 := by rw [mul_inv_cancel₀ hq]
               _ = q := by ring
        have hh2 : q^3 * q⁻¹ = q^2 := by
          calc q^3 * q⁻¹ = q^2 * (q * q⁻¹) := by ring
               _ = q^2 * 1 := by rw [mul_inv_cancel₀ hq]
               _ = q^2 := by ring
        have hh3 : (q^4 - q^2) * q⁻¹ = q^3 - q := by
          calc (q^4 - q^2) * q⁻¹ = q^4 * q⁻¹ - q^2 * q⁻¹ := by ring
               _ = q^3 * (q * q⁻¹) - q * (q * q⁻¹) := by ring
               _ = q^3 * 1 - q * 1 := by rw [mul_inv_cancel₀ hq]
               _ = q^3 - q := by ring
        have hh4 : q^4 * q⁻¹ = q^3 := by
          calc q^4 * q⁻¹ = q^3 * (q * q⁻¹) := by ring
               _ = q^3 * 1 := by rw [mul_inv_cancel₀ hq]
               _ = q^3 := by ring
        rw [smul_smul_fwd, hh1, smul_smul_fwd, hh2, smul_smul_fwd, hh3, smul_smul_fwd, hh2, smul_smul_fwd, hh4]

lemma quantumPlucker_of_q_zero (hq : q = 0) :
    p01 * p23 - q • (p02 * p13) + q^2 • (p03 * p12) = 0 := by
  have a0_a2_eq : a0 * a2 = q • (a2 * a0) := entry_sameRow R q 0 0 2 (by decide)
  have a0_a2_zero : a0 * a2 = 0 := by
    calc a0 * a2 = q • (a2 * a0) := a0_a2_eq
         _ = (0:R) • (a2 * a0) := by rw [hq]
         _ = 0 := zero_smul R (a2 * a0)
  have hp01 : p01 * p23 = 0 := by
    calc p01 * p23
      _ = a0 * a2 * b1 * b3 - q • (a0 * a3 * b1 * b2) - q • (a1 * a2 * b0 * b3) + q^2 • (a1 * a3 * b0 * b2) := p01_p23_expand q
      _ = (a0 * a2) * (b1 * b3) - q • (a0 * a3 * b1 * b2) - q • (a1 * a2 * b0 * b3) + q^2 • (a1 * a3 * b0 * b2) := by simp only [mul_assoc]
      _ = 0 * (b1 * b3) - q • (a0 * a3 * b1 * b2) - q • (a1 * a2 * b0 * b3) + q^2 • (a1 * a3 * b0 * b2) := by rw [a0_a2_zero]
      _ = 0 - q • (a0 * a3 * b1 * b2) - q • (a1 * a2 * b0 * b3) + q^2 • (a1 * a3 * b0 * b2) := by simp only [zero_mul]
      _ = 0 - (0:R) • (a0 * a3 * b1 * b2) - (0:R) • (a1 * a2 * b0 * b3) + (0:R)^2 • (a1 * a3 * b0 * b2) := by rw [hq]
      _ = 0 - 0 - 0 + 0 := by
          have hz1 : (0:R) • (a0 * a3 * b1 * b2) = 0 := zero_smul R _
          have hz2 : (0:R) • (a1 * a2 * b0 * b3) = 0 := zero_smul R _
          have hz3 : (0:R)^2 • (a1 * a3 * b0 * b2) = 0 := by 
            have hq2 : (0:R)^2 = 0 := by ring
            rw [hq2]
            exact zero_smul R _
          rw [hz1, hz2, hz3]
      _ = 0 := by abel
  have hp02 : q • (p02 * p13) = 0 := by
    calc q • (p02 * p13)
      _ = (0:R) • (p02 * p13) := by rw [hq]
      _ = 0 := zero_smul R _
  have hp03 : q^2 • (p03 * p12) = 0 := by
    calc q^2 • (p03 * p12)
      _ = (0:R)^2 • (p03 * p12) := by rw [hq]
      _ = 0 := by 
        have hq2 : (0:R)^2 = 0 := by ring
        rw [hq2]
        exact zero_smul R _
  rw [hp01, hp02, hp03]
  abel

lemma quantumPlucker_of_q_ne_zero (hq : q ≠ 0) :
    p01 * p23 - q • (p02 * p13) + q^2 • (p03 * p12) = 0 := by
  have h1 := p01_p23_expand q
  have h2 := q_p02_p13_expand q hq
  have h3 := q2_p03_p12_expand_rewritten q hq
  calc p01 * p23 - q • (p02 * p13) + q^2 • (p03 * p12)
    _ = (a0 * a2 * b1 * b3 - q • (a0 * a3 * b1 * b2) - q • (a1 * a2 * b0 * b3) + q^2 • (a1 * a3 * b0 * b2)) -
        (q • (a0 * a1 * b2 * b3) - (q^2 - 1) • (a0 * a2 * b1 * b3) - q • (a0 * a3 * b1 * b2) -
         q • (a1 * a2 * b0 * b3) + q^3 • (a2 * a3 * b0 * b1)) +
        (q • (a0 * a1 * b2 * b3) - (q^3 - q) • (a0 * a3 * b1 * b2) - q^2 • (a0 * a2 * b1 * b3) +
         (q^3 - q) • (a0 * a3 * b1 * b2) - q^2 • (a1 * a3 * b0 * b2) + q^3 • (a2 * a3 * b0 * b1)) := by rw [h1, h2, h3]
    _ = a0 * a2 * b1 * b3 + (q^2 - 1) • (a0 * a2 * b1 * b3) - q^2 • (a0 * a2 * b1 * b3) := by abel_nf
    _ = (1 : R) • (a0 * a2 * b1 * b3) + (q^2 - 1) • (a0 * a2 * b1 * b3) - q^2 • (a0 * a2 * b1 * b3) := by
        nth_rewrite 1 [← one_smul R (a0 * a2 * b1 * b3)]
        rfl
    _ = (1 + (q^2 - 1) - q^2) • (a0 * a2 * b1 * b3) := by
        rw [← add_smul, ← sub_smul]
    _ = (0 : R) • (a0 * a2 * b1 * b3) := by 
        have h_zero : 1 + (q^2 - 1) - q^2 = 0 := by ring
        rw [h_zero]
    _ = 0 := zero_smul R (a0 * a2 * b1 * b3)

theorem quantum_plucker_exchange :
    p01 * p23 - q • (p02 * p13) + q^2 • (p03 * p12) = 0 := by
  by_cases hq : q = 0
  · exact quantumPlucker_of_q_zero q hq
  · exact quantumPlucker_of_q_ne_zero q hq

end InfoGeometry.Projective.QuantumGrassmannian
"""
with open("lean/InfoGeometry/Projective/Sandbox/QuantumPluckerExchange.lean", "w") as f:
    f.write(code)
