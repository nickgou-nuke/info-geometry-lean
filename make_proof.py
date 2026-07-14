def generate_plucker():
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

lemma expand_binomial {A : Type u} [Ring A] [Algebra R A] (X Y Z W : A) (q : R) :
  (X - q • Y) * (Z - q • W) = X * Z - q • (X * W) - q • (Y * Z) + q^2 • (Y * W) := by
  calc (X - q • Y) * (Z - q • W)
    _ = X * Z - X * (q • W) - (q • Y) * Z + (q • Y) * (q • W) := by
      rw [sub_mul, mul_sub, mul_sub]
      abel
    _ = X * Z - q • (X * W) - q • (Y * Z) + q^2 • (Y * W) := by
      simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul, sq]

variable (hq : q ≠ 0)

"""
    for i, j in [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]:
        code += f"""lemma a{j}_a{i} (hq : q ≠ 0) : a{j} * a{i} = q⁻¹ • (a{i} * a{j}) := by
  have h := entry_sameRow R q 0 {i} {j} (by decide)
  calc a{j} * a{i} = 1 • (a{j} * a{i}) := by simp
       _ = (q⁻¹ * q) • (a{j} * a{i}) := by rw [inv_mul_cancel₀ hq]
       _ = q⁻¹ • (q • (a{j} * a{i})) := by rw [mul_smul]
       _ = q⁻¹ • (a{i} * a{j}) := by rw [← h]
"""

    code += "\n"
    for i, j in [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]:
        code += f"""lemma b{j}_b{i} (hq : q ≠ 0) : b{j} * b{i} = q⁻¹ • (b{i} * b{j}) := by
  have h := entry_sameRow R q 1 {i} {j} (by decide)
  calc b{j} * b{i} = 1 • (b{j} * b{i}) := by simp
       _ = (q⁻¹ * q) • (b{j} * b{i}) := by rw [inv_mul_cancel₀ hq]
       _ = q⁻¹ • (q • (b{j} * b{i})) := by rw [mul_smul]
       _ = q⁻¹ • (b{i} * b{j}) := by rw [← h]
"""

    code += """
lemma b0_a1 : b0 * a1 = a1 * b0 := (entry_separated R q 0 1 1 0 (by decide) (by decide)).symm
lemma b0_a2 : b0 * a2 = a2 * b0 := (entry_separated R q 0 1 2 0 (by decide) (by decide)).symm
lemma b0_a3 : b0 * a3 = a3 * b0 := (entry_separated R q 0 1 3 0 (by decide) (by decide)).symm
lemma b1_a2 : b1 * a2 = a2 * b1 := (entry_separated R q 0 1 2 1 (by decide) (by decide)).symm
lemma b1_a3 : b1 * a3 = a3 * b1 := (entry_separated R q 0 1 3 1 (by decide) (by decide)).symm
lemma b2_a3 : b2 * a3 = a3 * b2 := (entry_separated R q 0 1 3 2 (by decide) (by decide)).symm

"""
    for j, l in [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]:
        code += f"""lemma b{l}_a{j} : b{l} * a{j} = a{j} * b{l} - (q - q⁻¹) • (a{l} * b{j}) := by
  have h := entry_crossing R q 0 1 {j} {l} (by decide) (by decide)
  calc b{l} * a{j} = a{j} * b{l} - (a{j} * b{l} - b{l} * a{j}) := by abel
       _           = a{j} * b{l} - (q - q⁻¹) • (a{l} * b{j}) := by rw [h]
"""
    
    code += """

lemma p01_p23_expand : p01 * p23 =
    a0 * a2 * b1 * b3 - q • (a0 * a3 * b1 * b2) -
    q • (a1 * a2 * b0 * b3) + q^2 • (a1 * a3 * b0 * b2) := by
  calc p01 * p23
    _ = (a0 * b1 - q • (a1 * b0)) * (a2 * b3 - q • (a3 * b2)) := rfl
    _ = a0 * b1 * (a2 * b3) - q • (a0 * b1 * (a3 * b2)) -
        q • (a1 * b0 * (a2 * b3)) + q^2 • (a1 * b0 * (a3 * b2)) := by rw [expand_binomial]
    _ = a0 * (b1 * a2) * b3 - q • (a0 * (b1 * a3) * b2) -
        q • (a1 * (b0 * a2) * b3) + q^2 • (a1 * (b0 * a3) * b2) := by simp only [mul_assoc]
    _ = a0 * (a2 * b1) * b3 - q • (a0 * (a3 * b1) * b2) -
        q • (a1 * (a2 * b0) * b3) + q^2 • (a1 * (a3 * b0) * b2) := by
        rw [b1_a2 q, b1_a3 q, b0_a2 q, b0_a3 q]
    _ = a0 * a2 * b1 * b3 - q • (a0 * a3 * b1 * b2) -
        q • (a1 * a2 * b0 * b3) + q^2 • (a1 * a3 * b0 * b2) := by simp only [mul_assoc]

lemma q_p02_p13_expand (hq : q ≠ 0) : q • (p02 * p13) =
    q • (a0 * a1 * b2 * b3) - (q * (q - q⁻¹)) • (a0 * a2 * b1 * b3) -
    q • (a0 * a3 * b1 * b2) - q • (a1 * a2 * b0 * b3) + q^3 • (a2 * a3 * b0 * b1) := by
  calc q • (p02 * p13)
    _ = q • ((a0 * b2 - q • (a2 * b0)) * (a1 * b3 - q • (a3 * b1))) := rfl
    _ = q • (a0 * b2 * (a1 * b3) - q • (a0 * b2 * (a3 * b1)) -
             q • (a2 * b0 * (a1 * b3)) + q^2 • (a2 * b0 * (a3 * b1))) := by rw [expand_binomial]
    _ = q • (a0 * b2 * (a1 * b3)) - q • q • (a0 * b2 * (a3 * b1)) -
        q • q • (a2 * b0 * (a1 * b3)) + q • q^2 • (a2 * b0 * (a3 * b1)) := by
        simp only [smul_sub, smul_add]
    _ = q • (a0 * (b2 * a1) * b3) - q^2 • (a0 * (b2 * a3) * b1) -
        q^2 • (a2 * (b0 * a1) * b3) + q^3 • (a2 * (b0 * a3) * b1) := by
        have h2 : q * q = q^2 := by ring
        have h3 : q * q^2 = q^3 := by ring
        rw [← smul_smul, ← smul_smul, ← smul_smul]
        rw [h2, h3]
        simp only [mul_assoc]
    _ = q • (a0 * (a1 * b2 - (q - q⁻¹) • (a2 * b1)) * b3) - q^2 • (a0 * (a3 * b2) * b1) -
        q^2 • (a2 * (a1 * b0) * b3) + q^3 • (a2 * (a3 * b0) * b1) := by
        rw [b2_a1 q, b2_a3 q, b0_a1 q, b0_a3 q]
    _ = q • (a0 * a1 * b2 * b3 - (q - q⁻¹) • (a0 * a2 * b1 * b3)) - q^2 • (a0 * a3 * b2 * b1) -
        q^2 • (a2 * a1 * b0 * b3) + q^3 • (a2 * a3 * b0 * b1) := by
        simp only [mul_sub, sub_mul, mul_assoc, smul_mul_assoc, Algebra.mul_smul_comm]
    _ = q • (a0 * a1 * b2 * b3) - q • (q - q⁻¹) • (a0 * a2 * b1 * b3) - q^2 • (a0 * a3 * (q⁻¹ • (b1 * b2))) -
        q^2 • (a2 * a1 * b0 * b3) + q^3 • (a2 * a3 * b0 * b1) := by
        rw [b2_b1 q hq, smul_sub]
    _ = q • (a0 * a1 * b2 * b3) - (q * (q - q⁻¹)) • (a0 * a2 * b1 * b3) - (q^2 * q⁻¹) • (a0 * a3 * b1 * b2) -
        q^2 • ((q⁻¹ • (a1 * a2)) * b0 * b3) + q^3 • (a2 * a3 * b0 * b1) := by
        rw [a2_a1 q hq, smul_smul, smul_smul]
        simp only [smul_mul_assoc, Algebra.mul_smul_comm, mul_assoc]
    _ = q • (a0 * a1 * b2 * b3) - (q * (q - q⁻¹)) • (a0 * a2 * b1 * b3) - q • (a0 * a3 * b1 * b2) -
        (q^2 * q⁻¹) • (a1 * a2 * b0 * b3) + q^3 • (a2 * a3 * b0 * b1) := by
        have hqq : q^2 * q⁻¹ = q := by
          calc q^2 * q⁻¹ = q * (q * q⁻¹) := by ring
               _ = q * 1 := by rw [mul_inv_cancel₀ hq]
               _ = q := by ring
        rw [hqq, smul_smul]
    _ = q • (a0 * a1 * b2 * b3) - (q * (q - q⁻¹)) • (a0 * a2 * b1 * b3) - q • (a0 * a3 * b1 * b2) -
        q • (a1 * a2 * b0 * b3) + q^3 • (a2 * a3 * b0 * b1) := by
        have hqq : q^2 * q⁻¹ = q := by
          calc q^2 * q⁻¹ = q * (q * q⁻¹) := by ring
               _ = q * 1 := by rw [mul_inv_cancel₀ hq]
               _ = q := by ring
        rw [hqq]

lemma q2_p03_p12_expand (hq : q ≠ 0) : q^2 • (p03 * p12) =
    q • (a0 * a1 * b2 * b3) - (q^2 * (q - q⁻¹)) • (a0 * a3 * b1 * b2) -
    q^2 • (a0 * a2 * b1 * b3) + (q^2 * (q - q⁻¹)) • (a0 * a3 * b1 * b2) -
    q^2 • (a1 * a3 * b0 * b2) + q^3 • (a2 * a3 * b0 * b1) := by
  calc q^2 • (p03 * p12)
    _ = q^2 • ((a0 * b3 - q • (a3 * b0)) * (a1 * b2 - q • (a2 * b1))) := rfl
    _ = q^2 • (a0 * b3 * (a1 * b2) - q • (a0 * b3 * (a2 * b1)) -
               q • (a3 * b0 * (a1 * b2)) + q^2 • (a3 * b0 * (a2 * b1))) := by rw [expand_binomial]
    _ = q^2 • (a0 * b3 * (a1 * b2)) - q^2 • q • (a0 * b3 * (a2 * b1)) -
        q^2 • q • (a3 * b0 * (a1 * b2)) + q^2 • q^2 • (a3 * b0 * (a2 * b1)) := by
        simp only [smul_sub, smul_add]
    _ = q^2 • (a0 * (b3 * a1) * b2) - q^3 • (a0 * (b3 * a2) * b1) -
        q^3 • (a3 * (b0 * a1) * b2) + (q^2 * q^2) • (a3 * (b0 * a2) * b1) := by
        have h3 : q^2 * q = q^3 := by ring
        rw [← smul_smul, ← smul_smul, ← smul_smul]
        rw [h3]
        simp only [mul_assoc]
    _ = q^2 • (a0 * (a1 * b3 - (q - q⁻¹) • (a3 * b1)) * b2) - q^3 • (a0 * (a2 * b3 - (q - q⁻¹) • (a3 * b2)) * b1) -
        q^3 • (a3 * (a1 * b0) * b2) + (q^2 * q^2) • (a3 * (a2 * b0) * b1) := by
        rw [b3_a1 q, b3_a2 q, b0_a1 q, b0_a2 q]
    _ = q^2 • (a0 * a1 * b3 * b2 - (q - q⁻¹) • (a0 * a3 * b1 * b2)) - q^3 • (a0 * a2 * b3 * b1 - (q - q⁻¹) • (a0 * a3 * b2 * b1)) -
        q^3 • (a3 * a1 * b0 * b2) + (q^2 * q^2) • (a3 * a2 * b0 * b1) := by
        simp only [mul_sub, sub_mul, mul_assoc, smul_mul_assoc, Algebra.mul_smul_comm]
    _ = q^2 • (a0 * a1 * b3 * b2) - q^2 • (q - q⁻¹) • (a0 * a3 * b1 * b2) -
        q^3 • (a0 * a2 * b3 * b1) + q^3 • (q - q⁻¹) • (a0 * a3 * b2 * b1) -
        q^3 • (a3 * a1 * b0 * b2) + (q^2 * q^2) • (a3 * a2 * b0 * b1) := by
        calc q^2 • (a0 * a1 * b3 * b2 - (q - q⁻¹) • (a0 * a3 * b1 * b2)) - q^3 • (a0 * a2 * b3 * b1 - (q - q⁻¹) • (a0 * a3 * b2 * b1)) - q^3 • (a3 * a1 * b0 * b2) + (q^2 * q^2) • (a3 * a2 * b0 * b1)
          _ = q^2 • (a0 * a1 * b3 * b2) - q^2 • (q - q⁻¹) • (a0 * a3 * b1 * b2) - (q^3 • (a0 * a2 * b3 * b1) - q^3 • (q - q⁻¹) • (a0 * a3 * b2 * b1)) - q^3 • (a3 * a1 * b0 * b2) + (q^2 * q^2) • (a3 * a2 * b0 * b1) := by rw [smul_sub, smul_sub]
          _ = q^2 • (a0 * a1 * b3 * b2) - q^2 • (q - q⁻¹) • (a0 * a3 * b1 * b2) - q^3 • (a0 * a2 * b3 * b1) + q^3 • (q - q⁻¹) • (a0 * a3 * b2 * b1) - q^3 • (a3 * a1 * b0 * b2) + (q^2 * q^2) • (a3 * a2 * b0 * b1) := by abel
    _ = q^2 • (a0 * a1 * (q⁻¹ • (b2 * b3))) - q^2 • (q - q⁻¹) • (a0 * a3 * b1 * b2) -
        q^3 • (a0 * a2 * (q⁻¹ • (b1 * b3))) + q^3 • (q - q⁻¹) • (a0 * a3 * (q⁻¹ • (b1 * b2))) -
        q^3 • ((q⁻¹ • (a1 * a3)) * b0 * b2) + (q^2 * q^2) • ((q⁻¹ • (a2 * a3)) * b0 * b1) := by
        rw [b3_b2 q hq, b3_b1 q hq, b2_b1 q hq, a3_a1 q hq, a3_a2 q hq]
    _ = (q^2 * q⁻¹) • (a0 * a1 * b2 * b3) - (q^2 * (q - q⁻¹)) • (a0 * a3 * b1 * b2) -
        (q^3 * q⁻¹) • (a0 * a2 * b1 * b3) + (q^3 * (q - q⁻¹) * q⁻¹) • (a0 * a3 * b1 * b2) -
        (q^3 * q⁻¹) • (a1 * a3 * b0 * b2) + (q^2 * q^2 * q⁻¹) • (a2 * a3 * b0 * b1) := by
        simp only [smul_mul_assoc, Algebra.mul_smul_comm, mul_assoc, smul_smul]
    _ = q • (a0 * a1 * b2 * b3) - (q^2 * (q - q⁻¹)) • (a0 * a3 * b1 * b2) -
        q^2 • (a0 * a2 * b1 * b3) + (q^2 * (q - q⁻¹)) • (a0 * a3 * b1 * b2) -
        q^2 • (a1 * a3 * b0 * b2) + q^3 • (a2 * a3 * b0 * b1) := by
        have h1 : q^2 * q⁻¹ = q := by
          calc q^2 * q⁻¹ = q * (q * q⁻¹) := by ring
               _ = q * 1 := by rw [mul_inv_cancel₀ hq]
               _ = q := by ring
        have h2 : q^3 * q⁻¹ = q^2 := by
          calc q^3 * q⁻¹ = q^2 * (q * q⁻¹) := by ring
               _ = q^2 * 1 := by rw [mul_inv_cancel₀ hq]
               _ = q^2 := by ring
        have h3 : q^3 * (q - q⁻¹) * q⁻¹ = q^2 * (q - q⁻¹) := by
          calc q^3 * (q - q⁻¹) * q⁻¹ = (q^3 * q⁻¹) * (q - q⁻¹) := by ring
               _ = q^2 * (q - q⁻¹) := by rw [h2]
        have h4 : q^2 * q^2 * q⁻¹ = q^3 := by
          calc q^2 * q^2 * q⁻¹ = q^3 * (q * q⁻¹) := by ring
               _ = q^3 * 1 := by rw [mul_inv_cancel₀ hq]
               _ = q^3 := by ring
        rw [h1, h2, h3, h4]

lemma quantumPlucker_of_q_zero (hq : q = 0) :
    p01 * p23 - q • (p02 * p13) + q^2 • (p03 * p12) = 0 := by
  have a0_a2_eq : a0 * a2 = q • (a2 * a0) := entry_sameRow R q 0 0 2 (by decide)
  have h_p01 : p01 * p23 = a0 * a2 * b1 * b3 - q • (a0 * a3 * b1 * b2) - q • (a1 * a2 * b0 * b3) + q^2 • (a1 * a3 * b0 * b2) := p01_p23_expand q
  rw [hq]
  simp only [zero_smul, sub_zero, add_zero, zero_pow (by decide)]
  rw [hq] at a0_a2_eq
  have a0_a2_zero : a0 * a2 = 0 := by
    calc a0 * a2 = 0 • (a2 * a0) := a0_a2_eq
         _ = 0 := by simp
  rw [hq] at h_p01
  simp only [zero_smul, sub_zero, add_zero, zero_pow (by decide)] at h_p01
  calc p01 * p23
    _ = a0 * a2 * b1 * b3 := h_p01
    _ = (a0 * a2) * b1 * b3 := by simp only [mul_assoc]
    _ = 0 * b1 * b3 := by rw [a0_a2_zero]
    _ = 0 := by simp

lemma quantumPlucker_of_q_ne_zero (hq : q ≠ 0) :
    p01 * p23 - q • (p02 * p13) + q^2 • (p03 * p12) = 0 := by
  have h1 : (q * (q - q⁻¹)) = q^2 - 1 := by
    calc q * (q - q⁻¹) = q^2 - q * q⁻¹ := by ring
         _ = q^2 - 1 := by rw [mul_inv_cancel₀ hq]
  have h2 : q^2 * (q - q⁻¹) = q^3 - q := by
    calc q^2 * (q - q⁻¹) = q^3 - q^2 * q⁻¹ := by ring
         _ = q^3 - q * (q * q⁻¹) := by ring
         _ = q^3 - q * 1 := by rw [mul_inv_cancel₀ hq]
         _ = q^3 - q := by ring
  rw [p01_p23_expand q, q_p02_p13_expand q hq, q2_p03_p12_expand q hq]
  rw [h1, h2]
  simp only [sub_smul, one_smul, smul_sub, smul_add]
  abel

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
"""
    with open("lean/InfoGeometry/Projective/QuantumPluckerExchange.lean", "w") as f:
        f.write(code)

if __name__ == "__main__":
    generate_plucker()
