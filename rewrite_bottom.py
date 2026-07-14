import re

with open("lean/InfoGeometry/Projective/QuantumPluckerExchange.lean", "r") as f:
    text = f.read()

# We will cut the text before `lemma q2_p03_p12_expand_rewritten`
parts = text.split("lemma q2_p03_p12_expand_rewritten")
top_part = parts[0]

bottom_part = """lemma q2_p03_p12_expand_rewritten (hq : q ≠ 0) : q^2 • (p03 * p12) =
    q • (a0 * a1 * b2 * b3) - (q^3 - q) • (a0 * a3 * b1 * b2) -
    q^2 • (a0 * a2 * b1 * b3) + (q^3 - q) • (a0 * a3 * b1 * b2) -
    q^2 • (a1 * a3 * b0 * b2) + q^3 • (a2 * a3 * b0 * b1) := by
  have h_exp := q2_p03_p12_expand q hq
  calc q^2 • (p03 * p12)
    _ = q^2 • (a0 * a1 * b3 * b2) - (q^3 - q) • (a0 * a3 * b1 * b2) -
        q^3 • (a0 * a2 * b3 * b1) + (q^4 - q^2) • (a0 * a3 * b2 * b1) -
        q^3 • (a3 * a1 * b0 * b2) + q^4 • (a3 * a2 * b0 * b1) := by rw [h_exp]
    _ = q^2 • (a0 * (a1 * (b3 * b2))) - (q^3 - q) • (a0 * (a3 * (b1 * b2))) -
        q^3 • (a0 * (a2 * (b3 * b1))) + (q^4 - q^2) • (a0 * (a3 * (b2 * b1))) -
        q^3 • (a3 * (a1 * (b0 * b2))) + q^4 • (a3 * (a2 * (b0 * b1))) := by simp only [mul_assoc]
    _ = q^2 • (a0 * (a1 * (q⁻¹ • (b2 * b3)))) - (q^3 - q) • (a0 * (a3 * (b1 * b2))) -
        q^3 • (a0 * (a2 * (q⁻¹ • (b1 * b3)))) + (q^4 - q^2) • (a0 * (a3 * (q⁻¹ • (b1 * b2)))) -
        q^3 • ((q⁻¹ • (a1 * a3)) * (b0 * b2)) + q^4 • ((q⁻¹ • (a2 * a3)) * (b0 * b1)) := by
        rw [b3_b2 q hq, b3_b1 q hq, b2_b1 q hq, a3_a1 q hq, a3_a2 q hq]
    _ = q^2 • q⁻¹ • (a0 * (a1 * (b2 * b3))) - (q^3 - q) • (a0 * (a3 * (b1 * b2))) -
        q^3 • q⁻¹ • (a0 * (a2 * (b1 * b3))) + (q^4 - q^2) • q⁻¹ • (a0 * (a3 * (b1 * b2))) -
        q^3 • q⁻¹ • (a1 * (a3 * (b0 * b2))) + q^4 • q⁻¹ • (a2 * (a3 * (b0 * b1))) := by
        simp only [smul_pull_right, smul_pull_left, mul_assoc]
    _ = q • (a0 * (a1 * (b2 * b3))) - (q^3 - q) • (a0 * (a3 * (b1 * b2))) -
        q^2 • (a0 * (a2 * (b1 * b3))) + (q^3 - q) • (a0 * (a3 * (b1 * b2))) -
        q^2 • (a1 * (a3 * (b0 * b2))) + q^3 • (a2 * (a3 * (b0 * b1))) := by
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
    _ = q • (a0 * a1 * b2 * b3) - (q^3 - q) • (a0 * a3 * b1 * b2) -
        q^2 • (a0 * a2 * b1 * b3) + (q^3 - q) • (a0 * a3 * b1 * b2) -
        q^2 • (a1 * a3 * b0 * b2) + q^3 • (a2 * a3 * b0 * b1) := by simp only [mul_assoc]

lemma quantumPlucker_of_q_zero (hq : q = 0) :
    p01 * p23 - q • (p02 * p13) + q^2 • (p03 * p12) = 0 := by
  have a0_a2_eq : a0 * a2 = q • (a2 * a0) := entry_sameRow R q 0 0 2 (by decide)
  have a0_a2_zero : a0 * a2 = 0 := by
    rw [hq] at a0_a2_eq
    rw [a0_a2_eq]
    exact zero_smul R (a2 * a0)
  have hp01 : p01 * p23 = 0 := by
    have h1 := p01_p23_expand q
    rw [h1]
    have h_assoc : a0 * a2 * b1 * b3 = (a0 * a2) * (b1 * b3) := by simp only [mul_assoc]
    rw [h_assoc, a0_a2_zero]
    simp only [zero_mul, sub_zero, zero_add]
    rw [hq]
    exact zero_smul R (a0 * a3 * b1 * b2 - a1 * a2 * b0 * b3) -- actually just rewrite hq first, then simplify?
  -- Wait, the terms are separated!
  -- Let's just use calc for hp01 to be safe:
  -- We don't need calc.
  
  -- Re-doing hp01 the safe way:
  -- p01 * p23 = a0 * a2 * b1 * b3 - q • (a0 * a3 * b1 * b2) - q • (a1 * a2 * b0 * b3) + q^2 • (a1 * a3 * b0 * b2)
  -- rw [hq] everywhere makes q=0
  -- rw [a0_a2_zero] makes the first term 0
  -- Let's just rw [p01_p23_expand q, hq, a0_a2_zero] and then use zero_smul !

  -- Wait, I'll use explicit terms.

lemma quantumPlucker_of_q_zero_safe (hq : q = 0) :
    p01 * p23 - q • (p02 * p13) + q^2 • (p03 * p12) = 0 := by
  have a0_a2_eq : a0 * a2 = q • (a2 * a0) := entry_sameRow R q 0 0 2 (by decide)
  have a0_a2_zero : a0 * a2 = 0 := by
    rw [hq] at a0_a2_eq
    rw [a0_a2_eq]
    exact zero_smul R (a2 * a0)
  have hp01 : p01 * p23 = 0 := by
    rw [p01_p23_expand q]
    have h_assoc : a0 * a2 * b1 * b3 = (a0 * a2) * (b1 * b3) := by simp only [mul_assoc]
    rw [h_assoc, a0_a2_zero]
    simp only [zero_mul, zero_add, sub_zero, zero_sub]
    rw [hq]
    have hz1 : (0:R) • (a0 * a3 * b1 * b2) = 0 := zero_smul R _
    have hz2 : (0:R) • (a1 * a2 * b0 * b3) = 0 := zero_smul R _
    have hq2 : (0:R)^2 = 0 := by change (0:R) * (0:R) = 0; ring
    rw [hz1, hz2, hq2]
    have hz3 : (0:R) • (a1 * a3 * b0 * b2) = 0 := zero_smul R _
    rw [hz3]
    abel
  have hp02 : q • (p02 * p13) = 0 := by
    rw [hq]
    exact zero_smul R _
  have hp03 : q^2 • (p03 * p12) = 0 := by
    rw [hq]
    have hq2 : (0:R)^2 = 0 := by change (0:R) * (0:R) = 0; ring
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
  · exact quantumPlucker_of_q_zero_safe q hq
  · exact quantumPlucker_of_q_ne_zero q hq

end InfoGeometry.Projective.QuantumGrassmannian
"""

new_text = top_part + bottom_part

with open("lean/InfoGeometry/Projective/QuantumPluckerExchange.lean", "w") as f:
    f.write(new_text)
