with open("lean/InfoGeometry/Projective/QuantumPluckerExchange.lean", "r") as f:
    lines = f.read()

proof = """
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
        simp only [smul_smul_fwd, h2, h3, mul_assoc]
    _ = q • (a0 * (a1 * b2 - (q - q⁻¹) • (a2 * b1)) * b3) - q^2 • (a0 * (a3 * b2) * b1) -
        q^2 • (a2 * (a1 * b0) * b3) + q^3 • (a2 * (a3 * b0) * b1) := by
        rw [b2_a1 q, b2_a3 q, b0_a1 q, b0_a3 q]
    _ = q • (a0 * a1 * b2 * b3 - (q - q⁻¹) • (a0 * (a2 * b1) * b3)) - q^2 • (a0 * a3 * b2 * b1) -
        q^2 • (a2 * a1 * b0 * b3) + q^3 • (a2 * a3 * b0 * b1) := by
        simp only [mul_assoc, mul_sub, sub_mul, smul_pull_right, smul_pull_left]
    _ = q • (a0 * a1 * b2 * b3) - (q * (q - q⁻¹)) • (a0 * a2 * b1 * b3) - q^2 • (a0 * a3 * (q⁻¹ • (b1 * b2))) -
        q^2 • ((q⁻¹ • (a1 * a2)) * b0 * b3) + q^3 • (a2 * a3 * b0 * b1) := by
        rw [b2_b1 q hq, a2_a1 q hq]
        simp only [smul_sub, smul_pull_right, smul_pull_left, smul_smul_fwd]
    _ = q • (a0 * a1 * b2 * b3) - (q^2 - 1) • (a0 * a2 * b1 * b3) - q • (a0 * a3 * b1 * b2) -
        q • (a1 * a2 * b0 * b3) + q^3 • (a2 * a3 * b0 * b1) := by
        have hh1 : q * (q - q⁻¹) = q^2 - 1 := by
          calc q * (q - q⁻¹) = q^2 - q * q⁻¹ := by ring
               _ = q^2 - 1 := by rw [mul_inv_cancel₀ hq]
        have hh2 : q^2 * q⁻¹ = q := by
          calc q^2 * q⁻¹ = q * (q * q⁻¹) := by ring
               _ = q * 1 := by rw [mul_inv_cancel₀ hq]
               _ = q := by ring
        simp only [hh1, hh2, mul_assoc]

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
        simp only [smul_smul_fwd, h3, h4, mul_assoc]
    _ = q^2 • (a0 * (a1 * b3 - (q - q⁻¹) • (a3 * b1)) * b2) - q^3 • (a0 * (a2 * b3 - (q - q⁻¹) • (a3 * b2)) * b1) -
        q^3 • (a3 * (a1 * b0) * b2) + q^4 • (a3 * (a2 * b0) * b1) := by
        rw [b3_a1 q, b3_a2 q, b0_a1 q, b0_a2 q]
    _ = q^2 • (a0 * a1 * b3 * b2) - (q^2 * (q - q⁻¹)) • (a0 * a3 * b1 * b2) -
        q^3 • (a0 * a2 * b3 * b1) + (q^3 * (q - q⁻¹)) • (a0 * a3 * b2 * b1) -
        q^3 • (a3 * a1 * b0 * b2) + q^4 • (a3 * a2 * b0 * b1) := by
        simp only [mul_assoc, mul_sub, sub_mul, smul_pull_right, smul_pull_left, smul_sub, smul_smul_fwd]
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
        simp only [h5, h6]

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
        q^3 • ((q⁻¹ • (a1 * a3)) * b0 * b2) + q^4 • ((q⁻¹ • (a2 * a3)) * b0 * b1) := by
        rw [b3_b2 q hq, b3_b1 q hq, b2_b1 q hq, a3_a1 q hq, a3_a2 q hq]
    _ = q^2 • q⁻¹ • (a0 * a1 * (b2 * b3)) - (q^3 - q) • (a0 * a3 * b1 * b2) -
        q^3 • q⁻¹ • (a0 * a2 * (b1 * b3)) + (q^4 - q^2) • q⁻¹ • (a0 * a3 * (b1 * b2)) -
        q^3 • q⁻¹ • (a1 * a3 * b0 * b2) + q^4 • q⁻¹ • (a2 * a3 * b0 * b1) := by
        simp only [smul_pull_right, smul_pull_left, mul_assoc]
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
        simp only [hh1, hh2, hh3, hh4, smul_smul_fwd, mul_assoc]

lemma quantumPlucker_of_q_zero (hq : q = 0) :
    p01 * p23 - q • (p02 * p13) + q^2 • (p03 * p12) = 0 := by
  have a0_a2_eq : a0 * a2 = q • (a2 * a0) := entry_sameRow R q 0 0 2 (by decide)
  have a0_a2_zero : a0 * a2 = 0 := by
    calc a0 * a2 = q • (a2 * a0) := a0_a2_eq
         _ = 0 • (a2 * a0) := by rw [hq]
         _ = 0 := zero_smul R (a2 * a0)
  have p01_p23_zero : p01 * p23 = 0 := by
    have h_p01 : p01 * p23 = (a0 * a2) * b1 * b3 - q • (a0 * a3 * b1 * b2) - q • (a1 * a2 * b0 * b3) + q^2 • (a1 * a3 * b0 * b2) := by
      have h1 := p01_p23_expand q
      rw [h1]
      simp only [mul_assoc]
    rw [a0_a2_zero] at h_p01
    have h2 : 0 * b1 * b3 = 0 := by simp
    rw [h2] at h_p01
    rw [hq] at h_p01
    have h3 : 0 • (a0 * a3 * b1 * b2) = 0 := zero_smul R _
    have h4 : 0 • (a1 * a2 * b0 * b3) = 0 := zero_smul R _
    have h5 : (0:R)^2 = 0 := by change 0 * 0 = 0; rfl
    rw [h3, h4, h5] at h_p01
    have h6 : 0 • (a1 * a3 * b0 * b2) = 0 := zero_smul R _
    rw [h6] at h_p01
    exact (by abel : 0 - 0 - 0 + 0 = (0 : QuantumGrassmannian R q)) ▸ h_p01
  have hp02 : q • (p02 * p13) = 0 := by
    rw [hq]
    exact zero_smul R _
  have hp03 : q^2 • (p03 * p12) = 0 := by
    have hq2 : q^2 = 0 := by rw [hq]; change 0 * 0 = 0; rfl
    rw [hq2]
    exact zero_smul R _
  rw [p01_p23_zero, hp02, hp03]
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
    _ = 0 • (a0 * a2 * b1 * b3) := by 
        have h_zero : 1 + (q^2 - 1) - q^2 = 0 := by ring
        rw [h_zero]
    _ = 0 := by rw [zero_smul]

theorem quantum_plucker_exchange :
    p01 * p23 - q • (p02 * p13) + q^2 • (p03 * p12) = 0 := by
  by_cases hq : q = 0
  · exact quantumPlucker_of_q_zero q hq
  · exact quantumPlucker_of_q_ne_zero q hq

end InfoGeometry.Projective.QuantumGrassmannian
"""

lines = lines.replace("lemma quantumPlucker_of_q_ne_zero (hq : q ≠ 0) :\n    p01 * p23 - q • (p02 * p13) + q^2 • (p03 * p12) = 0 := by\n  sorry\n\nend InfoGeometry.Projective.QuantumGrassmannian", proof)

with open("lean/InfoGeometry/Projective/QuantumPluckerExchange.lean", "w") as f:
    f.write(lines)
