import re

with open("lean/InfoGeometry/Projective/Sandbox/QuantumPluckerExchange.lean", "r") as f:
    text = f.read()

# I will just write a completely flat tactic block for each.
# Actually, let's just use `multi_replace_file_content` equivalent using Python string replacement for the proofs.

q_p02_p13_proof = """lemma q_p02_p13_expand (hq : q ≠ 0) : q • (p02 * p13) =
    q • (a0 * a1 * b2 * b3) - (q^2 - 1) • (a0 * a2 * b1 * b3) - q • (a0 * a3 * b1 * b2) -
    q • (a1 * a2 * b0 * b3) + q^3 • (a2 * a3 * b0 * b1) := by
  calc q • (p02 * p13)
    _ = q • ((a0 * b2 - q • (a2 * b0)) * (a1 * b3 - q • (a3 * b1))) := rfl
    _ = q • (a0 * b2 * (a1 * b3) - q • (a0 * b2 * (a3 * b1)) -
             q • (a2 * b0 * (a1 * b3)) + q^2 • (a2 * b0 * (a3 * b1))) := by 
        rw [expand_binomial (a0 * b2) (a2 * b0) (a1 * b3) (a3 * b1) q]
    _ = q • (a0 * b2 * (a1 * b3)) - q • q • (a0 * b2 * (a3 * b1)) -
        q • q • (a2 * b0 * (a1 * b3)) + q • q^2 • (a2 * b0 * (a3 * b1)) := by
        simp only [smul_sub, smul_add]
    _ = q • (a0 * (b2 * a1) * b3) - q^2 • (a0 * (b2 * a3) * b1) -
        q^2 • (a2 * (b0 * a1) * b3) + q^3 • (a2 * (b0 * a3) * b1) := by
        have h2 : q * q = q^2 := by ring
        have h3 : q * q^2 = q^3 := by ring
        rw [smul_smul q q, h2, smul_smul q q, h2, smul_smul q (q^2), h3]
        simp only [mul_assoc]
    _ = q • (a0 * (a1 * b2 - (q - q⁻¹) • (a2 * b1)) * b3) - q^2 • (a0 * (a3 * b2) * b1) -
        q^2 • (a2 * (a1 * b0) * b3) + q^3 • (a2 * (a3 * b0) * b1) := by
        rw [b2_a1 q, b2_a3 q, b0_a1 q, b0_a3 q]
    _ = q • (a0 * a1 * b2 * b3 - a0 * ((q - q⁻¹) • (a2 * b1)) * b3) - q^2 • (a0 * a3 * b2 * b1) -
        q^2 • (a2 * a1 * b0 * b3) + q^3 • (a2 * a3 * b0 * b1) := by
        simp only [mul_assoc, mul_sub, sub_mul]
    _ = q • (a0 * a1 * b2 * b3 - (q - q⁻¹) • (a0 * a2 * b1 * b3)) - q^2 • (a0 * a3 * b2 * b1) -
        q^2 • (a2 * a1 * b0 * b3) + q^3 • (a2 * a3 * b0 * b1) := by
        simp only [mul_assoc]
        rw [Algebra.mul_smul_comm (q - q⁻¹) a0, Algebra.smul_mul_assoc (q - q⁻¹) (a0 * (a2 * b1))]
        simp only [mul_assoc]
    _ = q • (a0 * a1 * b2 * b3) - (q * (q - q⁻¹)) • (a0 * a2 * b1 * b3) - q^2 • (a0 * a3 * b2 * b1) -
        q^2 • (a2 * a1 * b0 * b3) + q^3 • (a2 * a3 * b0 * b1) := by
        simp only [smul_sub]
        rw [smul_smul q (q - q⁻¹)]
    _ = q • (a0 * a1 * b2 * b3) - (q * (q - q⁻¹)) • (a0 * a2 * b1 * b3) - q^2 • (a0 * a3 * (q⁻¹ • (b1 * b2))) -
        q^2 • ((q⁻¹ • (a1 * a2)) * b0 * b3) + q^3 • (a2 * a3 * b0 * b1) := by
        simp only [mul_assoc]
        have hb2b1 : b2 * b1 = q⁻¹ • (b1 * b2) := b2_b1 q hq
        have ha2a1 : a2 * a1 = q⁻¹ • (a1 * a2) := a2_a1 q hq
        rw [hb2b1, ha2a1]
    _ = q • (a0 * a1 * b2 * b3) - (q * (q - q⁻¹)) • (a0 * a2 * b1 * b3) - q^2 • (q⁻¹ • (a0 * a3 * b1 * b2)) -
        q^2 • (q⁻¹ • (a1 * a2 * b0 * b3)) + q^3 • (a2 * a3 * b0 * b1) := by
        simp only [mul_assoc]
        rw [Algebra.mul_smul_comm q⁻¹ (a0 * a3), Algebra.smul_mul_assoc q⁻¹ (a1 * a2)]
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
        rw [hh1, smul_smul (q^2) q⁻¹, hh2, smul_smul (q^2) q⁻¹, hh2]"""

q2_p03_p12_proof = """lemma q2_p03_p12_expand (hq : q ≠ 0) : q^2 • (p03 * p12) =
    q^2 • (a0 * a1 * b3 * b2) - (q^3 - q) • (a0 * a3 * b1 * b2) -
    q^3 • (a0 * a2 * b3 * b1) + (q^4 - q^2) • (a0 * a3 * b2 * b1) -
    q^3 • (a3 * a1 * b0 * b2) + q^4 • (a3 * a2 * b0 * b1) := by
  calc q^2 • (p03 * p12)
    _ = q^2 • ((a0 * b3 - q • (a3 * b0)) * (a1 * b2 - q • (a2 * b1))) := rfl
    _ = q^2 • (a0 * b3 * (a1 * b2) - q • (a0 * b3 * (a2 * b1)) -
               q • (a3 * b0 * (a1 * b2)) + q^2 • (a3 * b0 * (a2 * b1))) := by 
        rw [expand_binomial (a0 * b3) (a3 * b0) (a1 * b2) (a2 * b1) q]
    _ = q^2 • (a0 * b3 * (a1 * b2)) - q^2 • q • (a0 * b3 * (a2 * b1)) -
        q^2 • q • (a3 * b0 * (a1 * b2)) + q^2 • q^2 • (a3 * b0 * (a2 * b1)) := by
        simp only [smul_sub, smul_add]
    _ = q^2 • (a0 * (b3 * a1) * b2) - q^3 • (a0 * (b3 * a2) * b1) -
        q^3 • (a3 * (b0 * a1) * b2) + q^4 • (a3 * (b0 * a2) * b1) := by
        have h3 : q^2 * q = q^3 := by ring
        have h4 : q^2 * q^2 = q^4 := by ring
        rw [smul_smul (q^2) q, h3, smul_smul (q^2) q, h3, smul_smul (q^2) (q^2), h4]
        simp only [mul_assoc]
    _ = q^2 • (a0 * (a1 * b3 - (q - q⁻¹) • (a3 * b1)) * b2) - q^3 • (a0 * (a2 * b3 - (q - q⁻¹) • (a3 * b2)) * b1) -
        q^3 • (a3 * (a1 * b0) * b2) + q^4 • (a3 * (a2 * b0) * b1) := by
        rw [b3_a1 q, b3_a2 q, b0_a1 q, b0_a2 q]
    _ = q^2 • (a0 * a1 * b3 * b2 - a0 * ((q - q⁻¹) • (a3 * b1)) * b2) - q^3 • (a0 * a2 * b3 * b1 - a0 * ((q - q⁻¹) • (a3 * b2)) * b1) -
        q^3 • (a3 * a1 * b0 * b2) + q^4 • (a3 * a2 * b0 * b1) := by
        simp only [mul_assoc, mul_sub, sub_mul]
    _ = q^2 • (a0 * a1 * b3 * b2 - (q - q⁻¹) • (a0 * a3 * b1 * b2)) - q^3 • (a0 * a2 * b3 * b1 - (q - q⁻¹) • (a0 * a3 * b2 * b1)) -
        q^3 • (a3 * a1 * b0 * b2) + q^4 • (a3 * a2 * b0 * b1) := by
        simp only [mul_assoc]
        rw [Algebra.mul_smul_comm (q - q⁻¹) a0, Algebra.smul_mul_assoc (q - q⁻¹) (a0 * (a3 * b1))]
        rw [Algebra.mul_smul_comm (q - q⁻¹) a0, Algebra.smul_mul_assoc (q - q⁻¹) (a0 * (a3 * b2))]
        simp only [mul_assoc]
    _ = q^2 • (a0 * a1 * b3 * b2) - (q^2 * (q - q⁻¹)) • (a0 * a3 * b1 * b2) -
        q^3 • (a0 * a2 * b3 * b1) + (q^3 * (q - q⁻¹)) • (a0 * a3 * b2 * b1) -
        q^3 • (a3 * a1 * b0 * b2) + q^4 • (a3 * a2 * b0 * b1) := by
        simp only [smul_sub]
        rw [smul_smul (q^2) (q - q⁻¹), smul_smul (q^3) (q - q⁻¹)]
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
        rw [h5, h6]"""

q2_p03_p12_proof_rewritten = """lemma q2_p03_p12_expand_rewritten (hq : q ≠ 0) : q^2 • (p03 * p12) =
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
        simp only [mul_assoc]
        rw [Algebra.mul_smul_comm q⁻¹ a1, Algebra.mul_smul_comm q⁻¹ a0]
        rw [Algebra.mul_smul_comm q⁻¹ a2, Algebra.mul_smul_comm q⁻¹ a0]
        rw [Algebra.mul_smul_comm q⁻¹ a3, Algebra.mul_smul_comm q⁻¹ a0]
        rw [Algebra.smul_mul_assoc q⁻¹ (a1 * a3), Algebra.smul_mul_assoc q⁻¹ (a2 * a3)]
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
        rw [smul_smul (q^2) q⁻¹, hh1, smul_smul (q^3) q⁻¹, hh2, smul_smul (q^4 - q^2) q⁻¹, hh3, smul_smul (q^3) q⁻¹, hh2, smul_smul (q^4) q⁻¹, hh4]"""

start1 = text.find("lemma q_p02_p13_expand")
end1 = text.find("lemma q2_p03_p12_expand")
text = text[:start1] + q_p02_p13_proof + "\n\n" + text[end1:]

start2 = text.find("lemma q2_p03_p12_expand")
end2 = text.find("lemma q2_p03_p12_expand_rewritten")
text = text[:start2] + q2_p03_p12_proof + "\n\n" + text[end2:]

start3 = text.find("lemma q2_p03_p12_expand_rewritten")
end3 = text.find("lemma quantumPlucker_of_q_zero")
text = text[:start3] + q2_p03_p12_proof_rewritten + "\n\n" + text[end3:]

with open("lean/InfoGeometry/Projective/Sandbox/QuantumPluckerExchange.lean", "w") as f:
    f.write(text)
