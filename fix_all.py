import re

with open("lean/InfoGeometry/Projective/Sandbox/QuantumPluckerExchange.lean", "r") as f:
    text = f.read()

# Remove the custom lemmas
text = re.sub(r"lemma smul_pull_left.*?:= Algebra.smul_mul_assoc c x y\n\n", "", text, flags=re.DOTALL)
text = re.sub(r"lemma smul_pull_right.*?:= Algebra.mul_smul_comm c x y\n\n", "", text, flags=re.DOTALL)
text = re.sub(r"lemma smul_smul_fwd.*?:= smul_smul c d x\n\n", "", text, flags=re.DOTALL)

# Replace all occurrences
text = text.replace("smul_pull_right (q - q⁻¹) a0 (a2 * b1)", "Algebra.mul_smul_comm (q - q⁻¹) a0")
text = text.replace("smul_pull_left (q - q⁻¹) (a0 * (a2 * b1)) b3", "Algebra.smul_mul_assoc (q - q⁻¹) (a0 * a2 * b1)")

text = text.replace("smul_smul_fwd q (q - q⁻¹) (a0 * a2 * b1 * b3)", "smul_smul q (q - q⁻¹)")

text = text.replace("smul_pull_right q⁻¹ (a0 * a3) (b1 * b2)", "Algebra.mul_smul_comm q⁻¹ (a0 * a3)")
text = text.replace("smul_pull_left q⁻¹ (a1 * a2) (b0 * b3)", "Algebra.smul_mul_assoc q⁻¹ (a1 * a2)")

text = text.replace("rw [hh1, smul_smul_fwd, hh2, smul_smul_fwd, hh2]", "rw [hh1, smul_smul (q^2) q⁻¹, hh2, smul_smul (q^2) q⁻¹, hh2]")

text = text.replace("smul_pull_right (q - q⁻¹) a0 (a3 * b1)", "Algebra.mul_smul_comm (q - q⁻¹) a0")
text = text.replace("smul_pull_left (q - q⁻¹) (a0 * (a3 * b1)) b2", "Algebra.smul_mul_assoc (q - q⁻¹) (a0 * a3 * b1)")

text = text.replace("smul_pull_right (q - q⁻¹) a0 (a3 * b2)", "Algebra.mul_smul_comm (q - q⁻¹) a0")
text = text.replace("smul_pull_left (q - q⁻¹) (a0 * (a3 * b2)) b1", "Algebra.smul_mul_assoc (q - q⁻¹) (a0 * a3 * b2)")

text = text.replace("smul_smul_fwd q^2 (q - q⁻¹) (a0 * a3 * b1 * b2)", "smul_smul (q^2) (q - q⁻¹)")
text = text.replace("smul_smul_fwd q^3 (q - q⁻¹) (a0 * a3 * b2 * b1)", "smul_smul (q^3) (q - q⁻¹)")

text = text.replace("rw [smul_smul_fwd, h3, smul_smul_fwd, h3, smul_smul_fwd, h4]", "rw [smul_smul (q^2) q, h3, smul_smul (q^2) q, h3, smul_smul (q^2) (q^2), h4]")

text = text.replace("smul_pull_right q⁻¹ a1 (b2 * b3)", "Algebra.mul_smul_comm q⁻¹ a1")
text = text.replace("smul_pull_right q⁻¹ a0 (a1 * (b2 * b3))", "Algebra.mul_smul_comm q⁻¹ a0")

text = text.replace("smul_pull_right q⁻¹ a2 (b1 * b3)", "Algebra.mul_smul_comm q⁻¹ a2")
text = text.replace("smul_pull_right q⁻¹ a0 (a2 * (b1 * b3))", "Algebra.mul_smul_comm q⁻¹ a0")

text = text.replace("smul_pull_right q⁻¹ a3 (b1 * b2)", "Algebra.mul_smul_comm q⁻¹ a3")
text = text.replace("smul_pull_right q⁻¹ a0 (a3 * (b1 * b2))", "Algebra.mul_smul_comm q⁻¹ a0")

text = text.replace("smul_pull_left q⁻¹ (a1 * a3) (b0 * b2)", "Algebra.smul_mul_assoc q⁻¹ (a1 * a3)")
text = text.replace("smul_pull_left q⁻¹ (a2 * a3) (b0 * b1)", "Algebra.smul_mul_assoc q⁻¹ (a2 * a3)")

text = text.replace("rw [smul_smul_fwd, hh1, smul_smul_fwd, hh2, smul_smul_fwd, hh3, smul_smul_fwd, hh2, smul_smul_fwd, hh4]", 
                    "rw [smul_smul (q^2) q⁻¹, hh1, smul_smul (q^3) q⁻¹, hh2, smul_smul (q^4 - q^2) q⁻¹, hh3, smul_smul (q^3) q⁻¹, hh2, smul_smul (q^4) q⁻¹, hh4]")

with open("lean/InfoGeometry/Projective/Sandbox/QuantumPluckerExchange.lean", "w") as f:
    f.write(text)
