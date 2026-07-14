with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "r") as f:
    content = f.read()

# Fix noncomputable for lines 89-92
content = content.replace("def trans_f1", "noncomputable def trans_f1")
content = content.replace("def inv_f2", "noncomputable def inv_f2")
content = content.replace("def dil_f3", "noncomputable def dil_f3")
content = content.replace("def trans_f4", "noncomputable def trans_f4")

# Fix λ to lam
content = content.replace("lemma eigenvalue_mapping (a b c d λ γ : ℂ)", "lemma eigenvalue_mapping (a b c d lam γ : ℂ)")
content = content.replace("(h_eigen : λ = c * γ + d) :", "(h_eigen : lam = c * γ + d) :")
content = content.replace("    λ^2 - (a + d) * λ + (a * d - b * c) = 0 := by", "    lam^2 - (a + d) * lam + (a * d - b * c) = 0 := by")
content = content.replace("  calc λ^2 - (a + d) * λ + (a * d - b * c)", "  calc lam^2 - (a + d) * lam + (a * d - b * c)")

# Fix line 324 div_div_eq_div_mul
content = content.replace("rw [div_mul_div_comm, mul_one]", "rw [div_div_eq_div_mul]")

with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "w") as f:
    f.write(content)
