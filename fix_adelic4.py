with open("proofs/AdelicSymmetrySpectrum.lean", "r") as f:
    text = f.read()

text = text.replace("    rw [← inner_conj_symm, ← h_adj, h_eigen, inner_smul_right, star_mul']\n    congr 1\n    exact inner_self_conj v", "    rw [← inner_conj_symm, ← h_adj, h_eigen, inner_smul_right]; simp [inner_self_conj v]")
text = text.replace("  have h8 : lambda + star lambda = (2 * lambda.re : ℂ) := by { apply Complex.ext <;> simp; ring; simp; ring }", "  have h8 : lambda + star lambda = (2 * lambda.re : ℂ) := by { apply Complex.ext <;> (simp; ring) }")
with open("proofs/AdelicSymmetrySpectrum.lean", "w") as f:
    f.write(text)
