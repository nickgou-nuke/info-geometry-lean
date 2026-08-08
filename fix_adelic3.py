with open("proofs/AdelicSymmetrySpectrum.lean", "r") as f:
    text = f.read()

text = text.replace("    rw [h_adj]", "    exact (h_adj v v).symm")
text = text.replace("    rw [h_adj', h_eigen, inner_smul_left, RingHom.id_apply]", "    rw [h_adj', h_eigen, inner_smul_left]\n    rfl")
text = text.replace("  have h8 : lambda + star lambda = (2 * lambda.re : ℂ) := Complex.add_star lambda", "  have h8 : lambda + star lambda = (2 * lambda.re : ℂ) := by { apply Complex.ext <;> simp; ring; simp; ring }")
text = text.replace("  have h10 : ((2 : ℂ) * lambda.re).re = (1 : ℂ).re := by rw [h9]\n  have h11 : 2 * lambda.re = 1 := by exact h10", "  have h11 : 2 * lambda.re = 1 := by { have h10 := congr_arg Complex.re h9; simpa using h10 }")
with open("proofs/AdelicSymmetrySpectrum.lean", "w") as f:
    f.write(text)
