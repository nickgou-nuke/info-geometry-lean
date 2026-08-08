with open("proofs/AdelicSymmetrySpectrum.lean", "r") as f:
    text = f.read()

text = text.replace("∀ u v,", "∀ (u v : V),")
text = text.replace("conj lambda", "star lambda")
text = text.replace("Complex.add_conj lambda", "by { apply Complex.ext <;> simp }")
text = text.replace("inv_mul_cancel h12", "inv_mul_cancel₀ h12")

with open("proofs/AdelicSymmetrySpectrum.lean", "w") as f:
    f.write(text)
