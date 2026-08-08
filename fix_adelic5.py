with open("proofs/AdelicSymmetrySpectrum.lean", "r") as f:
    text = f.read()

text = text.replace("simp [inner_self_conj v]", "simp")
text = text.replace("by { apply Complex.ext <;> (simp; ring) }", "by { apply Complex.ext <;> simp }")
with open("proofs/AdelicSymmetrySpectrum.lean", "w") as f:
    f.write(text)
