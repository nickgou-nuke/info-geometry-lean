with open("proofs/AdelicSymmetrySpectrum.lean", "r") as f:
    text = f.read()

text = text.replace("by { apply Complex.ext <;> simp }", "by { apply Complex.ext; { simp; ring }; { simp; ring } }")
with open("proofs/AdelicSymmetrySpectrum.lean", "w") as f:
    f.write(text)
