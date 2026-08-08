with open("proofs/AdelicSymmetrySpectrum.lean", "r") as f:
    text = f.read()

text = text.replace("by { apply Complex.ext; { simp; ring }; { simp; ring } }", "by { apply Complex.ext; { simp; ring }; { simp } }")
with open("proofs/AdelicSymmetrySpectrum.lean", "w") as f:
    f.write(text)
