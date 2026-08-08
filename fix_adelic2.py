import re
with open("proofs/AdelicSymmetrySpectrum.lean", "r") as f:
    text = f.read()

text = re.sub(r'\binner\b(?![_])', 'inner ℂ', text)

with open("proofs/AdelicSymmetrySpectrum.lean", "w") as f:
    f.write(text)
