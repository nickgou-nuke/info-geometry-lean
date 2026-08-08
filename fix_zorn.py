with open("proofs/SplitOctonionZorn.lean", "r") as f:
    text = f.read()

text = text.replace("import Mathlib.Data.Real.Basic", "import Mathlib.Data.Real.Basic\nimport Mathlib.Tactic")

text = text.replace("""  · dsimp [zornNorm, dotProd]
    norm_num""", """  · rfl""")

with open("proofs/SplitOctonionZorn.lean", "w") as f:
    f.write(text)
