with open("proofs/SplitOctonionZorn.lean", "r") as f:
    text = f.read()

text = text.replace("structure Zorn where", "@[ext]\nstructure Zorn where")
text = text.replace("  · rfl", "  · simp [zornNorm, dotProd, Z_null]")

with open("proofs/SplitOctonionZorn.lean", "w") as f:
    f.write(text)
