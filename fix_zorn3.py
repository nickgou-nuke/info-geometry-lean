with open("proofs/SplitOctonionZorn.lean", "r") as f:
    text = f.read()

text = text.replace("  · ext1 i; fin_cases i <;> ring", "  · ext1 i; fin_cases i <;> rfl")
text = text.replace("  · ext i; fin_cases i <;> ring", "  · ext i; fin_cases i <;> rfl")
with open("proofs/SplitOctonionZorn.lean", "w") as f:
    f.write(text)
