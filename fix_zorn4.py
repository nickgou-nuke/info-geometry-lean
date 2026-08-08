with open("proofs/SplitOctonionZorn.lean", "r") as f:
    text = f.read()

text = text.replace("  · ext1 i; fin_cases i <;> rfl", "  · ext1 i; fin_cases i <;> (simp; ring)")
text = text.replace("  · ext i; fin_cases i <;> rfl", "  · ext i; fin_cases i <;> (simp; ring)")
with open("proofs/SplitOctonionZorn.lean", "w") as f:
    f.write(text)
