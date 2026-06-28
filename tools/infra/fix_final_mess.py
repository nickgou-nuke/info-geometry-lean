import re

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "r") as f:
    text = f.read()

# 1. Add maxHeartbeats at the top
if "set_option maxHeartbeats" not in text:
    text = text.replace("open B", "set_option maxHeartbeats 8000000\nopen B")

# 2. Fix SuperBracket.lie_zero_right -> SuperBracket.zero_lie
text = text.replace("SuperBracket.lie_zero_right", "SuperBracket.zero_lie")

# 3. Replace brittle calc blocks in skew/symm proofs with simp
text = re.sub(
    r"  \| add a b ha hb haP hbP =>\n\s*calc.*?(?=  \| smul)",
    "  | add a b ha hb haP hbP =>\n      simp only [add_lie_proof, lie_add_proof, haP, hbP]; abel\n",
    text,
    flags=re.DOTALL
)

text = re.sub(
    r"  \| smul r a ha haP =>\n\s*calc.*?(?=\n\n)",
    "  | smul r a ha haP =>\n      simp only [smul_lie_proof, lie_smul_proof, haP]; simp [smul_add, smul_sub]",
    text,
    flags=re.DOTALL
)

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.write(text)

print("Done")
