import re

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "r") as f:
    text = f.read()

# Replace all calc blocks for `add` with the simp one-liner
text = re.sub(
    r"  \| add u v hu hv huP hvP =>\n\s*calc\n.*?(?=  \| smul r u hu huP =>)",
    "  | add u v hu hv huP hvP =>\n      simp only [add_lie_proof, lie_add_proof, huP, hvP]; abel\n",
    text,
    flags=re.DOTALL
)

# Replace all calc blocks for `smul` with the simp one-liner
text = re.sub(
    r"  \| smul r u hu huP =>\n\s*calc\n.*?(?=\n\n)",
    "  | smul r u hu huP =>\n      simp only [smul_lie_proof, lie_smul_proof, huP]; simp [smul_add, smul_sub]",
    text,
    flags=re.DOTALL
)

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.write(text)

print("Done")
