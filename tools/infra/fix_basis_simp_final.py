import re

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "r") as f:
    text = f.read()

# Replace the broken rfl basis proofs with the original simp!
text = text.replace(
    "cases b <;> cases c <;> ext k <;> fin_cases k <;> rfl",
    "cases b <;> cases c <;> ext k <;> fin_cases k <;> simp [bracket, Pi.single, Function.update, structConst]"
)

text = text.replace(
    "rcases hb with rfl | rfl <;> cases c <;> ext k <;> fin_cases k <;> rfl",
    "rcases hb with rfl | rfl <;> cases c <;> ext k <;> fin_cases k <;> simp [bracket, Pi.single, Function.update, structConst]"
)

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.write(text)

print("Done")
