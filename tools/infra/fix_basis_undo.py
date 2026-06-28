import re

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "r") as f:
    text = f.read()

text = text.replace(
    "simp only [bracket, Pi.single, Function.update, structConst] <;> simp only [sum_B_eval] <;> norm_num",
    "simp [bracket, Pi.single, Function.update, structConst]"
)

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.write(text)

print("Done")
