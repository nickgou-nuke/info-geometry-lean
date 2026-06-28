import re

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "r") as f:
    text = f.read()

# Replace the simple `simp` with `simp [...]; ring_nf` or `norm_num`
old_simp = "simp [bracket, Pi.single, Function.update, structConst]"
new_simp = "simp [bracket, Pi.single, Function.update, structConst]; norm_num"

text = text.replace(old_simp, new_simp)

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.write(text)

print("Done")
