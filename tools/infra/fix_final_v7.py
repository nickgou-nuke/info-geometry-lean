with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "r") as f:
    text = f.read()

text = text.replace("simp [this, Finset.sum_insert, Finset.sum_singleton]", "simp [this, Finset.sum_insert, Finset.sum_singleton]; abel")

text = text.replace("simp [ih_u, ih_v]", "simp [ih_u, ih_v, Pi.add_apply]")
text = text.replace("simp [ih_u]", "simp [ih_u, Pi.smul_apply]")

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.write(text)

print("Done")
