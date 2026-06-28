with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "r") as f:
    text = f.read()

# Replace {{ and }} with { and }
text = text.replace("{{", "{")
text = text.replace("}}", "}")

# Replace the bad simp string
text = text.replace("simp [Finset.sum_univ, Finset.univ, Finset.sum_insert, Finset.sum_singleton, bracket, Pi.single, Function.update, structConst]; abel",
                    "simp [bracket, Pi.single, Function.update, structConst] <;> simp [sum_B_eval] <;> norm_num")

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.write(text)

print("Done")
