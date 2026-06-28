import re

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "r") as f:
    text = f.read()

# For even:
text = text.replace(
    "cases b <;> cases c <;> ext k <;> fin_cases k <;>\n    simp [Finset.sum_univ, Finset.univ, Finset.sum_insert, Finset.sum_singleton, bracket, Pi.single, Function.update, structConst]; abel",
    "ext k; revert k b c; decide"
)

# For odd:
text = text.replace(
    "rcases hb with rfl | rfl <;> cases c <;> ext k <;> fin_cases k <;>\n    simp [Finset.sum_univ, Finset.univ, Finset.sum_insert, Finset.sum_singleton, bracket, Pi.single, Function.update, structConst]; abel",
    "ext k; revert k hb c b; decide"
)

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.write(text)

print("Done")
