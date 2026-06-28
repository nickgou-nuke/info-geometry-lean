import re

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "r") as f:
    text = f.read()

lemma_str = """
private lemma sum_B_eval {α : Type*} [AddCommMonoid α] (f : B → α) :
    ∑ x : B, f x = f B.H + f B.Ep + f B.Em + f B.G1 + f B.G2 := by
  simp [Finset.sum_univ, Finset.univ, Finset.sum_insert, Finset.sum_singleton]
  abel

"""

# Insert right after `open B`
text = text.replace("open B\n", "open B\n" + lemma_str)

# Replace basis_simp in python with the sum_B_eval applied
basis_simp_str = "simp [Finset.sum_univ, Finset.univ, Finset.sum_insert, Finset.sum_singleton, bracket, Pi.single, Function.update, structConst]; abel"

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.write(text)

print("Done")
