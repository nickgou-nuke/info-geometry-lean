import re

with open("lean/InfoGeometry/Canonical/Cl11BipartiteDiracBridge.lean", "r") as f:
    text = f.read()

# Replace Matrix.reindexAlgEquiv_apply with Matrix.coe_reindexAlgEquiv
text = text.replace("Matrix.reindexAlgEquiv_apply", "Matrix.coe_reindexAlgEquiv")

# Also add the type casting map_add fix from before
old_proof = """  rw [compositeDirac]
  rw [map_add, tensorSwap_kronecker, tensorSwap_kronecker]
  simp"""

new_proof = """  change tensorSwap ((DL ⊗ₖ betaR : StageTwo) + ((1 : StageOne) ⊗ₖ DR : StageTwo)) = _
  rw [map_add, tensorSwap_kronecker, tensorSwap_kronecker]
  simp"""

text = text.replace(old_proof, new_proof)

with open("lean/InfoGeometry/Canonical/Cl11BipartiteDiracBridge.lean", "w") as f:
    f.write(text)

