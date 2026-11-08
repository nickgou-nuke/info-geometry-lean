with open("lean/InfoGeometry/Canonical/Cl11BipartiteDiracBridge.lean", "r") as f:
    content = f.read()

old_proof = """  rw [compositeDirac]
  rw [map_add, tensorSwap_kronecker, tensorSwap_kronecker]
  simp"""

new_proof = """  change tensorSwap ((DL ⊗ₖ betaR : StageTwo) + ((1 : StageOne) ⊗ₖ DR : StageTwo)) = _
  rw [map_add, tensorSwap_kronecker, tensorSwap_kronecker]
  simp"""

content = content.replace(old_proof, new_proof)

with open("lean/InfoGeometry/Canonical/Cl11BipartiteDiracBridge.lean", "w") as f:
    f.write(content)

