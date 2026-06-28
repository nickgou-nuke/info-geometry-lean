import re

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "r") as f:
    text = f.read()

# Fix even y add
text = text.replace(
    "rw [← lie_add_proof x u v, ← add_lie_proof (bracket x u) (bracket x v) z, ← add_lie_proof u v (bracket x z)]",
    "rw [← add_lie_proof (bracket x u) (bracket x v) z, ← lie_add_proof x u v, ← add_lie_proof u v (bracket x z)]"
)

# Fix even y smul
text = text.replace(
    "rw [← lie_smul_proof r x u, ← smul_lie_proof r (bracket x u) z, ← smul_lie_proof r u (bracket x z)]",
    "rw [← smul_lie_proof r (bracket x u) z, ← lie_smul_proof r x u, ← smul_lie_proof r u (bracket x z)]"
)

# Fix even x add
text = text.replace(
    "rw [← add_lie_proof u v y, ← add_lie_proof (bracket u y) (bracket v y) z, ← add_lie_proof u v z, ← lie_add_proof y (bracket u z) (bracket v z)]",
    "rw [← add_lie_proof (bracket u y) (bracket v y) z, ← add_lie_proof u v y, ← lie_add_proof y (bracket u z) (bracket v z), ← add_lie_proof u v z]"
)

# Fix even x smul
text = text.replace(
    "rw [← smul_lie_proof r u y, ← smul_lie_proof r (bracket u y) z, ← smul_lie_proof r u z, ← lie_smul_proof r y (bracket u z)]",
    "rw [← smul_lie_proof r (bracket u y) z, ← smul_lie_proof r u y, ← lie_smul_proof r y (bracket u z), ← smul_lie_proof r u z]"
)

# Fix odd z add
text = text.replace(
    "rw [← lie_add_proof (bracket x y) u v, ← lie_add_proof x u v, ← lie_add_proof y (bracket x u) (bracket x v)]",
    "rw [← lie_add_proof (bracket x y) u v, ← lie_add_proof y (bracket x u) (bracket x v), ← lie_add_proof x u v]"
)

# Fix odd z smul
text = text.replace(
    "rw [← lie_smul_proof r (bracket x y) u, ← lie_smul_proof r x u, ← lie_smul_proof r y (bracket x u)]",
    "rw [← lie_smul_proof r (bracket x y) u, ← lie_smul_proof r y (bracket x u), ← lie_smul_proof r x u]"
)

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.write(text)

print("Done")
