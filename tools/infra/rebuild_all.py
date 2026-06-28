import re

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean.bak", "r") as f:
    lines = f.readlines()

# find jacobi_even_basis
for i, line in enumerate(lines):
    if line.startswith("private theorem jacobi_even_basis"):
        start_basis_idx = i
        break

for i in range(start_basis_idx, len(lines)):
    if line.startswith("instance : SuperLieRing OSp12 where"):
        pass

# Wait, `split_instance.py` logic is great. Let's just run it first.
