import re

with open("lean/InfoGeometry/Categorical/MobiusGeometry.lean", "r") as f:
    content = f.read()

content = content.replace(
    "intro h\n      have hz1 : M.a * p.z1 + M.b * p.z2 = 0 := h.1\n      have hz2 : M.c * p.z1 + M.d * p.z2 = 0 := h.2",
    "by_contra h\n      push_neg at h\n      have hz1 : M.a * p.z1 + M.b * p.z2 = 0 := h.1\n      have hz2 : M.c * p.z1 + M.d * p.z2 = 0 := h.2"
)

with open("lean/InfoGeometry/Categorical/MobiusGeometry.lean", "w") as f:
    f.write(content)
