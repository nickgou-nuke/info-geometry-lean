with open("lean/InfoGeometry/GrandUnification/KleinParabolicPeirceTwist.lean", "r") as f:
    content = f.read()

content = content.replace("    try rw [mat_mul_expand]\n    try rw [mat_mul_expand]", "    repeat rw [mat_mul_expand]")

with open("lean/InfoGeometry/GrandUnification/KleinParabolicPeirceTwist.lean", "w") as f:
    f.write(content)
