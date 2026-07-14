with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "r") as f:
    content = f.read()

# At line 514, we need `rw [div_mul_div_comm, mul_one]` instead of `ring`
content = content.replace("""  have eq1 : ((b * c - a * d) / c ^ 2) * (1 / (z + d / c)) = (b * c - a * d) / (c ^ 2 * (z + d / c)) := by
    ring""", """  have eq1 : ((b * c - a * d) / c ^ 2) * (1 / (z + d / c)) = (b * c - a * d) / (c ^ 2 * (z + d / c)) := by
    rw [div_mul_div_comm, mul_one]""")

with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "w") as f:
    f.write(content)
