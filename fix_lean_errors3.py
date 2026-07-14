with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "r") as f:
    content = f.read()

content = content.replace("""  have eq1 : ((b * c - a * d) / c ^ 2) * (1 / (z + d / c)) = (b * c - a * d) / (c ^ 2 * (z + d / c)) := by
    rw [div_div]""", """  have eq1 : ((b * c - a * d) / c ^ 2) * (1 / (z + d / c)) = (b * c - a * d) / (c ^ 2 * (z + d / c)) := by
    ring""")

with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "w") as f:
    f.write(content)
