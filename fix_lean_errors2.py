with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "r") as f:
    content = f.read()

content = content.replace("rw [div_div_eq_div_mul]", "rw [div_div]")

with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "w") as f:
    f.write(content)
