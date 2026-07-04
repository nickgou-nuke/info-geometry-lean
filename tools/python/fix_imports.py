import re

with open("lean/InfoGeometry/Causal/CelestialMobiusProjection.lean", "r") as f:
    content = f.read()

content = content.replace("import Mathlib.LinearAlgebra.Basic\nimport Mathlib.LinearAlgebra.FiniteDimensional\n", "")

with open("lean/InfoGeometry/Causal/CelestialMobiusProjection.lean", "w") as f:
    f.write(content)
