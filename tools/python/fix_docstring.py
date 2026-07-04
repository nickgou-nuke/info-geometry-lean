import re

with open("lean/InfoGeometry/Causal/CelestialMobiusProjection.lean", "r") as f:
    content = f.read()

content = content.replace("/--\nThe mapping", "/-\nThe mapping")
content = content.replace("/--\nA structural boundary projector", "/-\nA structural boundary projector")

with open("lean/InfoGeometry/Causal/CelestialMobiusProjection.lean", "w") as f:
    f.write(content)
