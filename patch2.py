import re

with open("lean/InfoGeometry/Canonical/IntegralZornAlternativeAlgebra.lean", "r") as f:
    text = f.read()

text = text.replace("ZornAuto.", "")

with open("lean/InfoGeometry/Canonical/IntegralZornAlternativeAlgebra.lean", "w") as f:
    f.write(text)
