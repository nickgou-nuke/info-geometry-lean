import re

with open('lean/InfoGeometry/Arithmetic/PrimeBitMellinLaplaceBridge.lean', 'r') as f:
    text = f.read()

target = """  rw [hlog]
  ring"""

replacement = """  rw [hlog]
  congr 1
  ring"""

text = text.replace(target, replacement)

with open('lean/InfoGeometry/Arithmetic/PrimeBitMellinLaplaceBridge.lean', 'w') as f:
    f.write(text)

