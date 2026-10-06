import re

with open("lean/DAG/MatrixGaussJordan.lean", "r") as f:
    text = f.read()

options = """
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
"""

if "set_option linter.unusedVariables false" not in text:
    text = text.replace("open Matrix\n", "open Matrix\n" + options)

with open("lean/DAG/MatrixGaussJordan.lean", "w") as f:
    f.write(text)
