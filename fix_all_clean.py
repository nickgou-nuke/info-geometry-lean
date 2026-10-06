import re

with open("lean/DAG/MatrixGaussJordan.lean", "r") as f:
    text = f.read()

# Add linter options
options = """set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

"""
if "set_option linter.unusedVariables false" not in text:
    # insert after imports
    text = text.replace("import Mathlib.LinearAlgebra.Matrix.ToLin\n", "import Mathlib.LinearAlgebra.Matrix.ToLin\n\n" + options)

with open("lean/DAG/MatrixGaussJordan.lean", "w") as f:
    f.write(text)
