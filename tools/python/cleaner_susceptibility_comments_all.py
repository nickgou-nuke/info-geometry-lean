import re

filepath = "lean/InfoGeometry/OperatorAlgebra/SusceptibilityHessian.lean"

with open(filepath, "r") as f:
    content = f.read()

# Delete lines that are just `  /-- Evidence for ... -/` optionally followed by blank lines
content = re.sub(r'^[ \t]*/-- Evidence for [^\n]* -/\n+', '', content, flags=re.MULTILINE)

with open(filepath, "w") as f:
    f.write(content)
