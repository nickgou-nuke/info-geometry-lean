import re

filepath = "lean/InfoGeometry/OperatorAlgebra/SusceptibilityHessian.lean"

with open(filepath, "r") as f:
    content = f.read()

# Replace trailing `  /-- Evidence for the .* law. -/\n\nnamespace` with `\nnamespace`
content = re.sub(r'^[ \t]*/-- Evidence for the [^\n]* -/\n+(namespace|/--|@[a-zA-Z])', r'\n\1', content, flags=re.MULTILINE)

with open(filepath, "w") as f:
    f.write(content)
