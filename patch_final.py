import re

# Fix LieRing in SplitOctonionJordanStructure
with open('lean/InfoGeometry/Canonical/SplitOctonionJordanStructure.lean', 'r') as f:
    content = f.read()
if 'import Mathlib.Algebra.Lie.OfAssociative' not in content:
    content = content.replace('import Mathlib.Algebra.Jordan.Basic', 'import Mathlib.Algebra.Jordan.Basic\nimport Mathlib.Algebra.Lie.OfAssociative\nimport Mathlib.Algebra.Lie.Matrix')
    with open('lean/InfoGeometry/Canonical/SplitOctonionJordanStructure.lean', 'w') as f:
        f.write(content)

# Fix ThreeModeCARHodgeLaplacianBridge
with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'r') as f:
    content = f.read()

# Replace `rfl` with `norm_num` if it's preceded by `fin_cases` and it's failing. 
# But wait, the error is `unsolved goals case «0».«0»`. This means `fin_cases` left a goal!
# It's probably `rfl` failing to reduce addition of matrices or something.
# We can replace `rfl` with `norm_num` for these matrix things.
content = content.replace('fin_cases i <;> fin_cases j <;> rfl', 'fin_cases i <;> fin_cases j <;> norm_num')
content = content.replace('fin_cases i <;> fin_cases j <;> decide', 'fin_cases i <;> fin_cases j <;> norm_num')

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'w') as f:
    f.write(content)

