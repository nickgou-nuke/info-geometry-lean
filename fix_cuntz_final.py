import re

with open('lean/InfoGeometry/Topology/AlgebraicCuntzQuotient.lean', 'r') as f:
    content = f.read()

# Add import Mathlib.Algebra.RingQuot if missing
if 'import Mathlib.Algebra.RingQuot' not in content:
    content = content.replace('import Mathlib.LinearAlgebra.TensorAlgebra.Basic', 'import Mathlib.LinearAlgebra.TensorAlgebra.Basic\nimport Mathlib.Algebra.RingQuot')

# Remove (R := R) globally
content = content.replace('(R := R)', '')
content = content.replace('(A := (CuntzAlg R ι)ᵐᵒᵖ)', '')

with open('lean/InfoGeometry/Topology/AlgebraicCuntzQuotient.lean', 'w') as f:
    f.write(content)
