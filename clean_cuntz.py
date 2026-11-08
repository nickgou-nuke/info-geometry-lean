import re

with open('lean/InfoGeometry/Topology/AlgebraicCuntzQuotient.lean', 'r') as f:
    content = f.read()

content = content.replace('(R := R)', '')
content = content.replace('(A := (CuntzAlg R ι)ᵐᵒᵖ)', '')

with open('lean/InfoGeometry/Topology/AlgebraicCuntzQuotient.lean', 'w') as f:
    f.write(content)
