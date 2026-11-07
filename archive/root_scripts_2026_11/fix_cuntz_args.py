import re

with open('lean/InfoGeometry/Topology/AlgebraicCuntzQuotient.lean', 'r') as f:
    content = f.read()

content = content.replace('T (R := R)', 'T')
content = content.replace('S (R := R)', 'S')

with open('lean/InfoGeometry/Topology/AlgebraicCuntzQuotient.lean', 'w') as f:
    f.write(content)
