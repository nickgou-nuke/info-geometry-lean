import re

with open('lean/InfoGeometry/Topology/AlgebraicCuntzQuotient.lean', 'r') as f:
    content = f.read()

content = content.replace('T (R := R) i', '(T i : CuntzAlg R ι)')
content = content.replace('S (R := R) i', '(S i : CuntzAlg R ι)')
content = content.replace('T (R := R) j', '(T j : CuntzAlg R ι)')
content = content.replace('S (R := R) j', '(S j : CuntzAlg R ι)')
content = content.replace('lift_S (R := R)', 'lift_S')
content = content.replace('lift_T (R := R)', 'lift_T')

with open('lean/InfoGeometry/Topology/AlgebraicCuntzQuotient.lean', 'w') as f:
    f.write(content)
