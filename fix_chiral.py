with open('lean/DAG/ChiralDiracAnticommutation.lean', 'r') as f:
    content = f.read()

import re

content = content.replace('Fintype.sum_ite_eq, ', '')

with open('lean/DAG/ChiralDiracAnticommutation.lean', 'w') as f:
    f.write(content)
