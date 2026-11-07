import re

with open('lean/InfoGeometry/Canonical/SplitOctonionJordanStructure.lean', 'r') as f:
    content = f.read()

content = content.replace('Ring.lieRing', 'LieRing.ofAssociativeRing')

with open('lean/InfoGeometry/Canonical/SplitOctonionJordanStructure.lean', 'w') as f:
    f.write(content)

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'r') as f:
    content = f.read()

content = content.replace('fin_cases i <;> fin_cases j <;> norm_num', 'fin_cases i <;> fin_cases j <;> simp <;> ring')

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'w') as f:
    f.write(content)

