import re

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'r') as f:
    content = f.read()

content = content.replace('ext i j; fin_cases i <;> fin_cases j <;> (', 'ext i j; fin_cases i <;> fin_cases j')
content = content.replace('ext i j; fin_cases i <;> fin_cases j <;> \\(', 'ext i j; fin_cases i <;> fin_cases j')

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'w') as f:
    f.write(content)
