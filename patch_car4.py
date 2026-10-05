import re

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'r') as f:
    content = f.read()

content = content.replace('; norm_num', '; try norm_num')

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'w') as f:
    f.write(content)
