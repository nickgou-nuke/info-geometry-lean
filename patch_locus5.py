import re

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'r') as f:
    text = f.read()

text = text.replace('fun y _ =>', 'fun y =>')

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'w') as f:
    f.write(text)
