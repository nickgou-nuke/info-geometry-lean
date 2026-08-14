import re

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'r') as f:
    text = f.read()

text = text.replace("exact axialFlowCoordinate_eq_hyperbolicFlowCoordinate t x", "exact congrFun (axialFlowCoordinate_eq_hyperbolicFlowCoordinate t) x")

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'w') as f:
    f.write(text)

