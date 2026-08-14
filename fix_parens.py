import re

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'r') as f:
    text = f.read()

text = text.replace("(kill 4 1 (by simpa [ha']) (by simp)))", "(kill 4 1 (by simpa [ha']) (by simp))))")

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'w') as f:
    f.write(text)

