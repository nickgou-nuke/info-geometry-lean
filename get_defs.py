import re
content = open('lean/InfoGeometry/Probability/HomologicalProbability.lean').read()
matches = re.findall(r'^def\s+([A-Za-z0-9_]+)[\s\S]*?:\s*Prop\s*:=', content, re.MULTILINE)
for m in matches:
    print(m)
