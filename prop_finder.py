import re

content = open('lean/InfoGeometry/Probability/HomologicalProbability.lean').read()

# Match def ... : Prop :=
matches = re.findall(r'^def\s+([A-Za-z0-9_]+)[\s\S]*?:\s*Prop\s*:=', content, re.MULTILINE)
print("Defs returning Prop:", matches)

matches_struct = re.findall(r'^structure\s+([A-Za-z0-9_]+)[\s\S]*?:\s*Prop\s*where', content, re.MULTILINE)
print("Structures returning Prop:", matches_struct)

