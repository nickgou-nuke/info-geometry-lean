import re

with open('lean/InfoGeometry/Probability/HomologicalProbability.lean', 'r') as f:
    content = f.read()

# Replace def X (args) : Prop := ... with theorem X (args) : ... := by sorry
def prop_replacer(match):
    prefix = match.group(1) # e.g. def X
    name = match.group(2)
    args = match.group(3)
    body = match.group(4)
    # The body could be multiple lines. Let's just output `theorem X args : body := by sorry`
    # if it's a def... wait, we need to handle the body correctly.
    # It's better to just write a smart regex.
    pass

