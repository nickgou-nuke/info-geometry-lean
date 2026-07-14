import re

with open('/home/goutev/repos/info-geometry-lean/recovery/pre-hermes-snapshot/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket.lean', 'r') as f:
    text = f.read()

# 1. Replace Type* with Type
text = text.replace('Type*', 'Type')

# 2. Replace the _True / _sorryProof pattern in structures.
# Pattern:
#   name_True : Prop := by
#     sorry
#   name_sorryProof :
#     name_True
# Replacement:
#   name_Prop : Prop
#   name_law : name_Prop
pattern1 = re.compile(r'([a-zA-Z0-9_]+)_True\s*:\s*Prop\s*:=\s*by\s*\n\s*sorry\s*\n\s*\1_sorryProof\s*:\s*\1_True', re.MULTILINE)
text = pattern1.sub(r'\1_Prop : Prop\n  \1_law : \1_Prop', text)

# 3. There are some where the type is not just Prop, e.g. normalizable_iff_criticalLine_True
# Pattern:
#   name_True :
#     expr
#   name_sorryProof :
#     name_True
# Actually, let's just replace `_True` with `_Prop` and `_sorryProof` with `_law` everywhere!
text = text.replace('_True', '_Prop')
text = text.replace('_sorryProof', '_law')

# Wait, the structure fields for complex ones:
#   normalizable_iff_criticalLine_Prop :
#     normalizable_Prop ↔ IsCriticalLineRealPart realPart
#   normalizable_iff_criticalLine_law :
#     normalizable_Prop ↔ IsCriticalLineRealPart realPart
# We want to remove the first one, and just keep the `_law`.
# Let's fix this up.

with open('/home/goutev/repos/info-geometry-lean/sandbox/refactored.lean', 'w') as f:
    f.write(text)

