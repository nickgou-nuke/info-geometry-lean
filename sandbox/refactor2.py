import re

with open('/home/goutev/repos/info-geometry-lean/recovery/pre-hermes-snapshot/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket.lean', 'r') as f:
    text = f.read()

text = text.replace('Type*', 'Type')

# Replace:
#   name_True : Prop := by
#     sorry
#   name_sorryProof :
#     name_True
# With:
#   name_Prop : Prop
#   name_law : name_Prop
pattern_simple = re.compile(
    r'([a-zA-Z0-9_]+)_True\s*:\s*Prop\s*:=\s*by\s*\n\s*sorry\s*\n\s*\1_sorryProof\s*:\s*\1_True',
    re.MULTILINE
)
text = pattern_simple.sub(r'\1_Prop : Prop\n  \1_law : \1_Prop', text)

text = text.replace('_True', '_Prop')
text = text.replace('_sorryProof', '_law')

# Fix redundancies like:
#   normalizable_iff_criticalLine_Prop :
#     normalizable_Prop ↔ IsCriticalLineRealPart realPart
#   normalizable_iff_criticalLine_law :
#     normalizable_Prop ↔ IsCriticalLineRealPart realPart
pattern_redundant = re.compile(
    r'([a-zA-Z0-9_]+)_Prop\s*:\s*([^\n]+(?:\n[ \t]+[^\n]+)*)\s*\n\s*\1_law\s*:\s*\2',
    re.MULTILINE
)
text = pattern_redundant.sub(r'\1_law : \2', text)

with open('/home/goutev/repos/info-geometry-lean/sandbox/MajoranaPolyaHilbertSocket.lean', 'w') as f:
    f.write(text)
