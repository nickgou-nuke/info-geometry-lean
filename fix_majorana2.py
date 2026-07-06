import re
with open('lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket.lean', 'r') as f:
    text = f.read()

# If there's a doc comment directly before namespace, and it's inside the structure, it might be dangling
text = re.sub(r'^\s*/--[^\n]*-\/\n\nnamespace', '\nnamespace', text, flags=re.MULTILINE)
text = re.sub(r'^\s*/--[^\n]*\n\nnamespace', '\nnamespace', text, flags=re.MULTILINE)

with open('lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket.lean', 'w') as f:
    f.write(text)
