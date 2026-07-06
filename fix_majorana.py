import re
with open('lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket.lean', 'r') as f:
    text = f.read()

# Remove the fields that end with _law
text = re.sub(r'^\s+\w+_law\s*:\s*.*?\n', '', text, flags=re.MULTILINE)
# Replace exact P.*_law with sorry
text = re.sub(r'exact P\.\w+_law', 'sorry', text)
# Replace exact P.*_guard with sorry
text = re.sub(r'exact P\.\w+_guard', 'sorry', text)
text = re.sub(r'exact \w+_law', 'sorry', text)

with open('lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket.lean', 'w') as f:
    f.write(text)
