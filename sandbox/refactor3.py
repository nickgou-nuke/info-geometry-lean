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

# Now fix redundancies using a simpler regex.
# Let's match line by line.
lines = text.split('\n')
new_lines = []
i = 0
while i < len(lines):
    line = lines[i]
    # Check if this line looks like `  name_Prop :`
    m = re.match(r'^(\s*)([a-zA-Z0-9_]+)_Prop\s*:\s*(.*)$', line)
    if m:
        indent = m.group(1)
        name = m.group(2)
        prop_type = m.group(3)
        # Collect lines for the type
        prop_type_lines = [prop_type]
        j = i + 1
        while j < len(lines) and (lines[j].startswith(indent + '  ') or lines[j].strip() == ''):
            if lines[j].strip() != '':
                prop_type_lines.append(lines[j])
            j += 1
        
        # Now see if the next field is `name_law : ` with the exact same type
        if j < len(lines):
            m2 = re.match(r'^(\s*)' + name + r'_law\s*:\s*(.*)$', lines[j])
            if m2 and m2.group(1) == indent:
                law_type = m2.group(2)
                law_type_lines = [law_type]
                k = j + 1
                while k < len(lines) and (lines[k].startswith(indent + '  ') or lines[k].strip() == ''):
                    if lines[k].strip() != '':
                        law_type_lines.append(lines[k])
                    k += 1
                
                # Check if types match
                if prop_type_lines == law_type_lines:
                    # They match! Skip the `_Prop` declaration entirely.
                    # Just add the `_law` declaration.
                    new_lines.append(indent + name + '_law : ' + law_type)
                    for k_line in lines[j+1:k]:
                        new_lines.append(k_line)
                    i = k
                    continue

    new_lines.append(line)
    i += 1

with open('/home/goutev/repos/info-geometry-lean/sandbox/MajoranaPolyaHilbertSocket.lean', 'w') as f:
    f.write('\n'.join(new_lines))
