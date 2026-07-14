import re

with open('/home/goutev/repos/info-geometry-lean/sandbox/MajoranaPolyaHilbertSocket.lean', 'r') as f:
    text = f.read()

# For every structure definition, we want to ensure that if there is a `name_Prop : Prop` field,
# it is immediately followed by `name_law : name_Prop`.
# And for every `mkDummy` function, we want to ensure it has `name_Prop := False` and `name_law := sorry`.

lines = text.split('\n')
new_lines = []

in_mkDummy = False
in_struct = False
current_struct_props = []

for line in lines:
    m_struct = re.match(r'^structure\s+([a-zA-Z0-9_]+)', line)
    if m_struct:
        in_struct = True
        current_struct_props = []
    elif line.startswith('end '):
        in_struct = False
        in_mkDummy = False

    m_prop = re.match(r'^(\s*)([a-zA-Z0-9_]+)_Prop\s*:\s*Prop$', line)
    if m_prop and in_struct:
        indent = m_prop.group(1)
        name = m_prop.group(2)
        new_lines.append(line)
        # Check if next line is the law
        # Wait, we can't easily peek without looking ahead, but we can just append it
        # and if the next line is already the law, it will be skipped?
        # Actually it's easier to just ALWAYS append the law if it matches exactly `name_Prop : Prop`
        new_lines.append(indent + name + '_law : ' + name + '_Prop')
        current_struct_props.append(name)
        continue
    
    # If the line is an existing `_law : _Prop`, skip it if we just added it
    m_law = re.match(r'^(\s*)([a-zA-Z0-9_]+)_law\s*:\s*\2_Prop$', line)
    if m_law and in_struct:
        # We already added it in the previous step
        continue

    # Now for mkDummy
    m_mk = re.match(r'^(\s*)def mkDummy', line)
    if m_mk:
        in_mkDummy = True
    
    m_prop_assign = re.match(r'^(\s*)([a-zA-Z0-9_]+)_Prop\s*:=.*$', line)
    if m_prop_assign and in_mkDummy:
        indent = m_prop_assign.group(1)
        name = m_prop_assign.group(2)
        new_lines.append(line)
        new_lines.append(indent + name + '_law := sorry')
        continue
    
    m_law_assign = re.match(r'^(\s*)([a-zA-Z0-9_]+)_law\s*:=.*$', line)
    if m_law_assign and in_mkDummy:
        # Check if we already added it
        continue
        
    new_lines.append(line)

with open('/home/goutev/repos/info-geometry-lean/sandbox/MajoranaPolyaHilbertSocket.lean', 'w') as f:
    f.write('\n'.join(new_lines))
