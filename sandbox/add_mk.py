import re

with open('/home/goutev/repos/info-geometry-lean/sandbox/MajoranaPolyaHilbertSocket.lean', 'r') as f:
    text = f.read()

structures = []
# Find all structures
# structure Name (A B C : Type) where
#   field : type
#   ...
pattern_struct = re.compile(r'structure\s+([a-zA-Z0-9_]+)\s*\n?\s*\(([^)]+)\)\s*where\n((?:\s+[^\n]+\n)+)', re.MULTILINE)

for m in pattern_struct.finditer(text):
    name = m.group(1)
    type_args_str = m.group(2)
    fields_str = m.group(3)
    
    # parse type args to get count of types
    # e.g. "A B C : Type" -> 3 Units
    type_args = []
    for part in type_args_str.split(':'):
        part = part.strip()
        if 'Type' not in part and part != '':
            type_args.extend(part.split())
    
    num_types = len(type_args)
    units = ' '.join(['Unit'] * num_types)
    
    # parse fields
    fields = []
    for line in fields_str.split('\n'):
        line = line.strip()
        if line.startswith('--') or line.startswith('/-') or line == '':
            continue
        # handle field : type
        if ':' in line:
            field_name = line.split(':')[0].strip()
            fields.append(field_name)
    
    # generate mkDummy
    mk_dummy = f"  def mkDummy : {name} {units} where\n"
    for f in fields:
        if f.endswith('_Prop') or f == 'classicalRHStatement':
            mk_dummy += f"    {f} := False\n"
        elif f.endswith('_law') or f.endswith('_guard'):
            mk_dummy += f"    {f} := sorry\n"
        else:
            # We don't know the exact type, but we can try to provide sorry
            # Or if it's Unit, we can provide ()
            # Actually just `sorry` for data fields is fine, but it might complain if it's a Prop
            # Let's just use `sorry` for all data fields.
            mk_dummy += f"    {f} := sorry\n"
    
    # insert mkDummy into the corresponding namespace
    namespace_str = f"namespace {name}"
    idx = text.find(namespace_str)
    if idx != -1:
        # find the end of the namespace or just insert after the namespace declaration
        insert_idx = text.find('\n', idx) + 1
        text = text[:insert_idx] + mk_dummy + text[insert_idx:]
    else:
        # if namespace doesn't exist, create it
        # find the end of the structure definition
        end_idx = m.end()
        insertion = f"\nnamespace {name}\n{mk_dummy}end {name}\n"
        text = text[:end_idx] + insertion + text[end_idx:]

with open('/home/goutev/repos/info-geometry-lean/sandbox/MajoranaPolyaHilbertSocket2.lean', 'w') as f:
    f.write(text)

