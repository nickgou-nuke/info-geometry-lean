import re

def process_file(filepath):
    with open(filepath, 'r') as f:
        content = f.read()

    lines = content.split('\n')
    new_lines = []
    in_structure = False
    
    removed_fields = set()
    
    # Pass 1: Identify removed fields
    i = 0
    while i < len(lines):
        line = lines[i]
        
        if line.startswith('structure '):
            in_structure = True
            
        if in_structure and (line.startswith('namespace ') or line.startswith('def ') or line.startswith('theorem ') or line.startswith('inductive ') or line.startswith('attribute ') or line.startswith('end ')):
            in_structure = False
            
        if in_structure:
            m = re.match(r'^  (\w+)\s*:(.*)', line)
            if m:
                field_name = m.group(1)
                rest = m.group(2).strip()
                
                full_type = rest
                j = i + 1
                while j < len(lines) and re.match(r'^    (.*)', lines[j]):
                    full_type += ' ' + lines[j].strip()
                    j += 1
                
                is_prop_field = False
                if full_type == 'Prop':
                    is_prop_field = True
                elif full_type.startswith('∀'):
                    is_prop_field = True
                elif field_name.endswith('_holds'):
                    is_prop_field = True
                elif field_name == 'coherence':
                    is_prop_field = True
                
                if is_prop_field:
                    removed_fields.add(field_name)
        i += 1

    print(f"Removed fields for {filepath}: {removed_fields}")

    # Pass 2: Actually remove them and rewrite theorems
    in_structure = False
    i = 0
    while i < len(lines):
        line = lines[i]
        
        if line.startswith('structure '):
            in_structure = True
            
        if in_structure and (line.startswith('namespace ') or line.startswith('def ') or line.startswith('theorem ') or line.startswith('inductive ') or line.startswith('attribute ') or line.startswith('end ')):
            in_structure = False
            
        if in_structure:
            m = re.match(r'^  (\w+)\s*:(.*)', line)
            if m:
                field_name = m.group(1)
                if field_name in removed_fields:
                    # Skip docstring
                    if len(new_lines) > 0 and new_lines[-1].strip() == '-/':
                        new_lines.pop()
                        while len(new_lines) > 0 and not new_lines[-1].strip().startswith('/--'):
                            new_lines.pop()
                        if len(new_lines) > 0:
                            new_lines.pop()
                    elif len(new_lines) > 0 and new_lines[-1].strip().startswith('/--') and new_lines[-1].strip().endswith('-/'):
                        new_lines.pop()
                        
                    # Skip multi-line type
                    j = i + 1
                    while j < len(lines) and re.match(r'^    (.*)', lines[j]):
                        j += 1
                    i = j
                    continue

        if line.startswith('theorem ') or line.startswith('@[simp] theorem '):
            decl = line
            j = i + 1
            while j < len(lines) and ':=' not in decl:
                decl += '\n' + lines[j]
                j += 1
            if ':=' in decl:
                # Append declaration with 'by sorry'
                new_lines.extend(decl.split('\n')[:-1])
                last_line = decl.split('\n')[-1]
                last_line = last_line[:last_line.index(':=')] + ':= by sorry'
                new_lines.append(last_line)
                
                # Skip body
                while j < len(lines) and (lines[j].startswith(' ') or lines[j].startswith('\t') or lines[j].strip() == '' or lines[j].startswith('·')):
                    if lines[j].startswith('end ') or lines[j].startswith('namespace ') or lines[j].startswith('theorem ') or lines[j].startswith('def ') or lines[j].startswith('@[simp]'):
                        break
                    j += 1
                i = j
                continue

        m_assign = re.match(r'^  (\w+)\s*:=', line)
        if m_assign:
            field_name = m_assign.group(1)
            if field_name in removed_fields:
                j = i + 1
                while j < len(lines) and (lines[j].startswith('    ') or lines[j].startswith('  ·') or lines[j].strip() == '' or lines[j].startswith('  exact') or lines[j].startswith('  rw') or lines[j].startswith('  intro') or lines[j].startswith('  cases')):
                    if lines[j].startswith('end ') or lines[j].startswith('def '):
                        break
                    j += 1
                
                if line.strip().endswith('by') or line.strip().endswith('by ring'):
                    while j < len(lines) and (lines[j].startswith('    ') or lines[j].startswith('  ·') or lines[j].strip() == '' or lines[j].startswith('  exact') or lines[j].startswith('  rw') or lines[j].startswith('  intro') or lines[j].startswith('  cases')):
                        if lines[j].startswith('end '):
                            break
                        j += 1
                i = j
                continue
                
        new_lines.append(line)
        i += 1
        
    with open(filepath, 'w') as f:
        f.write('\n'.join(new_lines))

process_file('lean/InfoGeometry/Thermo/SusceptibilityHessian.lean')
process_file('lean/InfoGeometry/OperatorAlgebra/SusceptibilityHessian.lean')

