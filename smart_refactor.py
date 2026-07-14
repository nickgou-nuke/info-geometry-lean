import re

target_defs = [
    'EntropicSubadditivityStatement',
    'HomologicalPercolationDualityStatement',
    'ScalarFrequencyNotLinguisticInvariant',
    'AlmgrenCycleSpaceStatement',
    'GromovWaistStatement',
    'ScalarCurvatureWidthBoundStatement',
    'QuantumStrongSubadditivityStatement',
    'HomologicalProbabilityPrinciple',
    'HomologicalProbabilityMasterConjecture',
    'AffineClosureOwnerStatement',
    'KleinGromovPipelineStatement',
    'ModularFlowTriviality',
    'TypeIIIRequiresNontracialState',
    'CartanSplitStatement',
    'CliffordProbabilityHasClassicalShadow',
    'InfiniteCliffordTypeIII'
]

with open('lean/InfoGeometry/Probability/HomologicalProbability.lean', 'r') as f:
    lines = f.readlines()

new_lines = []
i = 0
while i < len(lines):
    line = lines[i]
    m = re.match(r'^def\s+([A-Za-z0-9_]+)', line)
    
    if m and m.group(1) in target_defs:
        name = m.group(1)
        
        def_lines = [line]
        i += 1
        while i < len(lines):
            next_line = lines[i]
            if next_line.strip() == '':
                j = i + 1
                is_end = False
                while j < len(lines) and lines[j].strip() == '':
                    j += 1
                if j < len(lines):
                    if not lines[j].startswith(' ') and not lines[j].startswith('--'):
                        is_end = True
                else:
                    is_end = True
                
                if is_end:
                    break
            else:
                if not next_line.startswith(' ') and not next_line.startswith('--'):
                    break
            def_lines.append(next_line)
            i += 1
            
        full_def = "".join(def_lines)
        
        parts = full_def.split(':=', 1)
        if len(parts) < 2:
            new_lines.extend(def_lines)
            continue
            
        sig = parts[0]
        body = parts[1]
        
        # safely replace the trailing `Prop` without stripping or appending colons
        sig = re.sub(r'\bProp\s*$', '', sig)
        
        new_name = name
        if new_name.endswith('Statement'): new_name = new_name[:-9]
        if new_name.endswith('Conjecture'): new_name = new_name[:-10]
        new_name = new_name[0].lower() + new_name[1:]
        
        sig = re.sub(r'^def\s+' + name, f"theorem {new_name}", sig)
        sig = sig.replace('(_', '(')
        
        new_lines.append(sig)
        
        body_lines = body.split('\n')
        if body_lines[0].strip() == '':
            body_lines = body_lines[1:]
            
        last_code_idx = -1
        for idx in range(len(body_lines) - 1, -1, -1):
            cl = body_lines[idx].strip()
            if cl != '' and not cl.startswith('--'):
                last_code_idx = idx
                break
                
        if last_code_idx != -1:
            body_lines[last_code_idx] = body_lines[last_code_idx] + " := by\n  sorry"
            
        for b in body_lines:
            if b.strip() != '' or b == body_lines[-1]: 
                new_lines.append(b + "\n")
                
        while new_lines[-1].strip() == '':
            new_lines.pop()
            
        continue

    new_lines.append(line)
    i += 1

with open('sandbox/HomologicalProbability.lean', 'w') as f:
    f.writelines(new_lines)
