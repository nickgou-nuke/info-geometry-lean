import re

with open('lean/InfoGeometry/Probability/HomologicalProbability.lean', 'r') as f:
    lines = f.readlines()

new_lines = []
i = 0
while i < len(lines):
    line = lines[i]
    
    # Check for def XStatement ... : Prop :=
    m = re.match(r'^def\s+([A-Za-z0-9_]+Statement)\b(.*?):\s*Prop\s*:=', line)
    if not m:
        m = re.match(r'^def\s+([A-Za-z0-9_]+)(.*?):\s*Prop\s*:=', line)
        
        # Avoid matching non-theorems if they are just properties. 
        # But let's assume theorems have "Statement", "Conjecture", or "Principle" in their name, or are clearly theorems.
        if m:
            name = m.group(1)
            # filter out actual predicates
            if name in ['IsProjection', 'ProjectionsOrthogonal', 'IsTracialState', 'CARRelations', 'IsInvolution', 'HasKleinFourGrading', 'HasProbabilityDefect', 'GrandCapstoneSlogans']:
                m = None

    if m:
        name = m.group(1)
        args = m.group(2)
        
        # We need to collect the body
        body = []
        i += 1
        while i < len(lines) and (lines[i].startswith('  ') or lines[i].strip() == ''):
            if lines[i].strip() != '':
                body.append(lines[i])
            i += 1
        
        # Transform name (remove Statement/Conjecture/Principle and lowerCamelCase)
        new_name = name
        if new_name.endswith('Statement'): new_name = new_name[:-9]
        if new_name.endswith('Conjecture'): new_name = new_name[:-10]
        # lowerCamelCase
        new_name = new_name[0].lower() + new_name[1:]
        
        # remove _ from args
        args = args.replace('(_', '(')
        
        new_lines.append(f"theorem {new_name}{args}:\n")
        for b in body:
            if b.strip().startswith('let'):
                new_lines.append(b)
            else:
                new_lines.append(b)
        # Check if the last line ends properly
        if new_lines[-1].strip().endswith('Prop'):
            # wait, if body was empty, this is an issue.
            pass
        
        # If the body is just one line or multiple lines, append `:= by sorry`
        # Actually, let's just append ` := by\n  sorry\n` to the last line of the statement
        if new_lines[-1].endswith('\n'):
            new_lines[-1] = new_lines[-1].rstrip('\n') + " := by\n  sorry\n"
        else:
            new_lines[-1] = new_lines[-1] + " := by\n  sorry\n"
            
        continue

    # Write the line as is
    new_lines.append(line)
    i += 1

with open('sandbox/HomologicalProbability.lean', 'w') as f:
    f.writelines(new_lines)
