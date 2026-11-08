import re

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'r') as f:
    content = f.read()

# We'll process line by line
lines = content.split('\n')
out = []
defined_symbols = set(['eps0', 'eps1', 'eps2', 'iota0', 'iota1', 'iota2'])

# Regular expressions to catch the start of theorems
re_theorem = re.compile(r'theorem (\w+)')

i = 0
while i < len(lines):
    line = lines[i]
    
    if line.startswith('def gam0'): defined_symbols.update(['gam0', 'gam1', 'gam2'])
    if line.startswith('def deRhamDirac'): defined_symbols.add('deRhamDirac')
    if line.startswith('def fermionParity'): defined_symbols.add('fermionParity')
    
    # Check if we are at `ext i j; fin_cases i <;> fin_cases j`
    if 'ext i j; fin_cases i <;> fin_cases j' in line:
        out.append(line)
        # Skip next lines until the end of the block or until `)` or `}`
        # The block can be `all_goals { ... }` or `<;> ( ... )`
        buffer = []
        is_all_goals = False
        if i + 1 < len(lines) and 'all_goals {' in lines[i+1]:
            is_all_goals = True
            j = i + 1
            while j < len(lines) and '}' not in lines[j]:
                j += 1
            i = j
        elif '<;> (' in line:
            # It's inline `ext ... <;> ( ... )`
            j = i + 1
            while j < len(lines) and ')' not in lines[j]:
                j += 1
            i = j
        else:
            # Try to see if it's the old inline style over multiple lines
            pass
            
        # Emit our custom block
        out.append("  all_goals {")
        
        # Determine what to simplify based on currently defined symbols
        if 'deRhamDirac' in defined_symbols or 'fermionParity' in defined_symbols:
            l = []
            if 'deRhamDirac' in defined_symbols: l.append('deRhamDirac')
            if 'fermionParity' in defined_symbols: l.append('fermionParity')
            out.append(f"    simp only [{', '.join(l)}]")
            out.append("    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.sub_apply]")
            
        if 'gam0' in defined_symbols:
            out.append("    simp only [gam0, gam1, gam2]")
            out.append("    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.sub_apply]")
            
        out.append("    simp only [eps0, eps1, eps2, iota0, iota1, iota2]")
        out.append("    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.sub_apply, Fin.sum_univ_eight]")
        out.append("    simp")
        out.append("    try norm_num")
        out.append("  }")
        
    else:
        # Avoid double emitting if we matched `<;> (` on the same line
        # Actually `ext i j; fin_cases i <;> fin_cases j` might have `<;> (` on the same line.
        # But we handled it above by skipping.
        if 'ext i j; fin_cases i <;> fin_cases j <;> (' in line:
            # Wait, the `if 'ext i j;' in line` already caught this!
            pass
        else:
            out.append(line)
            
    i += 1

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'w') as f:
    f.write('\n'.join(out))
