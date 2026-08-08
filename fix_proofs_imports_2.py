import os
import re

proofs_dir = 'proofs'
known_roots = ['Mathlib', 'Init', 'Lean', 'Std', 'ProofWidgets', 'Qq', 'Cli', 'Aesop', 'InfoGeometry', 'proofs', 'Batteries', 'Plsql', 'Lake']

for root, dirs, files in os.walk(proofs_dir):
    if '.lake' in dirs:
        dirs.remove('.lake')
    for file in files:
        if file.endswith('.lean'):
            path = os.path.join(root, file)
            with open(path, 'r') as f:
                lines = f.readlines()
            changed = False
            for i, line in enumerate(lines):
                if line.startswith('import '):
                    parts = line.split()
                    if len(parts) >= 2:
                        module = parts[1]
                        module_root = module.split('.')[0]
                        if module_root not in known_roots:
                            lines[i] = line.replace(f'import {module}', f'import proofs.{module}')
                            changed = True
            if changed:
                with open(path, 'w') as f:
                    f.writelines(lines)
