import os
import glob

# Get all .lean files in the proofs directory (excluding some like lakefile.toml if it was lean)
lean_files = [f for f in os.listdir('.') if f.endswith('.lean')]
# Strip .lean
roots = sorted([f[:-5] for f in lean_files if f[:-5] != "lakefile"])

with open('lakefile.toml', 'r') as f:
    lines = f.readlines()

new_lines = []
in_roots = False
for line in lines:
    if line.strip().startswith('roots = ['):
        in_roots = True
        new_lines.append('roots = [\n')
        for r in roots:
            new_lines.append(f'  "{r}",\n')
        new_lines.append(']\n')
        continue
    if in_roots:
        if line.strip() == ']':
            in_roots = False
        continue
    
    new_lines.append(line)

# Add the require block at the end if not present
require_str = '\n[[require]]\nname = "matrix_cookbook"\npath = "external_repos/lean-matrix-cookbook"\n'
if require_str not in "".join(new_lines):
    new_lines.append(require_str)

with open('lakefile.toml', 'w') as f:
    f.writelines(new_lines)
