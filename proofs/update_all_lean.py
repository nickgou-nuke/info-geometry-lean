import os
lean_files = [f for f in os.listdir('.') if f.endswith('.lean')]
roots = sorted([f[:-5] for f in lean_files if f[:-5] != "lakefile" and f[:-5] != "All"])

with open('All.lean', 'w') as f:
    for r in roots:
        f.write(f'import {r}\n')
    f.write('import MatrixCookbook\n')
