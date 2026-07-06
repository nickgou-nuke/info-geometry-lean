import os

def fix_file(filepath):
    with open(filepath, 'r') as f:
        lines = f.read().splitlines()
    
    new_lines = []
    changed = False
    for line in lines:
        if line.startswith('import InfoGeometry.'):
            mod = line.split()[1]
            path = 'lean/' + mod.replace('.', '/') + '.lean'
            if not os.path.exists(path):
                print(f"Removing broken import {mod} from {filepath}")
                changed = True
                continue
        new_lines.append(line)
        
    if changed:
        with open(filepath, 'w') as f:
            f.write('\n'.join(new_lines) + '\n')

for root, _, files in os.walk('lean'):
    for file in files:
        if file.endswith('.lean'):
            fix_file(os.path.join(root, file))
