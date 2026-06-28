import os
import shutil

# Find all Lean files
all_lean_files = set()
for root, _, files in os.walk('lean/InfoGeometry'):
    # skip Forge directory if it exists
    if 'Forge' in root.split(os.sep):
        continue
    for file in files:
        if file.endswith('.lean'):
            path = os.path.join(root, file)
            mod = path[5:-5].replace('/', '.')
            all_lean_files.add(mod)

with open('lean/InfoGeometry/All.lean', 'r') as f:
    all_content = f.read()

imported = set()
for line in all_content.splitlines():
    if line.startswith('import '):
        imported.add(line.strip().split(' ')[1])

unimported = all_lean_files - imported
unimported.discard('InfoGeometry.All')
unimported.discard('InfoGeometry.Forge')

print(f"Total files: {len(all_lean_files)}")
print(f"Imported in All.lean: {len(imported)}")
print(f"Unimported: {len(unimported)}")

# Create Forge structure and copy files
forge_mods = []
os.makedirs('lean/InfoGeometry/Forge', exist_ok=True)

for mod in unimported:
    rel_path = mod.replace('InfoGeometry.', '').replace('.', '/') + '.lean'
    src = os.path.join('lean/InfoGeometry', rel_path)
    dst = os.path.join('lean/InfoGeometry/Forge', rel_path)
    
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    shutil.copy2(src, dst)
    
    forge_mod = f"InfoGeometry.Forge.{mod.replace('InfoGeometry.', '')}"
    forge_mods.append(forge_mod)

# Write Forge.lean
forge_mods.sort()
with open('lean/InfoGeometry/Forge.lean', 'w') as f:
    f.write("-- Auto-generated Forge module\n")
    for mod in forge_mods:
        f.write(f"import {mod}\n")

# Append Forge.lean to All.lean
if "import InfoGeometry.Forge" not in all_content:
    with open('lean/InfoGeometry/All.lean', 'a') as f:
        f.write("\nimport InfoGeometry.Forge\n")

print("Forge setup complete.")
