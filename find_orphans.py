import os
import re

def get_imports(filepath):
    imports = []
    if not os.path.exists(filepath):
        return imports
    with open(filepath, 'r', encoding='utf-8') as f:
        for line in f:
            m = re.match(r'^\s*import\s+([A-Za-z0-9_.]+)', line)
            if m:
                imports.append(m.group(1))
    return imports

visited = set()
queue = ["InfoGeometry"]

while queue:
    mod = queue.pop(0)
    if mod in visited:
        continue
    visited.add(mod)
    filepath = "lean/" + mod.replace(".", "/") + ".lean"
    imports = get_imports(filepath)
    for imp in imports:
        if imp.startswith("InfoGeometry"):
            queue.append(imp)

import glob
all_files = glob.glob("lean/InfoGeometry/**/*.lean", recursive=True)
all_mods = set()
for f in all_files:
    if "lean_sandbox" in f:
        continue
    mod = f[5:-5].replace("/", ".")
    all_mods.add(mod)

orphans = all_mods - visited

print(f"Total InfoGeometry modules: {len(all_mods)}")
print(f"Reachable from InfoGeometry.lean: {len(visited)}")
print(f"Orphaned modules: {len(orphans)}")

print("\nFirst 30 orphans:")
for o in sorted(list(orphans))[:30]:
    print(o)

