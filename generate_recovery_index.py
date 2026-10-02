import os
import glob
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
    for imp in get_imports(filepath):
        if imp.startswith("InfoGeometry"):
            queue.append(imp)

all_files = glob.glob("lean/InfoGeometry/**/*.lean", recursive=True)
all_mods = set()
for f in all_files:
    if "lean_sandbox" in f:
        continue
    mod = f[5:-5].replace("/", ".")
    all_mods.add(mod)

orphans = all_mods - visited

# Sort them alphabetically
orphans = sorted(list(orphans))

with open("lean/InfoGeometry/RecoveredIndex.lean", "w", encoding='utf-8') as f:
    f.write("/-!\n# Recovered Index\n")
    f.write(f"This index recovers {len(orphans)} orphaned modules disconnected by previous agents.\n-/\n\n")
    for o in orphans:
        f.write(f"import {o}\n")

