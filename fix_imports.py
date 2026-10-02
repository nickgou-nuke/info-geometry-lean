import os
import glob

def get_lean_files(directory):
    files = glob.glob(os.path.join(directory, "**", "*.lean"), recursive=True)
    return [f for f in files if "lean_sandbox" not in f]

all_lean_files = get_lean_files("lean/InfoGeometry")

# Convert to module names
modules = []
for f in all_lean_files:
    if f.startswith("lean/"):
        mod = f[5:-5].replace("/", ".")
        modules.append(mod)

# Read existing InfoGeometry.lean
with open("lean/InfoGeometry.lean", "r") as f:
    existing_content = f.read()

new_imports = []
for mod in modules:
    if mod == "InfoGeometry":
        continue
    if f"import {mod}" not in existing_content:
        new_imports.append(f"import {mod}")

new_imports.sort()

with open("lean/InfoGeometry.lean", "a") as f:
    f.write("\n/-! # Recovered Submodules -/\n")
    for imp in new_imports:
        f.write(imp + "\n")

print(f"Added {len(new_imports)} missing imports to lean/InfoGeometry.lean")
