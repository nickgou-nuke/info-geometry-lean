import os
import glob
import re
import shutil

src_dir = "/media/goutev/SP DS72/auto/proofs/"
dest_dir = "lean/InfoGeometry/Physics/"

# Get a list of all lean files in the source dir
all_src_files = glob.glob(os.path.join(src_dir, "*.lean"))
available_modules = {os.path.basename(f)[:-5]: f for f in all_src_files}

def get_imports(filepath):
    imports = []
    with open(filepath, 'r') as f:
        for line in f:
            match = re.match(r'^import\s+([A-Za-z0-9_]+)', line.strip())
            if match:
                imports.append(match.group(1))
    return imports

# Starting files
queue = ["ZornBraidScalingCovariance"]
processed = set()
to_copy = set()

while queue:
    mod = queue.pop(0)
    if mod in processed:
        continue
    processed.add(mod)
    
    if mod in available_modules:
        to_copy.add(mod)
        imports = get_imports(available_modules[mod])
        for imp in imports:
            if imp in available_modules and imp not in processed:
                queue.append(imp)

print(f"Modules to copy and refactor: {to_copy}")

for mod in to_copy:
    src_path = available_modules[mod]
    with open(src_path, "r") as f:
        content = f.read()
    
    for dep in to_copy:
        content = re.sub(rf'\bimport\s+{dep}\b', f'import InfoGeometry.Physics.{dep}', content)
        content = re.sub(rf'\bnamespace\s+{dep}\b', f'namespace InfoGeometry.Physics.{dep}', content)
        content = re.sub(rf'\bopen\s+{dep}\b', f'open InfoGeometry.Physics.{dep}', content)
        
    dest_path = os.path.join(dest_dir, f"{mod}.lean")
    with open(dest_path, "w") as f:
        f.write(content)

