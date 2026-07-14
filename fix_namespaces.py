import os, glob, re

root_dir = "lean/InfoGeometry/"
all_files = glob.glob(root_dir + "**/*.lean", recursive=True)

# Map basename (without .lean) to fully qualified module name
module_map = {}
for f in all_files:
    rel_path = os.path.relpath(f, "lean/")
    module_name = rel_path.replace("/", ".")[:-5]
    basename = os.path.basename(f)[:-5]
    module_map[basename] = module_name

for f in all_files:
    with open(f, "r") as file:
        content = file.read()
    
    modified = False
    
    # Fix import statements
    lines = content.split('\n')
    for i, line in enumerate(lines):
        if line.startswith("import "):
            parts = line.split(" ")
            if len(parts) >= 2:
                imp = parts[1]
                if imp in module_map and imp != module_map[imp]:
                    lines[i] = line.replace("import " + imp, "import " + module_map[imp])
                    modified = True
        elif line.startswith("open "):
            parts = line.split(" ")
            if len(parts) >= 2:
                imp = parts[1]
                if imp in module_map and imp != module_map[imp]:
                    lines[i] = line.replace("open " + imp, "open " + module_map[imp])
                    modified = True

    # Fix namespace statements for newly added files
    basename = os.path.basename(f)[:-5]
    if basename in module_map:
        fqn = module_map[basename]
        content_new = "\n".join(lines)
        if f"namespace {basename}" in content_new and fqn != basename:
            content_new = content_new.replace(f"namespace {basename}", f"namespace {fqn}")
            content_new = content_new.replace(f"end {basename}", f"end {fqn}")
            modified = True
        
        if modified:
            with open(f, "w") as file:
                file.write(content_new)
                print(f"Fixed {f}")

