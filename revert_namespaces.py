import os, glob

root_dir = "lean/InfoGeometry/"
all_files = glob.glob(root_dir + "**/*.lean", recursive=True)

for f in all_files:
    with open(f, "r") as file:
        content = file.read()
    
    rel_path = os.path.relpath(f, "lean/")
    module_name = rel_path.replace("/", ".")[:-5]
    basename = os.path.basename(f)[:-5]
    
    modified = False
    
    if f"namespace {module_name}" in content and module_name != basename:
        content = content.replace(f"namespace {module_name}", f"namespace {basename}")
        content = content.replace(f"end {module_name}", f"end {basename}")
        modified = True
        
    if modified:
        with open(f, "w") as file:
            file.write(content)
        print(f"Reverted namespace in {f}")
