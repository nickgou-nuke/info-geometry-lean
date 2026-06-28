import os

all_lean_files = set()
for root, _, files in os.walk('lean/InfoGeometry'):
    for file in files:
        if file.endswith('.lean'):
            path = os.path.join(root, file)
            # convert path to import format, e.g. lean/InfoGeometry/Foo.lean -> InfoGeometry.Foo
            mod = path[5:-5].replace('/', '.')
            all_lean_files.add(mod)

with open('lean/InfoGeometry/All.lean', 'r') as f:
    all_content = f.read()

imported = set()
for line in all_content.splitlines():
    if line.startswith('import '):
        imported.add(line.split(' ')[1])

unimported = all_lean_files - imported
unimported.discard('InfoGeometry.All')
unimported.discard('InfoGeometry.Forge')

print(f"Total files: {len(all_lean_files)}")
print(f"Imported in All.lean: {len(imported)}")
print(f"Unimported: {len(unimported)}")

# Create Forge folder
os.makedirs('lean/InfoGeometry/Forge', exist_ok=True)

forge_imports = []
import shutil

for mod in unimported:
    # copy to Forge
    src = f"lean/{mod.replace('.', '/')}.lean"
    filename = os.path.basename(src)
    dst = f"lean/InfoGeometry/Forge/{filename}"
    
    # Avoid overwriting if multiple files have the same name? They shouldn't if they come from different paths, but we will see
    # actually, the prompt says: "put copies of such files inside of it"
    # To keep module names valid, maybe we should just rename them or keep the hierarchy?
    # "put copies of such files inside of it" -> let's just copy them and rename if collision.
    
    # A simpler way: just create a file `lean/InfoGeometry/Forge.lean` that imports all unimported modules directly?
    # "we maybe shall make a folder Forga and put copies of such files inside of it and make a moduel Forge"
    pass

