import os
import glob
import re

dest_dir = "lean/InfoGeometry/Physics/"
files = glob.glob(os.path.join(dest_dir, "*.lean"))

for file in files:
    with open(file, "r") as f:
        content = f.read()
    
    # We want to replace "end <Module>" with "end InfoGeometry.Physics.<Module>"
    # Let's extract the modules from the available filenames.
    modules = [os.path.basename(f)[:-5] for f in files]
    
    for mod in modules:
        content = re.sub(rf'\bend\s+{mod}\b', f'end InfoGeometry.Physics.{mod}', content)
        
    with open(file, "w") as f:
        f.write(content)

