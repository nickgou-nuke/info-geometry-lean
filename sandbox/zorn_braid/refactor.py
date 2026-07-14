import os
import glob

files = glob.glob("*.lean")
for file in files:
    with open(file, "r") as f:
        content = f.read()
    
    # Update imports
    for dep in [f[:-5] for f in files]:
        content = content.replace(f"import {dep}", f"import InfoGeometry.Physics.{dep}")
    
    # Update namespaces
    for dep in [f[:-5] for f in files]:
        content = content.replace(f"namespace {dep}", f"namespace InfoGeometry.Physics.{dep}")
        content = content.replace(f"open {dep}", f"open InfoGeometry.Physics.{dep}")
    
    with open(f"../../lean/InfoGeometry/Physics/{file}", "w") as f:
        f.write(content)

