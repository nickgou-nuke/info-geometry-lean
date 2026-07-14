import os
import glob

# Copy JonesBraidB3.lean
os.system('cp "/media/goutev/SP DS72/auto/proofs/JonesBraidB3.lean" sandbox/zorn_braid/')

files = glob.glob("sandbox/zorn_braid/*.lean")

deps = [os.path.basename(f)[:-5] for f in files]

for file in files:
    with open(file, "r") as f:
        content = f.read()
    
    # Update imports
    for dep in deps:
        content = content.replace(f"import {dep}", f"import InfoGeometry.Physics.{dep}")
        content = content.replace(f"import InfoGeometry.Physics.InfoGeometry.Physics.{dep}", f"import InfoGeometry.Physics.{dep}")
    
    # Update namespaces
    for dep in deps:
        content = content.replace(f"namespace {dep}", f"namespace InfoGeometry.Physics.{dep}")
        content = content.replace(f"namespace InfoGeometry.Physics.InfoGeometry.Physics.{dep}", f"namespace InfoGeometry.Physics.{dep}")
        content = content.replace(f"open {dep}", f"open InfoGeometry.Physics.{dep}")
        content = content.replace(f"open InfoGeometry.Physics.InfoGeometry.Physics.{dep}", f"open InfoGeometry.Physics.{dep}")
    
    basename = os.path.basename(file)
    with open(f"lean/InfoGeometry/Physics/{basename}", "w") as f:
        f.write(content)

