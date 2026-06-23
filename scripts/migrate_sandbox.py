import os
import glob

sandbox_dir = "lean/InfoGeometry/Sandbox"
canonical_dir = "lean/InfoGeometry/Canonical"

files_to_migrate = [
    "CausalFunctor.lean",
    "CliffordCausalBridge.lean",
    "SingularityCausalCoupling.lean",
    "ModularEvolution.lean",
    "DiscreteContinuousTimeBridge.lean"
]

for filename in files_to_migrate:
    src = os.path.join(sandbox_dir, filename)
    dst = os.path.join(canonical_dir, filename)
    
    if os.path.exists(src):
        with open(src, "r") as f:
            content = f.read()
        
        # Replace namespace and imports
        content = content.replace("InfoGeometry.Sandbox", "InfoGeometry.Canonical")
        content = content.replace("namespace InfoGeometry.Sandbox", "namespace InfoGeometry.Canonical")
        
        with open(dst, "w") as f:
            f.write(content)
        print(f"Migrated {filename} to {dst}")
    else:
        print(f"Skipping {filename}: not found in Sandbox")
