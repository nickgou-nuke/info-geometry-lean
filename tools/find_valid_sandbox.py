import os
import subprocess

sandbox_dir = "sandbox"
canonical_dir = "lean/InfoGeometry"

for root, _, files in os.walk(sandbox_dir):
    for file in files:
        if file.endswith(".lean"):
            sandbox_path = os.path.join(root, file)
            # check if it has sorry
            with open(sandbox_path, "r") as f:
                content = f.read()
                if "sorry" in content or "admit" in content:
                    continue # skip files with sorry
            
            # Find matching file in canonical_dir
            find_cmd = ["find", canonical_dir, "-name", file]
            result = subprocess.run(find_cmd, capture_output=True, text=True)
            matches = result.stdout.strip().split("\n")
            
            if len(matches) > 0 and matches[0]:
                canonical_path = matches[0]
                diff = subprocess.run(["cmp", "-s", sandbox_path, canonical_path])
                if diff.returncode != 0:
                    print(f"VALID & DIFFERENT: {sandbox_path} vs {canonical_path}")
            else:
                print(f"VALID & NEW: {sandbox_path}")
