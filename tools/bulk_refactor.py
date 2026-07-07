import json
import os
import shutil
import subprocess

with open("scratch/hive_subagent_targets.json") as f:
    targets = json.load(f)

auto_resolved = []
needs_subagent = []

for t in targets:
    target_path = t["target"]
    fragment_path = t["fragment"]
    basename = t["basename"]
    sandbox_path = f"sandbox/{basename}.lean"
    
    if not os.path.exists(target_path):
        # The target file itself doesn't exist?
        needs_subagent.append(t)
        continue
        
    # Merge them
    with open(target_path, "r") as f:
        live_code = f.read()
    with open(fragment_path, "r") as f:
        frag_code = f.read()
        
    combined = live_code + "\n\n" + frag_code
    with open(sandbox_path, "w") as f:
        f.write(combined)
        
    # Check if it compiles
    res = subprocess.run(["lake", "env", "lean", sandbox_path], capture_output=True, text=True)
    if res.returncode == 0:
        auto_resolved.append(basename)
    else:
        needs_subagent.append(t)
        
print(f"Auto-resolved {len(auto_resolved)} files.")
print(f"Needs subagent: {len(needs_subagent)} files.")

with open("scratch/needs_subagent.json", "w") as f:
    json.dump(needs_subagent, f, indent=2)
with open("scratch/auto_resolved.json", "w") as f:
    json.dump(auto_resolved, f, indent=2)
