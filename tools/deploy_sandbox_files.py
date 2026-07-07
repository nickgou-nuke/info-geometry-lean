import json
import os
import shutil

with open("scratch/hive_subagent_targets.json") as f:
    targets = json.load(f)

count = 0
for t in targets:
    target_path = t["target"]
    basename = t["basename"]
    sandbox_path = f"sandbox/{basename}.lean"
    
    if os.path.exists(sandbox_path):
        shutil.copy(sandbox_path, target_path)
        count += 1
        print(f"Restored {basename} to {target_path}")

print(f"Total files restored: {count}")
