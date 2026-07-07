import json
import os

with open("scratch/hive_tasks.json") as f:
    data = json.load(f)

os.makedirs("sandbox/hive_fragments", exist_ok=True)
valid_targets = []

for target, blocks in data.items():
    if not target.endswith(".lean"): continue
    if target == "lean/InfoGeometry.lean": continue
    if "DAG/" in target: continue # Skip tool/dag code
    if "scripts/" in target: continue
    
    basename = os.path.basename(target).replace(".lean", "")
    fragment_path = f"sandbox/hive_fragments/fragment_{basename}.lean"
    with open(fragment_path, "w") as f:
        f.write("\n\n-- LOST FRAGMENT RECOVERED FROM HIVE MEMORY --\n\n".join(blocks))
    
    valid_targets.append({
        "target": target,
        "fragment": fragment_path,
        "basename": basename
    })

print(f"Prepared {len(valid_targets)} targets for subagents.")
with open("scratch/hive_subagent_targets.json", "w") as f:
    json.dump(valid_targets, f, indent=2)
