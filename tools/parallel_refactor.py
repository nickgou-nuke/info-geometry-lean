import json
import os
import subprocess
import concurrent.futures

with open("scratch/hive_subagent_targets.json") as f:
    targets = json.load(f)

def check_target(t):
    target_path = t["target"]
    fragment_path = t["fragment"]
    basename = t["basename"]
    sandbox_path = f"sandbox/{basename}.lean"
    
    if not os.path.exists(target_path):
        return (t, False)
        
    with open(target_path, "r") as f:
        live_code = f.read()
    with open(fragment_path, "r") as f:
        frag_code = f.read()
        
    combined = live_code + "\n\n" + frag_code
    with open(sandbox_path, "w") as f:
        f.write(combined)
        
    res = subprocess.run(["lake", "env", "lean", sandbox_path], capture_output=True, text=True)
    return (t, res.returncode == 0)

auto_resolved = []
needs_subagent = []

with concurrent.futures.ThreadPoolExecutor(max_workers=8) as executor:
    results = list(executor.map(check_target, targets))

for t, success in results:
    if success:
        auto_resolved.append(t["basename"])
    else:
        needs_subagent.append(t)

print(f"Auto-resolved {len(auto_resolved)} files.")
print(f"Needs subagent: {len(needs_subagent)} files.")

with open("scratch/needs_subagent.json", "w") as f:
    json.dump(needs_subagent, f, indent=2)
with open("scratch/auto_resolved.json", "w") as f:
    json.dump(auto_resolved, f, indent=2)
