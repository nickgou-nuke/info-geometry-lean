import os

untracked_dir = "agent_memory_recovery/untracked_lean"
live_dir = "lean"

live_files = {}
for root, dirs, files in os.walk(live_dir):
    for f in files:
        if f.endswith(".lean"):
            live_files[f] = os.path.join(root, f)

fixes = []

for f in os.listdir(untracked_dir):
    if not f.endswith(".lean"): continue
    
    untracked_path = os.path.join(untracked_dir, f)
    with open(untracked_path, "r") as fh:
        untracked_content = fh.read()
        
    if " sorry\n" in untracked_content or " sorry" in untracked_content:
        continue
        
    if f in live_files:
        live_path = live_files[f]
        with open(live_path, "r") as fh:
            live_content = fh.read()
            
        if " sorry" in live_content:
            fixes.append((f, live_path))
    else:
        fixes.append((f, "MISSING"))

print("| File | Live Path |")
print("|---|---|")
for f, path in fixes:
    print(f"| {f} | {path} |")

