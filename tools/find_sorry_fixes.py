import os

stitched_dir = "agent_memory_recovery_stitched"
live_dir = "lean"

live_files = {}
for root, dirs, files in os.walk(live_dir):
    for f in files:
        if f.endswith(".lean"):
            live_files[f] = os.path.join(root, f)

fixes = []

for f in os.listdir(stitched_dir):
    if not f.endswith(".lean"): continue
    
    stitched_path = os.path.join(stitched_dir, f)
    with open(stitched_path, "r") as fh:
        stitched_content = fh.read()
        
    # Check if stitched version is sorry-free
    if " sorry\n" in stitched_content or " sorry" in stitched_content:
        continue # Stitched also has sorry, or it's a false positive, ignore for now
        
    if f in live_files:
        live_path = live_files[f]
        with open(live_path, "r") as fh:
            live_content = fh.read()
            
        if " sorry" in live_content:
            fixes.append((f, live_path))
    else:
        # It's missing entirely!
        fixes.append((f, "MISSING"))

print("| File | Live Path |")
print("|---|---|")
for f, path in fixes:
    print(f"| {f} | {path} |")

