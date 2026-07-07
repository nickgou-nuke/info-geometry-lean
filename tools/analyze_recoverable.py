import os
import glob

# Build a map of all live files in the repository
live_files = {}
for root, _, files in os.walk("lean/InfoGeometry"):
    for file in files:
        if file.endswith(".lean"):
            live_files[file] = os.path.join(root, file)

recovered_dirs = glob.glob("agent_memory_recovery/*.lean")

missing = []
present_better = []

for d in recovered_dirs:
    basename = os.path.basename(d) # e.g. MobiusGeometry.lean
    snapshots = glob.glob(os.path.join(d, "*.lean"))
    if not snapshots:
        continue
    
    # Get largest snapshot
    largest_snapshot = max(snapshots, key=lambda f: os.path.getsize(f))
    with open(largest_snapshot, "r") as f:
        largest_lines = f.readlines()
    num_lines = len(largest_lines)
    num_sorrys = sum(1 for line in largest_lines if "sorry" in line)
    
    if basename not in live_files:
        missing.append((basename, largest_snapshot, num_lines, num_sorrys))
    else:
        live_path = live_files[basename]
        with open(live_path, "r") as f:
            live_lines = f.readlines()
        live_num_lines = len(live_lines)
        live_num_sorrys = sum(1 for line in live_lines if "sorry" in line)
        
        # We consider the recovered file "better" if it has fewer sorrys or significantly more lines (+10 lines)
        if num_sorrys < live_num_sorrys or num_lines > live_num_lines + 10:
            present_better.append((basename, largest_snapshot, num_lines, num_sorrys, live_path, live_num_lines, live_num_sorrys))

print(f"=== MISSING FROM CODEBASE: {len(missing)} files ===")
print("These files exist in agent memory but were deleted from the live repository.")
for m in sorted(missing, key=lambda x: x[0]):
    print(f"- {m[0]}: Recovered version has {m[2]} lines, {m[3]} sorrys. (Path: {m[1]})")

print(f"\n=== POTENTIALLY BETTER IN RECOVERY: {len(present_better)} files ===")
print("These files exist in both, but the recovered version has completed proofs or more code.")
for p in sorted(present_better, key=lambda x: x[0]):
    print(f"- {p[0]}:")
    print(f"    Live version:      {p[5]} lines, {p[6]} sorrys")
    print(f"    Recovered version: {p[2]} lines, {p[3]} sorrys")
    print(f"    Path: {p[1]}")
