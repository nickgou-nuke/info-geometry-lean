import os
import glob

recovery_dir = "agent_memory_recovery"
live_dir = "lean"

# Map basename to its length in live repo
live_files = {}
for root, dirs, files in os.walk(live_dir):
    for f in files:
        if f.endswith(".lean"):
            path = os.path.join(root, f)
            with open(path, "r") as p:
                lines = len(p.readlines())
            if f not in live_files or lines > live_files[f][1]:
                live_files[f] = (path, lines)

candidates = []

for basename in os.listdir(recovery_dir):
    rec_path = os.path.join(recovery_dir, basename)
    if not os.path.isdir(rec_path): continue
    
    chunks = glob.glob(os.path.join(rec_path, "*.lean"))
    if not chunks: continue
    
    max_chunk_lines = 0
    for chunk in chunks:
        with open(chunk, "r") as f:
            lines = len(f.readlines())
            if lines > max_chunk_lines:
                max_chunk_lines = lines
                
    if basename in live_files:
        live_path, live_lines = live_files[basename]
        if max_chunk_lines > live_lines + 30: # 30 lines tolerance
            candidates.append((basename, live_lines, max_chunk_lines, live_path))
    else:
        candidates.append((basename, 0, max_chunk_lines, "MISSING"))

print("| File | Live Lines | Max Recovered | Target Path |")
print("|---|---|---|---|")
for c in candidates:
    print(f"| {c[0]} | {c[1]} | {c[2]} | {c[3]} |")

