import os
import glob

recovery_dir = "agent_memory_recovery"
live_dir = "lean"

live_files = {}
for root, dirs, files in os.walk(live_dir):
    for f in files:
        if f.endswith(".lean"):
            live_files[f] = os.path.join(root, f)

fixes = []

for basename in os.listdir(recovery_dir):
    rec_path = os.path.join(recovery_dir, basename)
    if not os.path.isdir(rec_path): continue
    
    chunks = glob.glob(os.path.join(rec_path, "*.lean"))
    if not chunks: continue
    
    best_chunk = None
    max_len = 0
    
    for chunk in chunks:
        with open(chunk, "r") as f:
            content = f.read()
            lines = len(content.splitlines())
            if lines > 50 and " sorry\n" not in content and " sorry" not in content:
                if lines > max_len:
                    max_len = lines
                    best_chunk = chunk
                    
    if not best_chunk: continue
    
    if basename in live_files:
        live_path = live_files[basename]
        with open(live_path, "r") as f:
            live_content = f.read()
        
        # We want to replace if live has sorry OR if the best chunk is significantly longer
        if " sorry" in live_content or max_len > len(live_content.splitlines()) + 30:
            fixes.append((basename, live_path, best_chunk, max_len))
    else:
        fixes.append((basename, "MISSING", best_chunk, max_len))

print("| File | Live Path | Best Chunk | Chunk Lines |")
print("|---|---|---|---|")
for f, path, chunk, lines in fixes:
    print(f"| {f} | {path} | {chunk} | {lines} |")

