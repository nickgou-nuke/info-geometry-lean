import os
import glob
import re

recovery_dir = "agent_memory_recovery"

def find_namespace(file_path):
    with open(file_path, 'r') as f:
        for line in f:
            if line.startswith("namespace "):
                return line.split()[1]
    return None

truncated_candidates = []

for basename in os.listdir(recovery_dir):
    rec_path = os.path.join(recovery_dir, basename)
    if not os.path.isdir(rec_path): continue
    
    chunks = sorted(glob.glob(os.path.join(rec_path, "*.lean")))
    if not chunks: continue
    
    # Get namespace from the first chunk to determine live path
    ns = find_namespace(chunks[0])
    if ns:
        rel_path = ns.replace(".", "/") + ".lean"
        # If the namespace doesn't start with InfoGeometry, this might be off, but assume it does
        if not rel_path.startswith("InfoGeometry"):
            # fallback
            continue
        live_filepath = os.path.join("lean", rel_path)
    else:
        # Fallback if no namespace
        live_filepath = None
    
    max_chunk_lines = 0
    for chunk in chunks:
        with open(chunk, "r") as f:
            lines = f.readlines()
            if len(lines) > max_chunk_lines:
                max_chunk_lines = len(lines)
                
    if live_filepath and os.path.exists(live_filepath):
        with open(live_filepath, "r") as f:
            live_lines = len(f.readlines())
        
        if max_chunk_lines > live_lines + 50:
            truncated_candidates.append((basename, live_lines, max_chunk_lines, live_filepath, rec_path))
    else:
        # Missing or namespace couldn't be resolved
        if live_filepath:
            truncated_candidates.append((basename, 0, max_chunk_lines, live_filepath, rec_path))
        else:
            truncated_candidates.append((basename, 0, max_chunk_lines, "MISSING_NS", rec_path))

print("| File | Live Lines | Max Recovered Chunk Lines | Target Path |")
print("|---|---|---|---|")
for c in truncated_candidates:
    print(f"| {c[0]} | {c[1]} | {c[2]} | {c[3]} |")

