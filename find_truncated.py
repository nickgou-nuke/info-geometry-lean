import os
import glob

live_dir = "lean"
recovery_dir = "agent_memory_recovery"

# Find all lean files in the live directory
live_files = {}
for root, dirs, files in os.walk(live_dir):
    for f in files:
        if f.endswith(".lean"):
            live_files[f] = os.path.join(root, f)

truncated_candidates = []

# Check each directory in agent_memory_recovery
for basename in os.listdir(recovery_dir):
    rec_path = os.path.join(recovery_dir, basename)
    if not os.path.isdir(rec_path): continue
    
    # Get all chunks
    chunks = sorted(glob.glob(os.path.join(rec_path, "*.lean")))
    if not chunks: continue
    
    # Calculate total unique size of recovered (heuristic: sum of lines, though there is overlap)
    # Actually, we can just take the size of the largest chunk as a lower bound!
    max_chunk_lines = 0
    for chunk in chunks:
        with open(chunk, "r") as f:
            lines = f.readlines()
            if len(lines) > max_chunk_lines:
                max_chunk_lines = len(lines)
    
    # If it exists in live, compare
    if basename in live_files:
        live_filepath = live_files[basename]
        with open(live_filepath, "r") as f:
            live_lines = len(f.readlines())
        
        if max_chunk_lines > live_lines + 50:
            truncated_candidates.append((basename, live_lines, max_chunk_lines, live_filepath, rec_path))
    else:
        # File is completely missing from live codebase!
        truncated_candidates.append((basename, 0, max_chunk_lines, "MISSING", rec_path))

print("| File | Live Lines | Max Recovered Chunk Lines | Status |")
print("|---|---|---|---|")
for c in truncated_candidates:
    status = "TRUNCATED" if c[1] > 0 else "MISSING"
    print(f"| {c[0]} | {c[1]} | {c[2]} | {status} |")

