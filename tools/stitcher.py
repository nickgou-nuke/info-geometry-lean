import os
import glob
import re

recovery_dir = "agent_memory_recovery"
out_dir = "agent_memory_recovery_stitched"

os.makedirs(out_dir, exist_ok=True)

for basename in os.listdir(recovery_dir):
    rec_path = os.path.join(recovery_dir, basename)
    if not os.path.isdir(rec_path): continue
    
    chunks = sorted(glob.glob(os.path.join(rec_path, "*.lean")))
    if not chunks: continue
    
    if len(chunks) == 1:
        # Just copy it
        with open(chunks[0], "r") as f:
            content = f.read()
        with open(os.path.join(out_dir, basename), "w") as f:
            f.write(content)
        continue
        
    print(f"Stitching {basename} ({len(chunks)} chunks)...")
    
    # Simple overlap stitcher
    stitched_lines = []
    
    for i, chunk in enumerate(chunks):
        with open(chunk, "r") as f:
            lines = f.readlines()
            
        if i == 0:
            stitched_lines.extend(lines)
            continue
            
        # Find overlap
        # Check from the end of the current stitched_lines
        overlap_found = False
        
        # We try to find the longest prefix of `lines` that matches a suffix of `stitched_lines`
        max_overlap = 0
        search_range = min(len(stitched_lines), len(lines), 300) # search up to 300 lines of overlap
        
        for size in range(1, search_range + 1):
            if stitched_lines[-size:] == lines[:size]:
                max_overlap = size
        
        if max_overlap > 0:
            print(f"  Overlap of {max_overlap} lines found.")
            stitched_lines.extend(lines[max_overlap:])
        else:
            print(f"  NO OVERLAP FOUND for chunk {i}! Appending directly...")
            stitched_lines.extend(["\n-- [STITCHER: MISSING OVERLAP] --\n"])
            stitched_lines.extend(lines)

    with open(os.path.join(out_dir, basename), "w") as f:
        f.writelines(stitched_lines)

print("Stitching complete.")
