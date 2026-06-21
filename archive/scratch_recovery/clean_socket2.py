import re

with open('lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket.lean', 'r') as f:
    lines = f.readlines()

new_lines = []
skip = False
for line in lines:
    if line.strip().startswith('@[owner_target_tag]'):
        skip = True
    if line.strip().startswith('@[bridge_target_tag]'):
        skip = True
    if line.strip().startswith('/-- Re-export'):
        skip = True
    if line.strip().startswith('/-- The frontier includes'):
        skip = True
    if line.strip().startswith('/-- Owner-target packaging'):
        skip = True
    if line.strip().startswith('/-- Conditional RH readback'):
        skip = True
        
    if skip:
        # If we see `:=` and then `sorryProof` or `exact` or `implies`, we stop skipping at the end of the assignment
        if 'sorryProof' in line or 'exact ⟨' in line or 'hilbertPolya_reduction_sorryProof' in line:
            skip = False
            continue
        elif '⟩' in line and not line.strip().startswith('--'):
            skip = False
            continue
        continue
    
    # Also delete any line with `_True :=`
    if '_True :=' in line or 'sorryProof' in line:
        continue
    if '_True :' in line:
        continue
        
    new_lines.append(line)

with open('lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket.lean', 'w') as f:
    f.writelines(new_lines)
