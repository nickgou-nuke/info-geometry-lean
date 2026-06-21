import re
with open('/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Clifford/JordanWignerBridge.lean', 'r') as f:
    text = f.read()
for i, line in enumerate(text.splitlines()):
    if 'globalChirality' in line or 'jw' in line or 'witt' in line or 'hestenes' in line:
        print(f"{i+1}: {line}")
