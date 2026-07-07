import re
import os

with open("scratch/lost_hive_blocks.txt", "r") as f:
    blocks = f.read().split("=========================")

lean_blocks = []
for idx, block in enumerate(blocks):
    if not block.strip(): continue
    # Is it Lean?
    # Python uses 'def name(args):'
    # Lean uses 'def name ... : ... :=' or 'theorem name'
    if "theorem " in block or "lemma " in block or "structure " in block or ":=" in block:
        if "def verify_" in block and ":" in block and "print(" in block:
            continue # likely python
        lean_blocks.append(block.strip())

os.makedirs("sandbox/hive_recovery", exist_ok=True)
for i, b in enumerate(lean_blocks):
    with open(f"sandbox/hive_recovery/block_{i}.lean", "w") as f:
        f.write(b)

print(f"Dumped {len(lean_blocks)} Lean blocks to sandbox/hive_recovery/")
