import re

with open("scratch/lost_hive_blocks.txt", "r") as f:
    blocks = f.read().split("=========================")

for block in blocks:
    if not block.strip(): continue
    names = []
    for line in block.splitlines():
        match = re.match(r'^\s*(?:protected\s+)?(?:noncomputable\s+)?(?:def|theorem|lemma|structure|class|inductive|instance)\s+([a-zA-Z0-9_]+)', line)
        if match:
            names.append(match.group(1))
    if names:
        print(", ".join(names))
