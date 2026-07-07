import re
import subprocess
import os

with open("scratch/hive_code_blocks.txt", "r") as f:
    blocks = f.read().split("=========================")

lost_blocks = []

def check_in_lean(name):
    # Search for the definition in the lean/ directory
    # Using ripgrep or grep
    try:
        # Match 'def name', 'theorem name', 'structure name', 'lemma name'
        # We need a robust regex to avoid partial matches
        pattern = r"(def|theorem|lemma|structure|class)\s+" + re.escape(name) + r"\b"
        result = subprocess.run(["rg", pattern, "lean/"], capture_output=True, text=True)
        if result.stdout.strip():
            return True
        return False
    except Exception:
        return False

for block in blocks:
    if not block.strip(): continue
    # Extract names
    names = []
    for line in block.splitlines():
        # Match def, theorem, lemma, structure followed by the name
        match = re.match(r'^\s*(?:protected\s+)?(?:noncomputable\s+)?(?:def|theorem|lemma|structure|class)\s+([a-zA-Z0-9_]+)', line)
        if match:
            names.append(match.group(1))
    
    if not names: continue
    
    # Check if ANY of the names exist in lean/. If NONE exist, it's a completely lost block!
    all_lost = True
    for name in names:
        if check_in_lean(name):
            all_lost = False
            break
            
    if all_lost:
        lost_blocks.append(block.strip())

with open("scratch/lost_hive_blocks.txt", "w") as f:
    for lb in lost_blocks:
        f.write(lb + "\n\n=========================\n\n")

print(f"Found {len(lost_blocks)} completely lost code blocks.")
