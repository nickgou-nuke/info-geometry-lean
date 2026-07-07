import os
import glob
import re
import subprocess
import json

blocks = glob.glob("sandbox/hive_recovery/block_*.lean")
tasks = {}

def get_target_file(content):
    # Find words with capital letters or underscores (likely Lean identifiers)
    words = re.findall(r'[A-Z][a-zA-Z0-9_]*', content)
    words = [w for w in words if len(w) > 4 and w not in ('Theorem', 'Lemma', 'Structure', 'Def', 'Mathlib', 'InfoGeometry')]
    if not words:
        return None
    
    # Try to find a file containing the most of these words
    best_file = None
    best_count = 0
    
    # We use a simple grep for the first 3 words
    search_words = list(set(words))[:3]
    if not search_words: return None
    
    # Just run a fast rg search to see which file has the most occurrences
    # of the first search word
    try:
        res = subprocess.run(["rg", "-l", search_words[0], "lean/"], capture_output=True, text=True)
        files = res.stdout.strip().split('\n')
        if files and files[0]:
            return files[0]
    except Exception:
        pass
        
    return None

for block_file in blocks:
    with open(block_file, "r") as f:
        content = f.read()
    
    if "def verify_" in content and "print(" in content:
        continue # Skip python tests
    if "theorem idProp" in content or "theorem wrappedRfl" in content:
        continue # Skip trivial fake wrappers
        
    target = get_target_file(content)
    if target:
        if target not in tasks:
            tasks[target] = []
        tasks[target].append(content)

# Save tasks
with open("scratch/hive_tasks.json", "w") as f:
    json.dump(tasks, f, indent=2)

print(f"Grouped into {len(tasks)} target files.")
