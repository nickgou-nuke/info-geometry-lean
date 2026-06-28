import os, re
import sys

def find_sorrys(directory):
    total = 0
    for root, _, files in os.walk(directory):
        for file in files:
            if not file.endswith('.lean'): continue
            path = os.path.join(root, file)
            with open(path, 'r', encoding='utf-8') as f:
                content = f.read()
                
            # Naive comment stripping:
            # remove block comments /- ... -/
            content = re.sub(r'/-.*?-/', '', content, flags=re.DOTALL)
            
            lines = content.split('\n')
            for i, line in enumerate(lines):
                # remove line comments
                line = line.split('--')[0]
                if re.search(r'\bsorry\b', line):
                    print(f"{path}:{i+1}: {line.strip()}")
                    total += 1
    print(f"\nTotal sorrys: {total}")

find_sorrys('lean/InfoGeometry')
