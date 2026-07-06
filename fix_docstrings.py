import os
import glob

for filepath in glob.glob("lean/**/*.lean", recursive=True):
    with open(filepath, 'r') as f:
        content = f.read()
    if "/-- BROKEN DECLARATION:" in content:
        content = content.replace("/-- BROKEN DECLARATION:", "/- BROKEN DECLARATION:")
        with open(filepath, 'w') as f:
            f.write(content)
        print(f"Fixed {filepath}")
