import os
import re

def strip_comments(text):
    # Remove block comments
    text = re.sub(r'/-.*?-/', '', text, flags=re.DOTALL)
    # Remove line comments
    text = re.sub(r'--.*', '', text)
    return text

files_with_sorry = []
for root, _, files in os.walk('lean'):
    for file in files:
        if file.endswith('.lean'):
            path = os.path.join(root, file)
            with open(path, 'r', encoding='utf-8') as f:
                content = f.read()
            stripped = strip_comments(content)
            if re.search(r'\bsorry\b', stripped):
                files_with_sorry.append(path)

for f in files_with_sorry:
    print(f)
