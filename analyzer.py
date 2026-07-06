import os
import re
with open('all_vacuous.txt') as f:
    files = f.read().splitlines()
    
for file in files:
    if not os.path.exists(file): continue
    with open(file) as f:
        content = f.read()
    has_prop = re.search(r'_law\s*:\s*Prop', content)
    has_holds = re.search(r'_law_holds', content)
    has_exact = re.search(r'exact.*_law', content)
    has_sorry = 'sorry' in content
    
    if has_prop or has_holds or has_exact or has_sorry:
        print(f"{file} | prop:{bool(has_prop)} | holds:{bool(has_holds)} | exact:{bool(has_exact)} | sorry:{bool(has_sorry)}")
