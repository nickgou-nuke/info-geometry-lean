import os
import re
import glob

files = glob.glob("/home/goutev/auto/proofs/*.lean")
for f in files:
    with open(f, 'r') as file:
        content = file.read()
    
    # Replace theorem X : True := by \n exact trivial
    new_content = re.sub(r'theorem\s+([a-zA-Z0-9_]+)\s*:\s*True\s*:=\s*by\s*exact\s*trivial', r'axiom \1 : Prop', content)
    # Replace lemma X : True := by \n exact trivial
    new_content = re.sub(r'lemma\s+([a-zA-Z0-9_]+)\s*:\s*True\s*:=\s*by\s*exact\s*trivial', r'axiom \1 : Prop', new_content)
    # Replace theorem X : True := trivial
    new_content = re.sub(r'theorem\s+([a-zA-Z0-9_]+)\s*:\s*True\s*:=\s*trivial', r'axiom \1 : Prop', new_content)
    # Replace lemma X : True := trivial
    new_content = re.sub(r'lemma\s+([a-zA-Z0-9_]+)\s*:\s*True\s*:=\s*trivial', r'axiom \1 : Prop', new_content)
    
    if content != new_content:
        with open(f, 'w') as file:
            file.write(new_content)
        print(f"Fixed {f}")
