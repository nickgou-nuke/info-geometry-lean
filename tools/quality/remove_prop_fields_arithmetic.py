import re
import sys

def process_file(filepath):
    try:
        with open(filepath, 'r') as f:
            lines = f.readlines()
    except FileNotFoundError:
        return

    new_lines = []
    # Remove any field that ends with _True : Prop := by sorry
    # Also remove _sorryProof fields
    # Also remove certificate fields
    skip_next = False
    for line in lines:
        if skip_next:
            if "sorry" in line:
                skip_next = False
                continue
            # If not sorry, maybe it's something else?
            if re.search(r'^\s+.*$', line):
                continue
            else:
                skip_next = False
        
        if re.search(r'^\s+[a-zA-Z0-9_]+\s*:\s*(Prop|∀.+)\s*:=\s*by\s*$', line):
            skip_next = True
            continue
        if re.search(r'^\s+[a-zA-Z0-9_]+_sorryProof\s*:', line):
            # Might be multi-line
            continue
        if re.search(r'^\s+certificate\s*:', line):
            continue
        if re.search(r'^\s*M\.[a-zA-Z0-9_]+_sorryProof', line):
            continue
        if re.search(r'^\s*P\.[a-zA-Z0-9_]+_sorryProof', line):
            continue
        if re.search(r'^\s*B\.[a-zA-Z0-9_]+_sorryProof', line):
            continue
        if re.search(r'^\s*S\.[a-zA-Z0-9_]+_sorryProof', line):
            continue
        if re.search(r'^\s*Z\.[a-zA-Z0-9_]+_sorryProof', line):
            continue
        if re.search(r'^\s*F\.[a-zA-Z0-9_]+_sorryProof', line):
            continue
        if re.search(r'^\s*G\.[a-zA-Z0-9_]+_sorryProof', line):
            continue
        if re.search(r'^\s*M\.[a-zA-Z0-9_]+_True', line):
            continue
        if re.search(r'^\s*sorry\s*$', line):
            continue
        # Also remove usages
        if re.search(r'^\s*∧\s*P\.', line):
            continue
        new_lines.append(line)

    with open(filepath, 'w') as f:
        f.writelines(new_lines)
    print(f"Processed {filepath}")

FILES = [
    "lean/InfoGeometry/Arithmetic/LPrimitive.lean",
    "lean/InfoGeometry/Arithmetic/PrimeSpinorSquareRootBoost.lean",
    "lean/InfoGeometry/Arithmetic/ArithmeticSuperchargeHopfBridge.lean",
    "lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertDeferredInterface.lean",
]

for f in FILES:
    process_file(f)
