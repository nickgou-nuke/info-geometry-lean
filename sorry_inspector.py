import sys
import re

files = [
    'lean/InfoGeometry/Projective/KleinQuadric.lean',
    'lean/InfoGeometry/Canonical/ModularLorentzBoost.lean',
    'lean/InfoGeometry/Canonical/GaugeGroups.lean',
    'lean/InfoGeometry/Algebra/NilpotentNonunit.lean'
]

for file in files:
    print(f"\n--- {file} ---")
    try:
        with open(file) as f:
            lines = f.readlines()
        for i, line in enumerate(lines):
            if 'sorry' in line:
                start = max(0, i-5)
                end = min(len(lines), i+3)
                print("".join(lines[start:end]))
                print("---")
    except Exception as e:
        print(e)
