import re
import glob

files = [
    'lean/InfoGeometry/OperatorAlgebra/CPTSymmetryBranch.lean',
    'lean/InfoGeometry/OperatorAlgebra/ChiralLightconeStinespring.lean',
    'lean/InfoGeometry/Arithmetic/ZetaTraceSpecialization.lean',
    'lean/InfoGeometry/Arithmetic/FredholmClosure.lean',
    'lean/InfoGeometry/Canonical/SplitCliffordHeisenbergAdapter.lean'
]

for file in files:
    try:
        with open(file, 'r') as f:
            text = f.read()

        # Remove the fields that end with _law
        text = re.sub(r'^\s+\w+_law\s*:\s*.*?\n', '', text, flags=re.MULTILINE)
        
        # Remove exact P.*_law
        text = re.sub(r'exact [a-zA-Z0-9_]+\.\w+_law', 'sorry', text)
        
        # Remove exact .*_law
        text = re.sub(r'exact \w+_law', 'sorry', text)
        
        with open(file, 'w') as f:
            f.write(text)
        print(f"Processed {file}")
    except FileNotFoundError:
        pass
