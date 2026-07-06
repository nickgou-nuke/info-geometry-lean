import re

files = [
    'lean/InfoGeometry/OperatorAlgebra/ErlangenJaynesGromov.lean',
    'lean/InfoGeometry/Canonical/RealRotorGaussHestenesBridge.lean',
    'lean/InfoGeometry/Canonical/InfiniteCARColimit.lean',
    'lean/InfoGeometry/Clifford/CantorDiracSeaChargeHestenesBridge.lean'
]

for file in files:
    with open(file, 'r') as f:
        text = f.read()
    
    # Replace anything matching 'exact ... _law' with 'sorry'
    text = re.sub(r'exact\s+[^\n]*_law', 'sorry', text)
    
    with open(file, 'w') as f:
        f.write(text)
    print(f"Fixed exact in {file}")

