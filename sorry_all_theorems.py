import sys
import re
import os

def process_file(filepath):
    if not os.path.exists(filepath):
        print(f"Skipping {filepath}")
        return
    with open(filepath, 'r') as f:
        lines = f.read().split('\n')
    
    new_lines = []
    i = 0
    while i < len(lines):
        line = lines[i]
        
        if line.startswith('theorem ') or line.startswith('@[simp] theorem '):
            decl = line
            j = i + 1
            while j < len(lines) and ':=' not in decl:
                decl += '\n' + lines[j]
                j += 1
            if ':=' in decl:
                new_lines.extend(decl.split('\n')[:-1])
                last_line = decl.split('\n')[-1]
                last_line = last_line[:last_line.index(':=')] + ':= by sorry'
                new_lines.append(last_line)
                
                while j < len(lines):
                    if lines[j].startswith('end ') or lines[j].startswith('namespace ') or lines[j].startswith('theorem ') or lines[j].startswith('def ') or lines[j].startswith('@[simp]') or lines[j].startswith('structure ') or lines[j].startswith('instance '):
                        break
                    j += 1
                i = j
                continue
                
        new_lines.append(line)
        i += 1
        
    with open(filepath, 'w') as f:
        f.write('\n'.join(new_lines))
        
files = [
    "lean/InfoGeometry/Algebra/JordanCayleyOrbitStratification.lean",
    "lean/InfoGeometry/Algebra/OrbitClassification.lean",
    "lean/InfoGeometry/Quantum/PauliSoldering.lean",
    "lean/InfoGeometry/Canonical/DrazinGreenHorizonEnvelope.lean",
    "lean/InfoGeometry/Canonical/KreinCarrierInstances.lean",
    "lean/InfoGeometry/Canonical/SouriauMetriplecticOptimalTransport.lean",
    "lean/InfoGeometry/External/Automath/Omega/Zeta.lean",
    "lean/InfoGeometry/Quiver/MirrorCliffordBridge.lean",
    "lean/InfoGeometry/Algebra/Zorn/NormSimilitude.lean",
    "lean/InfoGeometry/LLM/PositionalAttentionBridge.lean",
    "lean/InfoGeometry/External/VirasoroPaperDigest.lean"
]

for f in files:
    process_file(f)

