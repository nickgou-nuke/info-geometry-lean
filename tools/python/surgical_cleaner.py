import re

with open('lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket.lean', 'r') as f:
    text = f.read()

# 1. First, we'll strip the _True and _sorryProof from the genuine ones we want to keep.
text = text.replace('bk_generalizedEigenvalue_True', 'bk_generalizedEigenvalue_law')
text = text.replace('selfAdjoint_forces_realEigenvalue_True', 'selfAdjoint_forces_realEigenvalue_law')
text = text.replace('criticalLine_True', 'criticalLine_law')
text = text.replace('normalizable_True', 'normalizable_law')
text = text.replace('normalizable_iff_criticalLine_sorryProof', 'normalizable_iff_criticalLine_proof')

# 2. We have `isZeroMode_True : Prop := by sorry`. Let's delete it.
text = re.sub(r'\s*isZeroMode_True\s*:\s*Prop\s*:=\s*by\s*sorry', '', text)
text = text.replace('(isZeroMode : Prop)', '') # from mkCriticalLine
text = re.sub(r'\s*isZeroMode_True\s*:=\s*isZeroMode', '', text)

# 3. For all the opaque structures, they are just a bunch of `_True : Prop := by sorry` and `_sorryProof : ...`.
# We want to identify the structures and delete their fields.
# All fields that end with `_True : Prop := by\n    sorry` or `_sorryProof : ...` or `_True : Prop`
# Let's just use regex to remove any line containing `_True : Prop` or `_sorryProof` or `_True\n`.

def remove_vacuous(text):
    lines = text.split('\n')
    new_lines = []
    skip_next = 0
    in_namespace = None
    namespaces_to_drop = {
        'MajoranaPfaffianZetaSpectralSocket',
        'WittenCharacterVsCompletedXiSocket',
        'BosonFermionSuperdeterminantSocket',
        'ArchimedeanGammaFactorSocket',
        'BoundaryScatteringDiscretizationSocket',
        'MBKHeatTraceExplicitFormulaSocket',
        'CompletedXiHilbertPolyaReduction',
        'MajoranaPolyaHilbertBridge',
        'MajoranaBKTraceFormulaBridge',
        'RelativeMBKDeterminantScatteringPacket',
        'EssentialSelfAdjointLimitSocket',
        'ZetaRegularizedPfaffianSocket',
        'CompletedXiSuperdeterminantIdentitySocket',
        'MBKAnalyticFrontier'
    }
    
    for i, line in enumerate(lines):
        if skip_next > 0:
            skip_next -= 1
            continue
            
        stripped = line.strip()
        
        # Namespace dropping
        if line.startswith('namespace '):
            ns = line.strip().split()[1]
            if ns in namespaces_to_drop:
                in_namespace = ns
                continue
        if in_namespace and line.startswith('end '):
            ns = line.strip().split()[1]
            if ns == in_namespace:
                in_namespace = None
                continue
        if in_namespace:
            continue
            
        # If it's a docstring right before a _True field, we want to drop it too.
        # But that's hard to look ahead. Let's just drop the fields first.
        
        if '_True : Prop' in line and 'sorry' in line:
            continue
        if '_True : Prop' in line and i+1 < len(lines) and 'sorry' in lines[i+1]:
            skip_next = 1
            continue
        if '_True : Prop' in line:
            continue
        if '_sorryProof :' in line and i+1 < len(lines) and '_True' in lines[i+1]:
            skip_next = 1
            continue
        if '_sorryProof :' in line:
            continue
        if '_implies_' in line and 'True' in line: # zetaZero_implies_reciprocalSingularity
            if i+1 < len(lines) and 'True' in lines[i+1]:
                skip_next = 1
            continue
            
        new_lines.append(line)
    return '\n'.join(new_lines)

text = remove_vacuous(text)

with open('lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket.lean', 'w') as f:
    f.write(text)

