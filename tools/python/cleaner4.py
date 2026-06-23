import re

with open('lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket.lean', 'r') as f:
    lines = f.readlines()

new_lines = []
i = 0
in_namespace_to_drop = False

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

while i < len(lines):
    line = lines[i]
    stripped = line.strip()

    # Drop specific namespaces
    if line.startswith('namespace '):
        ns = stripped.split()[1]
        if ns in namespaces_to_drop:
            in_namespace_to_drop = ns
            i += 1
            continue
    if in_namespace_to_drop and line.startswith('end '):
        ns = stripped.split()[1]
        if ns == in_namespace_to_drop:
            in_namespace_to_drop = False
            i += 1
            continue
    if in_namespace_to_drop:
        i += 1
        continue

    # Drop owner targets
    # An owner target starts with /-- then eventually @[owner_target_tag] then theorem ... then ends when next line is not indented, or hits an empty line after the body.
    if stripped == '/--':
        # peek ahead
        is_owner_target = False
        peek_i = i + 1
        while peek_i < len(lines):
            if lines[peek_i].strip() == '@[owner_target_tag]':
                is_owner_target = True
                break
            if lines[peek_i].strip() == '-/':
                # if the next line after -/ is owner target
                if peek_i + 1 < len(lines) and lines[peek_i+1].strip() == '@[owner_target_tag]':
                    is_owner_target = True
                break
            peek_i += 1
        
        if is_owner_target:
            # skip until we consume the theorem body
            # body ends when we hit an empty line or a non-indented line after the theorem signature
            i = peek_i + 2 # skip @[owner_target_tag] and theorem ...
            while i < len(lines):
                if lines[i].strip() == '' or (not lines[i].startswith(' ') and not lines[i].startswith('\t')):
                    break
                i += 1
            continue

    # Drop fake proof fields in structures
    # pfaffian_zeta_identity_True : Prop := by\n    sorry
    if stripped.endswith('_True : Prop := by') and i + 1 < len(lines) and lines[i+1].strip() == 'sorry':
        i += 2
        continue
    # pfaffian_zeta_identity_sorryProof :\n    pfaffian_zeta_identity_True
    if stripped.endswith('_sorryProof :') and i + 1 < len(lines) and lines[i+1].strip().endswith('_True'):
        i += 2
        continue
    # zetaZero_implies_reciprocalSingularity :\n    zetaZero_True -> reciprocalZetaSingularity_True
    if 'implies' in stripped and stripped.endswith(':'):
        if i + 1 < len(lines) and '_True' in lines[i+1]:
            i += 2
            continue

    # One line variants
    if stripped.endswith('_True : Prop'):
        i += 1
        continue

    # isZeroMode from mkCriticalLine
    if '(isZeroMode : Prop) :' in stripped:
        new_lines.append(line.replace('(isZeroMode : Prop) ', ''))
        i += 1
        continue
    if 'isZeroMode_True := isZeroMode' in stripped:
        i += 1
        continue

    # mkCriticalLine fields (rfls)
    if stripped.endswith('_True := by rfl'):
        # keep them but replace _True
        new_lines.append(line.replace('_True', '_law'))
        i += 1
        continue

    # _True to _law replacements for genuine fields
    line = line.replace('bk_generalizedEigenvalue_True', 'bk_generalizedEigenvalue_law')
    line = line.replace('selfAdjoint_forces_realEigenvalue_True', 'selfAdjoint_forces_realEigenvalue_law')
    line = line.replace('criticalLine_True', 'criticalLine_law')
    line = line.replace('normalizable_True', 'normalizable_law')
    line = line.replace('normalizable_iff_criticalLine_sorryProof', 'normalizable_iff_criticalLine_proof')

    new_lines.append(line)
    i += 1

with open('lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket.lean', 'w') as f:
    f.writelines(new_lines)
