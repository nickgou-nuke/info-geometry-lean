import re

with open('lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket.lean', 'r') as f:
    lines = f.readlines()

new_lines = []
skip_namespace = False
skip_owner_target = False

namespaces_to_delete = {
    'MellinPlancherelCriticalLinePacket',
    'BerryKeatingOperatorPacket',
    'MajoranaBerryKeatingOperatorPacket',
    'RealMajoranaBerryKeatingProblem',
    'FockVsMellinNormalizabilityGuard',
    'MajoranaZeroModeNormalizabilityPacket',
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
    stripped = line.strip()
    
    # Check for start of namespace
    if line.startswith('namespace '):
        ns = stripped.split()[1]
        if ns in namespaces_to_delete:
            skip_namespace = True
            continue
    if skip_namespace and line.startswith('end '):
        ns = stripped.split()[1]
        if ns in namespaces_to_delete:
            skip_namespace = False
            continue
    if skip_namespace:
        continue
        
    # Check for Owner Target theorems. They start with /-- ... -/ followed by @[owner_target_tag] theorem ...
    # We can detect `@[owner_target_tag]` and skip until the next empty line.
    if stripped.startswith('/--') and i+4 < len(lines) and '@[owner_target_tag]' in "".join(lines[i:i+6]):
        # actually, it's safer to just skip from docstring if owner_target follows
        pass
    if stripped.startswith('@[owner_target_tag]'):
        skip_owner_target = True
        continue
    if skip_owner_target:
        if stripped == '':
            skip_owner_target = False
        continue
        
    # Field deletion logic
    # If the line contains `_True : Prop := by`, we skip it and the next line (which is `sorry`)
    if stripped.endswith('_True : Prop := by'):
        continue
    if stripped == 'sorry' and i > 0 and lines[i-1].strip().endswith('_True : Prop := by'):
        continue
    # If the line contains `_sorryProof :` we skip it and the next line (which is the body)
    if stripped.endswith('_sorryProof :'):
        continue
    if stripped.endswith('_True') and i > 0 and lines[i-1].strip().endswith('_sorryProof :'):
        continue
    # One line variants
    if stripped.endswith('_True : Prop'):
        continue
    if re.match(r'^[a-zA-Z0-9_]+_True\s*:\s*Prop\s*:=\s*.*$', stripped):
        continue
        
    # implies rules
    if 'implies' in stripped and '_True' in stripped and stripped.endswith(':'):
        continue
    if '_True' in stripped and i > 0 and 'implies' in lines[i-1] and lines[i-1].strip().endswith(':'):
        continue

    # special rules for `normalizable_True : Prop := IsCriticalLineRealPart realPart`
    # the regex above catches it, but let's make sure it caught everything.
    
    # Let's drop comments that precede these deleted fields
    if stripped.startswith('/--') and i+1 < len(lines) and lines[i+1].strip().endswith('_True : Prop := by'):
        continue
    if stripped.startswith('/--') and i+2 < len(lines) and lines[i+2].strip().endswith('_True : Prop := by'):
        # multiline comment... this is getting too complex, let's just let comments sit there
        pass

    new_lines.append(line)

# Let's do a regex pass to clean up floating comments and empty lines
text = "".join(new_lines)
# Remove empty /-- -/ blocks
text = re.sub(r'/\-\-\s*\-/\n', '', text)
text = re.sub(r'/\-\-[^\n]+\-/\n(?=\n)', '\n', text) # drops comment if it's followed by empty line, meaning we deleted what it documented

with open('lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket.lean', 'w') as f:
    f.write(text)
with open('lean/InfoGeometry/Arithmetic/ConcreteMajorana.lean', 'r') as f:
    concrete_text = f.read()

concrete_text = re.sub(r'\s*combinedDirac_formula_True := [^\n]+\n\s*combinedDirac_formula_sorryProof := rfl', '', concrete_text)
concrete_text = re.sub(r'\s*rho_anticommutes_realBK_True := [^\n]+\n\s*rho_anticommutes_realBK_sorryProof := rho_anticommutes_bk', '', concrete_text)
concrete_text = re.sub(r'\s*majoranaDirac_square_True :=\s*\n\s*[^\n]+\n\s*majoranaDirac_square_sorryProof := by simp', '', concrete_text)
concrete_text = re.sub(r'\s*combinedDirac_square_True := [^\n]+\n\s*combinedDirac_square_sorryProof := combined_dirac_sq', '', concrete_text)
concrete_text = re.sub(r'\s*modeEnergyCoefficient_sqrtLog_True := [^\n]+\n\s*modeEnergyCoefficient_sqrtLog_sorryProof := by\n\s*intro _\n\s*rfl', '', concrete_text)

with open('lean/InfoGeometry/Arithmetic/ConcreteMajorana.lean', 'w') as f:
    f.write(concrete_text)
