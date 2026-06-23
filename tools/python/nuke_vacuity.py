import re

with open('lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket.lean', 'r') as f:
    lines = f.readlines()

new_lines = []
skip_namespace = False

# We want to delete all re-export namespaces entirely.
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
    # Namespace deletion
    if line.startswith('namespace '):
        ns = line.strip().split()[1]
        if ns in namespaces_to_delete:
            skip_namespace = True
            continue
    if skip_namespace and line.startswith('end '):
        ns = line.strip().split()[1]
        if ns in namespaces_to_delete:
            skip_namespace = False
            continue
    if skip_namespace:
        continue

    # Owner target theorems
    if line.strip().startswith('@[owner_target_tag]'):
        # this is MBKAnalyticFrontierOwnerTarget, we skip it completely
        skip_namespace = True
        continue

    # Structure fields deletion
    stripped = line.strip()
    if stripped.endswith('_True : Prop := by') or stripped.endswith('_sorryProof :') or stripped.endswith('_True : Prop'):
        continue
    if stripped == 'sorry' and i > 0 and 'Prop := by' in lines[i-1]:
        continue
    if stripped.endswith('_True') and i > 0 and '_sorryProof :' in lines[i-1]:
        continue
    if re.match(r'^[a-zA-Z0-9_]+_True\s*:\s*Prop\s*:=\s*.*$', stripped):
        continue
    if re.match(r'^[a-zA-Z0-9_]+_sorryProof\s*:\s*[a-zA-Z0-9_]+_True\s*:=\s*.*$', stripped):
        continue
    if re.match(r'^[a-zA-Z0-9_]+_sorryProof\s*:=\s*.*$', stripped):
        continue
    if re.match(r'^[a-zA-Z0-9_]+_True\s*:=\s*.*$', stripped):
        continue

    # Guardrails like:
    #   normalizable_sorryProof : normalizable_True := by rfl
    
    new_lines.append(line)

# Now, we also need to clean up `ConcreteMajorana.lean`
with open('lean/InfoGeometry/Arithmetic/ConcreteMajorana.lean', 'r') as f:
    concrete_lines = f.readlines()

new_concrete = []
for line in concrete_lines:
    stripped = line.strip()
    if stripped.startswith('combinedDirac_formula_True') or stripped.startswith('combinedDirac_formula_sorryProof') \
        or stripped.startswith('rho_anticommutes_realBK_True') or stripped.startswith('rho_anticommutes_realBK_sorryProof') \
        or stripped.startswith('majoranaDirac_square_True') or stripped.startswith('majoranaDirac_square_sorryProof') \
        or stripped.startswith('combinedDirac_square_True') or stripped.startswith('combinedDirac_square_sorryProof') \
        or stripped.startswith('modeEnergyCoefficient_sqrtLog_True') or stripped.startswith('modeEnergyCoefficient_sqrtLog_sorryProof') \
        or stripped.startswith('intro _'):
        continue
    if stripped == 'rfl' and new_concrete[-1].strip().startswith('modeEnergyCoefficient_sqrtLog_sorryProof'):
        continue
    if stripped == 'rfl' and new_concrete[-1].strip().startswith('intro _'):
        # Already skipped intro
        continue
    # we need to be careful not to drop `rfl` from other theorems
    # Wait, in the snippet, `modeEnergyCoefficient_sqrtLog_sorryProof := by\n    intro _\n    rfl`
    # We can just skip `intro _` and `rfl` if we are inside the `NativeMajoranaClifford` definition.
    if stripped == 'rfl' and len(new_concrete) > 0 and 'by' in new_concrete[-1]:
        # Actually just skip it manually
        pass
        
    new_concrete.append(line)

# Let's do a safer regex replacement for ConcreteMajorana
concrete_text = "".join(concrete_lines)
concrete_text = re.sub(r'\s*combinedDirac_formula_True := [^\n]+\n\s*combinedDirac_formula_sorryProof := rfl', '', concrete_text)
concrete_text = re.sub(r'\s*rho_anticommutes_realBK_True := [^\n]+\n\s*rho_anticommutes_realBK_sorryProof := rho_anticommutes_bk', '', concrete_text)
concrete_text = re.sub(r'\s*majoranaDirac_square_True :=\s*\n\s*[^\n]+\n\s*majoranaDirac_square_sorryProof := by simp', '', concrete_text)
concrete_text = re.sub(r'\s*combinedDirac_square_True := [^\n]+\n\s*combinedDirac_square_sorryProof := combined_dirac_sq', '', concrete_text)
concrete_text = re.sub(r'\s*modeEnergyCoefficient_sqrtLog_True := [^\n]+\n\s*modeEnergyCoefficient_sqrtLog_sorryProof := by\n\s*intro _\n\s*rfl', '', concrete_text)


with open('lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket.lean', 'w') as f:
    f.writelines(new_lines)

with open('lean/InfoGeometry/Arithmetic/ConcreteMajorana.lean', 'w') as f:
    f.write(concrete_text)

