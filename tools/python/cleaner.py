import re

with open('lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket.lean', 'r') as f:
    text = f.read()

# 1. Remove all namespace ... end ... blocks EXCEPT `namespace InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket`
# We can do this by finding `namespace X` where X is not the main one, up to `end X`.
namespaces = [
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
]

for ns in namespaces:
    text = re.sub(r'namespace ' + ns + r'\b.*?end ' + ns + r'\b', '', text, flags=re.DOTALL)

# 2. Remove any @[owner_target_tag] theorem ...
text = re.sub(r'(/--[^\n]*\n)*@\[owner_target_tag\]\ntheorem.*?(?=\n\n|\Z)', '', text, flags=re.DOTALL)

# 3. Remove fields ending with `_True` or `_sorryProof` from structures.
# Example:
#   splitClifford_True : Prop := by
#     sorry
# We remove lines that match `\s+[a-zA-Z0-9_]+_True\s*:.*?`
# But wait, some are `Prop := by sorry`, some are `Prop := IsCriticalLineRealPart realPart`.
# We want to remove the field entirely.
# A field declaration is usually `  name : type` or `  name : type := val`.
text = re.sub(r'^\s*[a-zA-Z0-9_]+_True\s*:.*?(\n\s+sorry)?\n', '', text, flags=re.MULTILINE)
text = re.sub(r'^\s*[a-zA-Z0-9_]+_sorryProof\s*:.*?\n', '', text, flags=re.MULTILINE)
# also remove things like `  normalizable_iff_criticalLine_sorryProof : ... := by rfl`
text = re.sub(r'^\s*[a-zA-Z0-9_]+_sorryProof\s*:=.*?\n', '', text, flags=re.MULTILINE)
text = re.sub(r'^\s*[a-zA-Z0-9_]+_True := by rfl\n', '', text, flags=re.MULTILINE)

# 4. In `MellinPlancherelCriticalLinePacket` and `MajoranaZeroModeNormalizabilityPacket`, there are fields like:
#   bk_generalizedEigenvalue_True := by rfl
text = re.sub(r'^\s*[a-zA-Z0-9_]+_True := by rfl\n', '', text, flags=re.MULTILINE)

# 5. Handle `zeta_zero_is_inverseZeta_pole_guard : Type*`
# We'll keep guard fields.

# 6. Some lines might have been missed if they span multiple lines. For example:
#   completedZeta_factorization_sorryProof :
#     completedZeta_factorization_True
text = re.sub(r'^\s+[a-zA-Z0-9_]+_sorryProof :\s*\n\s+[a-zA-Z0-9_]+_True\n', '', text, flags=re.MULTILINE)
text = re.sub(r'^\s+[a-zA-Z0-9_]+_implies_[a-zA-Z0-9_]+\s*:\s*\n\s+[a-zA-Z0-9_]+_True → [a-zA-Z0-9_]+_True\n', '', text, flags=re.MULTILINE)
text = re.sub(r'^\s*[a-zA-Z0-9_]+_implies_[a-zA-Z0-9_]+\s*:\s*[^\n]+\n', '', text, flags=re.MULTILINE)


# Finally, write it back
with open('lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket.lean', 'w') as f:
    f.write(text)
