import re

with open('/home/goutev/repos/info-geometry-lean/sandbox/MajoranaPolyaHilbertSocket2.lean', 'r') as f:
    text = f.read()

# 1. Clean up `Prop := by sorry` left over from bad refactoring
text = re.sub(r':\s*Prop\s*:=\s*by\s*\n\s*sorry', ': Prop', text)

# 2. Fix the mkDummy block for CompletedXiHilbertPolyaReduction
bad_mk1 = """  def mkDummy : CompletedXiHilbertPolyaReduction Unit Unit Unit Unit where
    classicalRHStatement := False
    operator := sorry
    height := sorry
    completedXiAtHeight := sorry
    renormalizedPfaffianAtHeight := sorry
    spectralKernelAtHeight := sorry
    self_adjoint_Prop := False
    renormalizedPfaffian_eq_completedXi_Prop := False
    renormalizedPfaffian_eq_completedXi_law := sorry
    completedXiZero_Prop := False
    completedXiZero_iff_spectralKernel_law := sorry
    spectralHeight_real_Prop := False
    spectralHeight_real_law := sorry
    spectralZero_on_criticalLine_Prop := False
    criticalLine_completedXiZeros_imply_RH_Prop := False
    IsCriticalLineRealPart (1 / 2 := sorry
    no_RH_without_completedXi_spectral_identity_guard := sorry"""

good_mk1 = """  def mkDummy : CompletedXiHilbertPolyaReduction Unit Unit Unit Unit where
    classicalRHStatement := False
    operator := sorry
    height := 0
    completedXiAtHeight := sorry
    renormalizedPfaffianAtHeight := sorry
    spectralKernelAtHeight := sorry
    self_adjoint_Prop := False
    self_adjoint_law := sorry
    renormalizedPfaffian_eq_completedXi_Prop := False
    renormalizedPfaffian_eq_completedXi_law := sorry
    completedXiZero_Prop := False
    completedXiZero_iff_spectralKernel_law := sorry
    spectralHeight_real_Prop := False
    spectralHeight_real_law := sorry
    spectralZero_on_criticalLine_Prop := by rfl
    criticalLine_completedXiZeros_imply_RH_Prop := sorry
    no_RH_without_completedXi_spectral_identity_guard := sorry"""

if bad_mk1 in text:
    text = text.replace(bad_mk1, good_mk1)
else:
    # Use regex to find and replace the mkDummy for CompletedXiHilbertPolyaReduction
    mk_pattern = re.compile(r'def mkDummy : CompletedXiHilbertPolyaReduction[^m]*mkDummy', re.MULTILINE | re.DOTALL)
    # We'll just replace the lines
    pass # we'll do it manually below

# Alternatively, just search and replace the specific bad lines
text = text.replace('IsCriticalLineRealPart (1 / 2 := sorry', 'spectralZero_on_criticalLine_Prop := by rfl')
text = text.replace('criticalLine_completedXiZeros_imply_RH_Prop := False', 'criticalLine_completedXiZeros_imply_RH_Prop := sorry')
text = text.replace('self_adjoint_Prop := False\n    renormalizedPfaffian_eq_completedXi_Prop', 'self_adjoint_Prop := False\n    self_adjoint_law := sorry\n    renormalizedPfaffian_eq_completedXi_Prop')


# 3. Fix mkDummy for MajoranaPolyaHilbertBridge
text = text.replace('criticalLine_implies_classicalRH_Prop := False', 'criticalLine_implies_classicalRH_Prop := sorry')

# Check other ones that might be wrong
text = text.replace('all_three_fronts_closed_Prop := False\n    all_three_fronts_closed_law := sorry', 'all_three_fronts_closed_Prop := False\n    all_three_fronts_closed_law := sorry')

# 4. Check for any missing `self_adjoint_law` in CompletedXiHilbertPolyaReduction structure definition
if 'self_adjoint_law : self_adjoint_Prop' not in text:
    text = text.replace('self_adjoint_Prop : Prop', 'self_adjoint_Prop : Prop\n  self_adjoint_law : self_adjoint_Prop')


with open('/home/goutev/repos/info-geometry-lean/sandbox/MajoranaPolyaHilbertSocket.lean', 'w') as f:
    f.write(text)

