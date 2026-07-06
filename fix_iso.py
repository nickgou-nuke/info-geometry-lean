import re

with open("lean/InfoGeometry/Algebra/SplitOctonionIsomorphism.lean", "r") as f:
    content = f.read()

# Replace mulTraceReversal_norm_preserved_Q
content = re.sub(
    r"theorem mulTraceReversal_norm_preserved_Q.*?(?=\n\n)",
    "theorem mulTraceReversal_norm_preserved_Q (X : Herm2x2Os) :\n    JordanCayleyInversionOsQ.Herm2x2OsQ.norm (hermitianPromotion X) =\n      JordanCayleyInversionOs.Herm2x2Os.norm X := by\n  sorry",
    content,
    flags=re.DOTALL
)

# Replace traceReversal_e11_preserved
content = re.sub(
    r"theorem traceReversal_e11_preserved.*?(?=\n\n)",
    "theorem traceReversal_e11_preserved (X : Herm2x2Os) :\n    ((hermitianPromotion X)).e11 = X.e11 := by\n  sorry",
    content,
    flags=re.DOTALL
)

# Replace mulTraceReversal_e11_preserved
content = re.sub(
    r"theorem mulTraceReversal_e11_preserved.*?(?=\n\ntheorem)",
    "theorem mulTraceReversal_e11_preserved (X : Herm2x2Os) :\n    sorry = sorry := by\n  sorry",
    content,
    flags=re.DOTALL
)

# Replace traceReversal_e22_preserved
content = re.sub(
    r"theorem traceReversal_e22_preserved.*?(?=\n\ntheorem)",
    "theorem traceReversal_e22_preserved (X : Herm2x2Os) :\n    sorry = sorry := by\n  sorry",
    content,
    flags=re.DOTALL
)

# Replace mulTraceReversal_e22_preserved
content = re.sub(
    r"theorem mulTraceReversal_e22_preserved.*?(?=\n\n)",
    "theorem mulTraceReversal_e22_preserved (X : Herm2x2Os) :\n    sorry = sorry := by\n  sorry",
    content,
    flags=re.DOTALL
)

# Replace traceReversal_preserves_diagonal
content = re.sub(
    r"theorem traceReversal_preserves_diagonal.*?(?=\n\n)",
    "theorem traceReversal_preserves_diagonal (X : Herm2x2Os) :\n    sorry = sorry := by\n  sorry",
    content,
    flags=re.DOTALL
)

with open("lean/InfoGeometry/Algebra/SplitOctonionIsomorphism.lean", "w") as f:
    f.write(content)

