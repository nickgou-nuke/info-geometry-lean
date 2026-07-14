import re

with open("lean/InfoGeometry/Canonical/IntegralZornAlternativeAlgebra.lean", "r") as f:
    text = f.read()

text = text.replace(
"""  rw [integralToCoreZorn_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul,
      integralToCoreZorn_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul,
      integralToCoreZorn_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul,
      integralToCoreZorn_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]""",
"""  simp only [integralToCoreZorn_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]"""
)

text = text.replace(
"""  rw [integralToCoreZorn_conj, CanonicalZornProjectiveTKKBridge.coreToCanonical_conj,
      integralToCoreZorn_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul,
      integralToCoreZorn_conj, CanonicalZornProjectiveTKKBridge.coreToCanonical_conj,
      integralToCoreZorn_conj, CanonicalZornProjectiveTKKBridge.coreToCanonical_conj]""",
"""  simp only [integralToCoreZorn_conj, CanonicalZornProjectiveTKKBridge.coreToCanonical_conj,
      integralToCoreZorn_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]"""
)

with open("lean/InfoGeometry/Canonical/IntegralZornAlternativeAlgebra.lean", "w") as f:
    f.write(text)
