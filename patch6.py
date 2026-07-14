import re

with open("lean/InfoGeometry/Canonical/IntegralZornAlternativeAlgebra.lean", "r") as f:
    text = f.read()

text = text.replace(
"""  rw [integralToCoreZorn_mul]
  rw [integralToCoreZorn_mul]
  rw [integralToCoreZorn_mul]
  rw [CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]
  rw [CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]""",
"""  repeat rw [integralToCoreZorn_mul]
  repeat rw [CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]"""
)

text = text.replace(
"""  rw [integralToCoreZorn_conj]
  rw [integralToCoreZorn_conj]
  rw [integralToCoreZorn_conj]
  rw [integralToCoreZorn_mul]
  rw [CanonicalZornProjectiveTKKBridge.coreToCanonical_conj]
  rw [CanonicalZornProjectiveTKKBridge.coreToCanonical_conj]
  rw [CanonicalZornProjectiveTKKBridge.coreToCanonical_conj]
  rw [CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]""",
"""  repeat rw [integralToCoreZorn_conj]
  repeat rw [integralToCoreZorn_mul]
  repeat rw [CanonicalZornProjectiveTKKBridge.coreToCanonical_conj]
  repeat rw [CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]"""
)

with open("lean/InfoGeometry/Canonical/IntegralZornAlternativeAlgebra.lean", "w") as f:
    f.write(text)
