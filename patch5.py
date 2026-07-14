import re

with open("lean/InfoGeometry/Canonical/IntegralZornAlternativeAlgebra.lean", "r") as f:
    text = f.read()

text = text.replace(
"""  simp only [integralToCoreZorn_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]
  exact canonicalZorn_left_alternative (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X))
    (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y))""",
"""  rw [integralToCoreZorn_mul]
  rw [integralToCoreZorn_mul]
  rw [integralToCoreZorn_mul]
  rw [CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]
  rw [CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]
  exact canonicalZorn_left_alternative (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X))
    (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y))"""
)

text = text.replace(
"""  simp only [integralToCoreZorn_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]
  exact canonicalZorn_right_alternative (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X))
    (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y))""",
"""  rw [integralToCoreZorn_mul]
  rw [integralToCoreZorn_mul]
  rw [integralToCoreZorn_mul]
  rw [CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]
  rw [CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]
  exact canonicalZorn_right_alternative (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X))
    (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y))"""
)

text = text.replace(
"""  simp only [integralToCoreZorn_conj, CanonicalZornProjectiveTKKBridge.coreToCanonical_conj,
      integralToCoreZorn_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]
  exact canonicalZorn_conj_mul (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X))
    (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y))""",
"""  rw [integralToCoreZorn_conj]
  rw [integralToCoreZorn_conj]
  rw [integralToCoreZorn_conj]
  rw [integralToCoreZorn_mul]
  rw [CanonicalZornProjectiveTKKBridge.coreToCanonical_conj]
  rw [CanonicalZornProjectiveTKKBridge.coreToCanonical_conj]
  rw [CanonicalZornProjectiveTKKBridge.coreToCanonical_conj]
  rw [CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]
  exact canonicalZorn_conj_mul (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X))
    (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y))"""
)

with open("lean/InfoGeometry/Canonical/IntegralZornAlternativeAlgebra.lean", "w") as f:
    f.write(text)
