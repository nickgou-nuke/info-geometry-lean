import re

with open("lean/InfoGeometry/Canonical/IntegralZornAlternativeAlgebra.lean", "r") as f:
    text = f.read()

text = text.replace(
"""  repeat rw [integralToCoreZorn_mul]
  repeat rw [CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]
  exact canonicalZorn_left_alternative (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X))
    (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y))""",
"""  have h := canonicalZorn_left_alternative (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X))
    (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y))
  repeat rw [← CanonicalZornProjectiveTKKBridge.coreToCanonical_mul] at h
  repeat rw [← integralToCoreZorn_mul] at h
  exact h"""
)

text = text.replace(
"""  repeat rw [integralToCoreZorn_mul]
  repeat rw [CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]
  exact canonicalZorn_right_alternative (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X))
    (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y))""",
"""  have h := canonicalZorn_right_alternative (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X))
    (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y))
  repeat rw [← CanonicalZornProjectiveTKKBridge.coreToCanonical_mul] at h
  repeat rw [← integralToCoreZorn_mul] at h
  exact h"""
)

text = text.replace(
"""  repeat rw [integralToCoreZorn_conj]
  repeat rw [integralToCoreZorn_mul]
  repeat rw [CanonicalZornProjectiveTKKBridge.coreToCanonical_conj]
  repeat rw [CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]
  exact canonicalZorn_conj_mul (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X))
    (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y))""",
"""  have h := canonicalZorn_conj_mul (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X))
    (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y))
  repeat rw [← CanonicalZornProjectiveTKKBridge.coreToCanonical_mul] at h
  repeat rw [← CanonicalZornProjectiveTKKBridge.coreToCanonical_conj] at h
  repeat rw [← integralToCoreZorn_mul] at h
  repeat rw [← integralToCoreZorn_conj] at h
  exact h"""
)

with open("lean/InfoGeometry/Canonical/IntegralZornAlternativeAlgebra.lean", "w") as f:
    f.write(text)
