import re

with open("lean/InfoGeometry/Canonical/IntegralZornAlternativeAlgebra.lean", "r") as f:
    text = f.read()

text = text.replace(
"""  have h := canonicalZorn_left_alternative (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X))
    (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y))
  repeat rw [← CanonicalZornProjectiveTKKBridge.coreToCanonical_mul] at h
  repeat rw [← integralToCoreZorn_mul] at h
  exact h""",
"""  have h1 : CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn (integralZornMul (integralZornMul X X) Y)) =
    zornMul (zornMul (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X)) (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X))) (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y)) := by
    rw [integralToCoreZorn_mul, integralToCoreZorn_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]
  have h2 : CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn (integralZornMul X (integralZornMul X Y))) =
    zornMul (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X)) (zornMul (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X)) (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y))) := by
    rw [integralToCoreZorn_mul, integralToCoreZorn_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]
  rw [h1, h2]
  exact canonicalZorn_left_alternative (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X))
    (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y))"""
)

text = text.replace(
"""  have h := canonicalZorn_right_alternative (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X))
    (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y))
  repeat rw [← CanonicalZornProjectiveTKKBridge.coreToCanonical_mul] at h
  repeat rw [← integralToCoreZorn_mul] at h
  exact h""",
"""  have h1 : CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn (integralZornMul (integralZornMul X Y) Y)) =
    zornMul (zornMul (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X)) (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y))) (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y)) := by
    rw [integralToCoreZorn_mul, integralToCoreZorn_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]
  have h2 : CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn (integralZornMul X (integralZornMul Y Y))) =
    zornMul (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X)) (zornMul (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y)) (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y))) := by
    rw [integralToCoreZorn_mul, integralToCoreZorn_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]
  rw [h1, h2]
  exact canonicalZorn_right_alternative (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X))
    (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y))"""
)

text = text.replace(
"""  have h := canonicalZorn_conj_mul (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X))
    (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y))
  repeat rw [← CanonicalZornProjectiveTKKBridge.coreToCanonical_mul] at h
  repeat rw [← CanonicalZornProjectiveTKKBridge.coreToCanonical_conj] at h
  repeat rw [← integralToCoreZorn_mul] at h
  repeat rw [← integralToCoreZorn_conj] at h
  exact h""",
"""  have h1 : CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn (integralZornConj (integralZornMul X Y))) =
    zornConj (zornMul (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X)) (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y))) := by
    rw [integralToCoreZorn_conj, integralToCoreZorn_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_conj, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]
  have h2 : CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn (integralZornMul (integralZornConj Y) (integralZornConj X))) =
    zornMul (zornConj (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y))) (zornConj (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X))) := by
    rw [integralToCoreZorn_mul, integralToCoreZorn_conj, integralToCoreZorn_conj, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_conj, CanonicalZornProjectiveTKKBridge.coreToCanonical_conj]
  rw [h1, h2]
  exact canonicalZorn_conj_mul (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X))
    (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y))"""
)

with open("lean/InfoGeometry/Canonical/IntegralZornAlternativeAlgebra.lean", "w") as f:
    f.write(text)
