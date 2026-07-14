import re

with open("lean/InfoGeometry/Canonical/IntegralZornAlternativeAlgebra.lean", "r") as f:
    text = f.read()

text = text.replace(
"""  have h :=
    (canonicalZorn_left_alternative
        (CanonicalZornProjectiveTKKBridge.coreToCanonical
          (integralToCoreZorn X))
        (CanonicalZornProjectiveTKKBridge.coreToCanonical
          (integralToCoreZorn Y)))
  simpa [IntegralZornCompositionAlgebra.integralToCoreZorn_mul,
    CanonicalZornProjectiveTKKBridge.coreToCanonical_mul] using h""",
"""  rw [integralToCoreZorn_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul,
      integralToCoreZorn_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul,
      integralToCoreZorn_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul,
      integralToCoreZorn_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]
  exact canonicalZorn_left_alternative (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X))
    (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y))"""
)

text = text.replace(
"""  have h :=
    (canonicalZorn_right_alternative
        (CanonicalZornProjectiveTKKBridge.coreToCanonical
          (integralToCoreZorn X))
        (CanonicalZornProjectiveTKKBridge.coreToCanonical
          (integralToCoreZorn Y)))
  simpa [IntegralZornCompositionAlgebra.integralToCoreZorn_mul,
    CanonicalZornProjectiveTKKBridge.coreToCanonical_mul] using h""",
"""  rw [integralToCoreZorn_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul,
      integralToCoreZorn_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul,
      integralToCoreZorn_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul,
      integralToCoreZorn_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]
  exact canonicalZorn_right_alternative (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X))
    (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y))"""
)

text = text.replace(
"""  have h :=
    (canonicalZorn_conj_mul
        (CanonicalZornProjectiveTKKBridge.coreToCanonical
          (integralToCoreZorn X))
        (CanonicalZornProjectiveTKKBridge.coreToCanonical
          (integralToCoreZorn Y)))
  simpa [coreToCanonical_integralZornConj,
    coreToCanonical_integralZornMul,
    CanonicalZornProjectiveTKKBridge.coreToCanonical_mul] using h""",
"""  rw [integralToCoreZorn_conj, CanonicalZornProjectiveTKKBridge.coreToCanonical_conj,
      integralToCoreZorn_mul, CanonicalZornProjectiveTKKBridge.coreToCanonical_mul,
      integralToCoreZorn_conj, CanonicalZornProjectiveTKKBridge.coreToCanonical_conj,
      integralToCoreZorn_conj, CanonicalZornProjectiveTKKBridge.coreToCanonical_conj]
  exact canonicalZorn_conj_mul (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn X))
    (CanonicalZornProjectiveTKKBridge.coreToCanonical (integralToCoreZorn Y))"""
)

with open("lean/InfoGeometry/Canonical/IntegralZornAlternativeAlgebra.lean", "w") as f:
    f.write(text)
