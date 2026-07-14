import re

with open("lean/InfoGeometry/Canonical/IntegralZornAlternativeAlgebra.lean", "r") as f:
    text = f.read()

text = text.replace(
"""  have hXXY := IntegralZornCompositionAlgebra.integralToCoreZorn_mul
    (integralZornMul X X) Y
  have hX_XY := IntegralZornCompositionAlgebra.integralToCoreZorn_mul
    X (integralZornMul X Y)
  rw [hXXY, hX_XY,
    InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical_mul,
    InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]
  exact canonicalZorn_left_alternative
    (InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical
      (integralToCoreZorn X))
    (InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical
      (integralToCoreZorn Y))""",
"""  have hXXY := IntegralZornCompositionAlgebra.integralToCoreZorn_mul
    (integralZornMul X X) Y
  have hX_XY := IntegralZornCompositionAlgebra.integralToCoreZorn_mul
    X (integralZornMul X Y)
  have hXX := IntegralZornCompositionAlgebra.integralToCoreZorn_mul X X
  have hXY := IntegralZornCompositionAlgebra.integralToCoreZorn_mul X Y
  rw [hXXY, hX_XY,
    hXX, hXY,
    InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical_mul,
    InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical_mul,
    InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical_mul,
    InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]
  exact canonicalZorn_left_alternative
    (InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical
      (integralToCoreZorn X))
    (InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical
      (integralToCoreZorn Y))"""
)

text = text.replace(
"""  have hXY_Y := IntegralZornCompositionAlgebra.integralToCoreZorn_mul
    (integralZornMul X Y) Y
  have hX_YY := IntegralZornCompositionAlgebra.integralToCoreZorn_mul
    X (integralZornMul Y Y)
  rw [hXY_Y, hX_YY,
    InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical_mul,
    InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]
  exact canonicalZorn_right_alternative
    (InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical
      (integralToCoreZorn X))
    (InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical
      (integralToCoreZorn Y))""",
"""  have hXY_Y := IntegralZornCompositionAlgebra.integralToCoreZorn_mul
    (integralZornMul X Y) Y
  have hX_YY := IntegralZornCompositionAlgebra.integralToCoreZorn_mul
    X (integralZornMul Y Y)
  have hXY := IntegralZornCompositionAlgebra.integralToCoreZorn_mul X Y
  have hYY := IntegralZornCompositionAlgebra.integralToCoreZorn_mul Y Y
  rw [hXY_Y, hX_YY,
    hXY, hYY,
    InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical_mul,
    InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical_mul,
    InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical_mul,
    InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical_mul]
  exact canonicalZorn_right_alternative
    (InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical
      (integralToCoreZorn X))
    (InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge.coreToCanonical
      (integralToCoreZorn Y))"""
)

with open("lean/InfoGeometry/Canonical/IntegralZornAlternativeAlgebra.lean", "w") as f:
    f.write(text)
