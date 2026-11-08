import re

with open('lean/InfoGeometry/Canonical/DrazinCoreFlow.lean', 'r') as f:
    content = f.read()

content = re.sub(
    r'simpa \[SemiconjBy, Commute\] using\n    \(projection_mul_eq_mul_projection h\)\.symm',
    r'exact (projection_mul_eq_mul_projection h).symm',
    content
)

content = re.sub(
    r'simpa \[CoreInverseKernel\.spectralComplementaryProjector, InverseKernel\.spectralComplementaryProjector\] using hnil',
    r'exact hnil',
    content
)

with open('lean/InfoGeometry/Canonical/DrazinCoreFlow.lean', 'w') as f:
    f.write(content)
