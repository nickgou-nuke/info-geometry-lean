import re

with open('lean/InfoGeometry/Canonical/EPAndGroupInverse.lean', 'r') as f:
    content = f.read()

content = content.replace(
    'simpa [InverseKernel.IsEP, InverseKernel.mpRangeProjector, InverseKernel.metricProjector] using hEP',
    'exact IK.isEP_iff_comm.mp hEP'
)

with open('lean/InfoGeometry/Canonical/EPAndGroupInverse.lean', 'w') as f:
    f.write(content)
