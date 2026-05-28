import re

with open("lean/InfoGeometry/OperatorAlgebra/DrazinProjectionLocalization.lean", "r") as f:
    content = f.read()

content = content.replace(
    "end TwoProjectionDrazinLocalizationPacket\n\n/-- The packet exposes Drazin inverse data for its decomposition element. -/\ndef drazinData : DrazinInverseData A :=\n  P.decomposition.toDrazinInverseData\n\nend TwoProjectionDrazinLocalizationPacket",
    "/-- The packet exposes Drazin inverse data for its decomposition element. -/\ndef drazinData : DrazinInverseData A :=\n  P.decomposition.toDrazinInverseData\n\nend TwoProjectionDrazinLocalizationPacket"
)

with open("lean/InfoGeometry/OperatorAlgebra/DrazinProjectionLocalization.lean", "w") as f:
    f.write(content)

print("Fixed end")
