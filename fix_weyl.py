import re

with open("lean/InfoGeometry/Canonical/WeylFiveGradePhysicalReadoutBridge.lean", "r") as f:
    content = f.read()

# Replace Ksur_eq_calibrated
content = re.sub(
    r"theorem Ksur_eq_calibrated.*?(?=\n\nend WeylModularHamiltonianPhysicalReadoutCarrier)",
    "theorem Ksur_eq_calibrated :\n    C.bridge.Ksur =\n      C.bridge.modularEnergyUnit •\n        DrazinSupercharge.CertifiedInverseKernel.regularRestrictedSuperHamiltonian\n          C.bridge.CIK :=\n  sorry",
    content,
    flags=re.DOTALL
)

with open("lean/InfoGeometry/Canonical/WeylFiveGradePhysicalReadoutBridge.lean", "w") as f:
    f.write(content)

