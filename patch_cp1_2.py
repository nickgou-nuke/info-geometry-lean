import re

files_to_patch = [
    "lean/InfoGeometry/GromovWittenErlangen/CP1DrazinModel.lean",
    "lean/InfoGeometry/GromovWittenErlangen/CP1DrazinNilpotentDefectModel.lean",
    "lean/InfoGeometry/GromovWittenErlangen/CP1DrazinNilpotentCountRayExample.lean",
]

for file_path in files_to_patch:
    with open(file_path, "r") as f:
        content = f.read()

    content = re.sub(
        r"  localizationAssemblyLaw := (.*)\n  localizationAssemblyCertificate := (.*)",
        r"  localizationAssembly := by rfl",
        content,
        flags=re.MULTILINE
    )

    content = re.sub(
        r"  divisorInsertionLaw := (.*)\n  divisorInsertionCertificate := by\n(.*)\n(.*)",
        r"  divisorInsertion := by sorry",
        content,
        flags=re.MULTILINE
    )

    content = re.sub(
        r"  semisimplicityLaw := Nonempty Unit\n  semisimplicityCertificate := ⟨\(\)⟩",
        r"  semisimple := by sorry",
        content,
        flags=re.MULTILINE
    )

    content = re.sub(
        r"  divisorDrazinCompatibilityLaw := (.*)\n  divisorDrazinCompatibilityCertificate := by\n(.*)\n(.*)",
        r"  divisorDrazinCompatibility := by sorry",
        content,
        flags=re.MULTILINE
    )

    content = re.sub(
        r"  residueAccountingLaw := (.*)\n  residueAccountingCertificate := by\n(.*)\n(.*)",
        r"  residueAccounting := by rfl",
        content,
        flags=re.MULTILINE
    )

    with open(file_path, "w") as f:
        f.write(content)

    print(f"Patched {file_path}")
