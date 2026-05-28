import re

files_to_patch = [
    "lean/InfoGeometry/GromovWittenErlangen/CP1DrazinModel.lean",
    "lean/InfoGeometry/GromovWittenErlangen/CP1DrazinNilpotentDefectModel.lean",
    "lean/InfoGeometry/GromovWittenErlangen/CP1DrazinNilpotentCountRayExample.lean",
]

for file_path in files_to_patch:
    with open(file_path, "r") as f:
        content = f.read()

    # SelfAdjointIdempotentPair
    content = re.sub(
        r"  selfAdjointLaw := (.*)\n  selfAdjointCertificate := (.*)",
        r"  support_selfAdjoint := by sorry\n  residue_selfAdjoint := by sorry",
        content,
        flags=re.MULTILINE
    )

    # RelativeCoreNilpotentDecomposition
    content = re.sub(
        r"  nilpotentResidueLaw := (.*)\n  nilpotentResidueCertificate := (.*)",
        r"  nilpotent_isNilpotent := by sorry",
        content,
        flags=re.MULTILINE
    )

    # DivisionResidueBlockPacket
    content = re.sub(
        r"  simpleResidueLaw := Nonempty Unit\n  simpleResidueCertificate := ⟨\(\)⟩",
        r"  carrier_divisionRing := by sorry",
        content,
        flags=re.MULTILINE
    )

    # FrobeniusSelfDualPacket
    content = re.sub(
        r"  nondegeneracyLaw := (.*)\n  nondegeneracyCertificate := (.*)",
        r"  nondegenerate := by sorry",
        content,
        flags=re.MULTILINE
    )

    with open(file_path, "w") as f:
        f.write(content)

    print(f"Patched {file_path}")
