import os
import sys

files_to_refactor = [
    "lean/InfoGeometry/All.lean",
    "lean/InfoGeometry/Cartan.lean",
    "lean/InfoGeometry/Convex.lean",
    "lean/InfoGeometry/ExponentialFamily.lean",
    "lean/InfoGeometry/LLM.lean",
    "lean/InfoGeometry/Library.lean",
    "lean/InfoGeometry/MaxEnt.lean",
    "lean/InfoGeometry/OptimalTransport.lean",
    "lean/InfoGeometry/Potential.lean",
    "lean/InfoGeometry/SuperUnified.lean",
    "lean/InfoGeometry/generalizedKL.lean",
    "lean/InfoGeometry/Architecture/All.lean",
    "lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean",
    "lean/InfoGeometry/Canonical/Algebra.lean",
    "lean/InfoGeometry/Canonical/All.lean",
    "lean/InfoGeometry/Canonical/AnalyticalIndex.lean",
    "lean/InfoGeometry/Canonical/CalabiYauBridge.lean",
    "lean/InfoGeometry/Canonical/ChiralTorsionBridge.lean",
    "lean/InfoGeometry/Canonical/Clifford.lean",
    "lean/InfoGeometry/Canonical/ConformalUnification.lean",
    "lean/InfoGeometry/Canonical/ConnesArakiFramework.lean",
    "lean/InfoGeometry/Canonical/CountEmergentFlow.lean",
    "lean/InfoGeometry/Canonical/CountSubstrateBridge.lean",
    "lean/InfoGeometry/Canonical/DrazinAdjoint.lean",
    "lean/InfoGeometry/Canonical/Foundations.lean",
    "lean/InfoGeometry/Canonical/Geometry.lean",
    "lean/InfoGeometry/Canonical/GrandCanonicalCore.lean",
    "lean/InfoGeometry/Canonical/InformationCalculus.lean",
    "lean/InfoGeometry/Canonical/KK.lean",
    "lean/InfoGeometry/Canonical/KKFoundation.lean",
    "lean/InfoGeometry/Canonical/KMSSinkhornBridge.lean",
    "lean/InfoGeometry/Canonical/Krein.lean",
    "lean/InfoGeometry/Canonical/KreinNaturalFlow.lean",
    "lean/InfoGeometry/Canonical/MoorePenroseAdjoint.lean",
    "lean/InfoGeometry/Canonical/OperatorAlgebraBridge.lean",
    "lean/InfoGeometry/Canonical/PerelmanW.lean",
    "lean/InfoGeometry/Canonical/Prequantum.lean",
    "lean/InfoGeometry/Canonical/Quantum.lean",
    "lean/InfoGeometry/Canonical/Statistics.lean",
    "lean/InfoGeometry/Canonical/Thermo.lean",
    "lean/InfoGeometry/Canonical/Twistor.lean",
    "lean/InfoGeometry/Canonical/WeylInformationGauge.lean",
    "lean/InfoGeometry/Canonical/YangMillsFinite.lean",
    "lean/InfoGeometry/Causal/All.lean",
    "lean/InfoGeometry/Clifford/All.lean",
    "lean/InfoGeometry/Clifford/Supercharge.lean",
    "lean/InfoGeometry/Convex/All.lean",
    "lean/InfoGeometry/Core/All.lean",
    "lean/InfoGeometry/Core/Derivatives.lean",
    "lean/InfoGeometry/ExponentialFamily/All.lean",
    "lean/InfoGeometry/Jordan/All.lean",
    "lean/InfoGeometry/KK/All.lean",
    "lean/InfoGeometry/Krein/All.lean",
    "lean/InfoGeometry/Krein/Dilation.lean",
    "lean/InfoGeometry/Krein/Grading.lean",
    "lean/InfoGeometry/MaxEnt/All.lean",
    "lean/InfoGeometry/MaxEnt/JaynesInfoStatMechTest.lean",
    "lean/InfoGeometry/Measure/All.lean",
    "lean/InfoGeometry/MeasureProjective/All.lean",
    "lean/InfoGeometry/Prequantum/All.lean",
    "lean/InfoGeometry/Projective/All.lean",
    "lean/InfoGeometry/Quantum/All.lean",
    "lean/InfoGeometry/Singular/All.lean",
    "lean/InfoGeometry/Thermo/All.lean",
    "lean/InfoGeometry/Unstable/Quarantine.lean",
    "lean/InfoGeometry/Volume/All.lean"
]

def refactor_file(file_path):
    if not os.path.exists(file_path):
        print(f"Skipping {file_path}: File not found")
        return

    with open(file_path, 'r') as f:
        lines = f.readlines()

    # Skip if file is clearly an entry point like Audit.lean (not in list anyway)
    if "Audit.lean" in file_path:
        print(f"Skipping {file_path}: Audit.lean")
        return

    # Skip if already has namespace
    has_namespace = any(line.strip().startswith("namespace ") for line in lines)
    if has_namespace:
        print(f"Skipping {file_path}: Already has namespace")
        return

    last_import_idx = -1
    for i, line in enumerate(lines):
        if line.startswith("import "):
            last_import_idx = i

    if last_import_idx == -1:
        print(f"No imports found in {file_path}. Inserting at top.")
        # Insert at the beginning, but after any comments if present (skipped for now, following instructions)
        lines.insert(0, "\nnamespace InfoGeometry\n\n")
    else:
        # Insert after last import
        lines.insert(last_import_idx + 1, "\nnamespace InfoGeometry\n")

    # Ensure there's a newline at the end of the file before appending
    if lines and not lines[-1].endswith('\n'):
        lines[-1] = lines[-1] + '\n'
    
    lines.append("\nend InfoGeometry\n")

    with open(file_path, 'w') as f:
        f.writelines(lines)
    print(f"Refactored {file_path}")

for f in files_to_refactor:
    refactor_file(f)
