import re
import sys

def process_file(filepath):
    try:
        with open(filepath, 'r') as f:
            lines = f.readlines()
    except FileNotFoundError:
        return

    new_lines = []
    # State machine or just regex?
    for line in lines:
        if re.search(r'^\s+[a-zA-Z0-9_]+\s*:\s*(Prop|∀.+)\s*$', line):
            # This is a Prop or forall field. Skip it.
            continue
        # Also remove usages of these fields.
        # This might leave trailing commas or broken syntax if we're not careful,
        # but in Lean structures, fields are just separated by newlines.
        
        # We also need to remove defs that use these fields.
        # Let's just comment out the defs that return Prop based on these fields.
        if re.search(r'^\s*∧\s*P\.', line):
            continue
        new_lines.append(line)

    with open(filepath, 'w') as f:
        f.writelines(new_lines)
    print(f"Processed {filepath}")

FILES = [
    "lean/InfoGeometry/Canonical/BulgarianThermodynamicGeometryPacket.lean",
    "lean/InfoGeometry/Canonical/LiteratureGrandCanonicalWeylTKK.lean",
    "lean/InfoGeometry/Canonical/OperatorialCramerRaoStateFirstChunk2.lean",
    "lean/InfoGeometry/Canonical/PedersenTakesakiRNInterface.lean",
    "lean/InfoGeometry/Canonical/PhotonicScatteringParabolicBridge.lean",
    "lean/InfoGeometry/Canonical/TypeIIIContinuousCoreReal.lean",
    "lean/InfoGeometry/Canonical/YangMillsContinuum.lean",
    "lean/InfoGeometry/OperatorAlgebra/SusceptibilityHessian.lean",
    "lean/InfoGeometry/Thermo/SusceptibilityHessian.lean",
]

if __name__ == "__main__":
    for f in FILES:
        process_file(f)
