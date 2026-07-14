import os

target_dirs = [
    "lean/InfoGeometry/Arithmetic/PrimeSpinorWittenIndex",
    "lean/InfoGeometry/Canonical/CantorCoadjointHamiltonianFlowBridge",
    "lean/InfoGeometry/OperatorAlgebra/OperatorialJonesCalculus"
]

for d in target_dirs:
    for root, _, files in os.walk(d):
        for file in files:
            if file.endswith(".lean"):
                path = os.path.join(root, file)
                with open(path, "r") as f:
                    content = f.read()
                if "Type*" in content and "import Mathlib" not in content:
                    # just insert import Mathlib at the top
                    content = "import Mathlib\n" + content
                    with open(path, "w") as f:
                        f.write(content)
                    print(f"Added import Mathlib to {path}")
