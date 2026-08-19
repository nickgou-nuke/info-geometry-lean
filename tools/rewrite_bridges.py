import os

targets = [
    ("lean/InfoGeometry/Projective/Twistor/Basic.lean", "lean/InfoGeometry/Projective/Twistor/Basic", "InfoGeometry.Projective.Twistor.Basic"),
    ("lean/InfoGeometry/OperatorAlgebra/SusceptibilityHessian.lean", "lean/InfoGeometry/OperatorAlgebra/SusceptibilityHessian", "InfoGeometry.OperatorAlgebra.SusceptibilityHessian"),
    ("lean/InfoGeometry/Quantum/SouriauFoliation.lean", "lean/InfoGeometry/Quantum/SouriauFoliation", "InfoGeometry.Quantum.SouriauFoliation"),
    ("lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbert.lean", "lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbert", "InfoGeometry.Arithmetic.MajoranaPolyaHilbert")
]

for file_path, dir_path, namespace in targets:
    imports = []
    for f in sorted(os.listdir(dir_path)):
        if f.endswith(".lean"):
            module_name = f[:-5]
            imports.append(f"import {namespace}.{module_name}")
            
    with open(file_path, "w") as f:
        f.write("\n".join(imports) + "\n")
        
print("Rewrote 4 bridges.")
