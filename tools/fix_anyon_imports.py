import os
import glob

anyon_dir = "lean/InfoGeometry/Algebra/AnyonFiniteSpinBraid"
files = glob.glob(os.path.join(anyon_dir, "*.lean"))

for f in files:
    with open(f, "r") as fh:
        content = fh.read()
        
    content = content.replace("import InfoGeometry.Algebra.FiniteSpin\n", "import InfoGeometry.Algebra.FiniteSpinAlgebra\n")
    content = content.replace("import InfoGeometry.Algebra.FiniteSUSY\n", "import InfoGeometry.Algebra.FiniteSUSYBlocks\n")
    
    with open(f, "w") as fh:
        fh.write(content)

print("Fixed Anyon imports.")
