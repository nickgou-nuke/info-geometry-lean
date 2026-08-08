import os
for file in ["proofs/test_zeta.lean", "proofs/Seed.lean"]:
    if os.path.exists(file):
        with open(file, "r") as f:
            text = f.read()
        text = text.replace("import Mathlib.NumberTheory.ZetaFunction", "import Mathlib")
        text = text.replace("import Mathlib.CategoryTheory.Limits.FilteredColimits", "import Mathlib")
        text = text.replace("import Mathlib.CategoryTheory.Filtered", "import Mathlib")
        with open(file, "w") as f:
            f.write(text)
