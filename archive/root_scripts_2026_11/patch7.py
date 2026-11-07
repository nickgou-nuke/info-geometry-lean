import re

with open('lean/InfoGeometry/Canonical/SplitOctonionJordanStructure.lean', 'r') as f:
    content = f.read()

old_1 = """noncomputable def structureActionLieSubalgebra :
    LieSubalgebra ℝ (Module.End ℝ Carrier) :="""

new_1 = """local instance : LieRing (Module.End ℝ Carrier) := Ring.lieRing
local instance : LieAlgebra ℝ (Module.End ℝ Carrier) := LieAlgebra.ofAssociativeAlgebra

noncomputable def structureActionLieSubalgebra :
    LieSubalgebra ℝ (Module.End ℝ Carrier) :="""

if old_1 in content:
    content = content.replace(old_1, new_1)
    print("Patched 1")
else:
    print("Failed to patch 1")

with open('lean/InfoGeometry/Canonical/SplitOctonionJordanStructure.lean', 'w') as f:
    f.write(content)
