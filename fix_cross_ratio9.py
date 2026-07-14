with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "r") as f:
    content = f.read()

import re

# We want to replace the `hd` pos branch
replacement1 = """        constructor
        · exact one_div_ne_zero ha
        · constructor
          · field_simp; ring
          · change (0 : ℂ) = 1 / (M.a * z' + M.b) * (M.c * z' + M.d * 1)
            have h_zero : M.c * z' + M.d * 1 = 0 := by
              calc M.c * z' + M.d * 1 = M.c * z' + M.d := by ring
                                      _ = 0 := hd
            rw [h_zero, mul_zero]"""

# Find the exact block we modified last time
match1 = re.search(r"        constructor\n        · exact one_div_ne_zero ha\n        · have h1.*?          exact ⟨h1, h2⟩", content, re.DOTALL)
if match1:
    content = content[:match1.start()] + replacement1 + content[match1.end():]

# We want to replace the `hd` neg branch
replacement2 = """        constructor
        · exact one_div_ne_zero hd
        · constructor
          · field_simp; ring
          · field_simp; ring"""

match2 = re.search(r"        constructor\n        · exact one_div_ne_zero hd\n        · have h1.*?          exact ⟨h1, h2⟩", content, re.DOTALL)
if match2:
    content = content[:match2.start()] + replacement2 + content[match2.end():]

with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "w") as f:
    f.write(content)
