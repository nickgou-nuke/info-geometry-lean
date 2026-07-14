with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "r") as f:
    content = f.read()

replacement = """        constructor
        · exact one_div_ne_zero ha
        · constructor
          · field_simp; ring
          · have h_zero : M.c * z' + M.d * 1 = 0 := by
              calc M.c * z' + M.d * 1 = M.c * z' + M.d := by ring
                                      _ = 0 := hd
            have h_rhs : 1 / (M.a * z' + M.b) * (M.c * z' + M.d * 1) = 0 := by
              rw [h_zero, mul_zero]
            rw [h_rhs]
            rfl"""

import re
# Find the exact block we modified last time
match = re.search(r"        constructor\n        · exact one_div_ne_zero ha\n        · have h1.*?      · rw \[if_neg hd\]", content, re.DOTALL)
if match:
    content = content[:match.start()] + replacement + "\n      · rw [if_neg hd]" + content[match.end():]

# Also fix the "No goals to be solved" at lines 1572-1573. In the if_neg hd branch:
#        constructor
#        · exact one_div_ne_zero hd
#        · constructor
#          · field_simp; ring
#          · field_simp; ring
# Let's replace the inner constructor with a <;> to handle however many goals there are.
content = content.replace("""        · exact one_div_ne_zero hd
        · constructor
          · field_simp; ring
          · field_simp; ring""", """        · exact one_div_ne_zero hd
        · constructor <;> { field_simp; ring }""")

with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "w") as f:
    f.write(content)
