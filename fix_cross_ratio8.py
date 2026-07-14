with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "r") as f:
    content = f.read()

import re

# We want to replace the `hd` pos branch
replacement1 = """        constructor
        · exact one_div_ne_zero ha
        · have h1 : (match none with | none => (1, 0) | some z' => (z', 1)).1 = 1 / (M.a * z' + M.b) * (M.a * z' + M.b * 1) := by field_simp; ring
          have h2 : (match none with | none => (1, 0) | some z' => (z', 1)).2 = 1 / (M.a * z' + M.b) * (M.c * z' + M.d * 1) := by
            change (0 : ℂ) = 1 / (M.a * z' + M.b) * (M.c * z' + M.d * 1)
            have h_zero : M.c * z' + M.d * 1 = 0 := by
              calc M.c * z' + M.d * 1 = M.c * z' + M.d := by ring
                                      _ = 0 := hd
            rw [h_zero, mul_zero]
          exact ⟨h1, h2⟩"""

# Find the exact block we modified last time
match1 = re.search(r"        constructor\n        · exact one_div_ne_zero ha\n        · constructor\n          · field_simp; ring\n          · have h_zero : M.c \* z' \+ M.d \* 1 = 0 := by\n.*?            rfl", content, re.DOTALL)
if match1:
    content = content[:match1.start()] + replacement1 + content[match1.end():]

# We want to replace the `hd` neg branch
replacement2 = """        constructor
        · exact one_div_ne_zero hd
        · have h1 : (match none with | none => (1, 0) | some z' => (z', 1)).1 = 1 / (M.c * z' + M.d) * (M.a * z' + M.b * 1) := by field_simp; ring
          have h2 : (match none with | none => (1, 0) | some z' => (z', 1)).2 = 1 / (M.c * z' + M.d) * (M.c * z' + M.d * 1) := by field_simp; ring
          exact ⟨h1, h2⟩"""

match2 = re.search(r"        constructor\n        · exact one_div_ne_zero hd\n        · constructor <;> { field_simp; ring }", content, re.DOTALL)
if match2:
    content = content[:match2.start()] + replacement2 + content[match2.end():]

with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "w") as f:
    f.write(content)
